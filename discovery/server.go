// MIT License. Copyright (c) 2020 CQFN
// https://github.com/cqfn/degitx/blob/master/LICENSE

package discovery

import (
	"context"
	"net"

	"cqfn.org/degitx/locators"
	pb "cqfn.org/degitx/proto/go/degitxpb"
	ma "github.com/multiformats/go-multiaddr"
	"google.golang.org/grpc"
)

type grpcServer struct {
	addr  net.Addr
	peers *Peers
}

// NewServer for gRPC discovery protocol
func NewServer(maddr ma.Multiaddr, loc locators.Locator) (Service, error) {
	addr := new(maNetworkAddr)
	if err := addr.parse(maddr); err != nil { //nolint:dupl // just parsing an address
		return nil, err
	}
	srv := new(grpcServer)
	srv.addr = addr
	return srv, nil
}

type hostService struct {
	ctx   context.Context
	peers *Peers
}

func (s *hostService) Ping(req context.Context, coord *pb.NodeCoord) (*pb.PingResponse, error) {
	result := make(chan *pb.PingResponse)
	failure := make(chan error)
	go func() {
		upd := new(Peer)
		if err := upd.fromGRPCCoord(coord); err != nil {
			failure <- err
			return
		}
		updated := make(chan struct{})
		if err := s.peers.Update(upd, updated); err != nil {
			failure <- err
			return
		}
		<-updated
		rsp := new(pb.PingResponse)
		rsp.Peers = make([]*pb.NodeCoord, len(s.peers.peers))
		for i, peer := range s.peers.Peers() {
			coord := new(pb.NodeCoord)
			addr, err := peer.Addr.MarshalText()
			if err != nil {
				failure <- err
				return
			}
			coord.Address = string(addr)
			hash, err := peer.Locator.Multihash()
			if err != nil {
				failure <- err
				return
			}
			coord.Locator = hash
			rsp.Peers[i] = coord
		}
		result <- rsp
	}()
	select {
	case <-s.ctx.Done():
		return nil, s.ctx.Err()
	case <-req.Done():
		return nil, req.Err()
	case rsp := <-result:
		return rsp, nil
	case err := <-failure:
		return nil, err
	}
}

func (s *grpcServer) Start(ctx context.Context) error {
	srv := grpc.NewServer()
	svc := &hostService{ctx, s.peers}
	pb.RegisterDiscoveryServiceServer(srv, svc)

	l, err := net.Listen(s.addr.Network(), s.addr.String())
	if err != nil {
		return err
	}

	if err := srv.Serve(l); err != nil {
		return err
	}

	go func() {
		<-ctx.Done()
		srv.GracefulStop()
	}()
	return nil
}
