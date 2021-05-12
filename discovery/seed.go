// MIT License. Copyright (c) 2020 CQFN
// https://github.com/cqfn/degitx/blob/master/LICENSE

package discovery

import (
	"context"
	"log"
	"net"

	"cqfn.org/degitx/locators"
	pb "cqfn.org/degitx/proto/go/degitxpb"
	ma "github.com/multiformats/go-multiaddr"
	mh "github.com/multiformats/go-multihash"
	"google.golang.org/grpc"
)

// Seed host for discovery peers resolving
type Seed interface {
	Start(context.Context) error
}

type grpcSeed struct {
	addr  net.Addr
	peers *Peers
}

// NewGrpcSeed for gRPC seed host
func NewGrpcSeed(maddr ma.Multiaddr, node *locators.Node,
	peers *Peers) (Seed, error) {
	addr := new(MaNetworkAddr)
	if err := addr.Parse(maddr); err != nil {
		return nil, err
	}
	return &grpcSeed{addr, peers}, nil
}

type hostService struct {
	ctx   context.Context
	peers *Peers
}

func (p *Peer) fromGRPCCoord(c *pb.NodeCoord) error {
	addr, err := ma.NewMultiaddr(c.Address)
	if err != nil {
		return err
	}
	hash, err := mh.Cast(c.Locator)
	if err != nil {
		return err
	}
	p.Addr = addr
	p.Locator = &locators.Node{ID: hash}
	return nil
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
		s.peers.update(upd, updated)
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
			coord.Locator = peer.Locator.ID
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

func (s *grpcSeed) Start(ctx context.Context) error {
	srv := grpc.NewServer()
	svc := &hostService{ctx, s.peers}
	pb.RegisterDiscoveryServiceServer(srv, svc)

	log.Printf("Starting discovery seed host on %s - %s", s.addr.Network(), s.addr)
	l, err := net.Listen("tcp", s.addr.String())
	if err != nil {
		return err
	}

	if err := srv.Serve(l); err != nil {
		log.Printf("Discovery server failed: %s", err)
	}

	log.Printf("Discovery server started at %s", s.addr)
	return nil
}
