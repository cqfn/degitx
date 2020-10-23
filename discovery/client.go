// MIT License. Copyright (c) 2020 CQFN
// https://github.com/cqfn/degitx/blob/master/LICENSE

package discovery

import (
	"context"
	"errors"
	"log"
	"time"

	"cqfn.org/degitx/locators"
	"cqfn.org/degitx/misc"
	pb "cqfn.org/degitx/proto/go/degitxpb"
	ma "github.com/multiformats/go-multiaddr"
	"google.golang.org/grpc"
)

type grpcClient struct {
	peers *Peers
	seed  ma.Multiaddr
	node  *locators.Node
}

// NewGrpcClient creates new gRPC client for seed host
func NewGrpcClient(seed ma.Multiaddr, node *locators.Node, peers *Peers) Service {
	return &grpcClient{peers, seed, node}
}

const ping = time.Second * 5

func (c *grpcClient) Start(ctx context.Context) error {
	ticker := time.NewTicker(ping)
	go func() {
		for {
			select {
			case <-ticker.C:
				if err := c.ping(ctx); err != nil {
					log.Printf("Ping failed to %s: %s", c.seed, err)
					return
				}
			case <-ctx.Done():
				log.Printf("Client service cancelled: %s", ctx.Err())
				return
			}
		}
	}()
	log.Printf("Discovery client started with seed %s", c.seed)
	return nil
}

var errInvalidSeedAddr = errors.New("invalid seed address, should contain IP and TCP components")

const reqTimeout = time.Second * 5

const conTimeout = time.Second * 5

func grpcClientCon(ctx context.Context, maddr ma.Multiaddr) (*grpc.ClientConn, error) {
	ctx, cancel := context.WithTimeout(ctx, conTimeout)
	defer cancel()
	addr := new(MaNetworkAddr)
	if err := addr.Parse(maddr); err != nil { //nolint:dupl // just parsing an address
		return nil, err
	}
	return grpc.DialContext(ctx, addr.String(), grpc.WithInsecure())
}

func (c *grpcClient) ping(ctx context.Context) error {
	con, err := grpcClientCon(ctx, c.seed)
	if err != nil {
		return err
	}

	defer misc.CloseWithLog(con)

	svc := pb.NewDiscoveryServiceClient(con)
	ctx, cancel := context.WithTimeout(ctx, reqTimeout)
	defer cancel()

	coord := coordFromLocator(c.node)
	rsp, err := svc.Ping(ctx, coord)
	if err != nil {
		return err
	}
	coords := rsp.GetPeers()
	upd := make([]*Peer, len(coords))
	for i, crd := range rsp.GetPeers() {
		p := new(Peer)
		if err := p.fromGRPCCoord(crd); err != nil {
			return err
		}
		if err := c.peers.Update(p, nil); err != nil {
			return err
		}
		upd[i] = p
	}
	return nil
}

func coordFromLocator(n *locators.Node) *pb.NodeCoord {
	c := new(pb.NodeCoord)
	c.Locator = n.ID
	c.Address = n.Addr.String()
	return c
}
