// MIT License. Copyright (c) 2020 CQFN
// https://github.com/cqfn/degitx/blob/master/LICENSE

package discovery

import (
	"bytes"
	"context"
	"errors"
	"fmt"
	"log"
	"time"

	"cqfn.org/degitx/internal/locators"
	"cqfn.org/degitx/internal/misc"
	pb "cqfn.org/degitx/proto/go/degitxpb"
	ma "github.com/multiformats/go-multiaddr"
	mh "github.com/multiformats/go-multihash"
	"google.golang.org/grpc"
)

type grpcSeedProvider struct {
	peers *Peers
	seed  ma.Multiaddr
	node  *locators.Node
}

// NewGrpcSeedProvider creates new doscovery provider for gRPC seed host
func NewGrpcSeedProvider(ctx context.Context, seed ma.Multiaddr,
	node *locators.Node, peers *Peers) Provider {
	res := &grpcSeedProvider{peers, seed, node}
	res.sync(ctx)
	return res
}

const ping = time.Second * 5

func (c *grpcSeedProvider) Resolve(ctx context.Context,
	loc mh.Multihash) (*Peer, error) {
	done := make(chan struct{})
	if err := c.ping(ctx, done); err != nil {
		return nil, &ErrFailedToResolve{err, c, loc}
	}
	select {
	case <-ctx.Done():
		return nil, &ErrFailedToResolve{ctx.Err(), c, loc}
	case <-done:
		for _, p := range c.peers.Peers() {
			if bytes.Equal(p.Locator.ID, loc) {
				return p, nil
			}
		}
		return nil, &ErrPeerNotFound{c, loc}
	}
}

func (c *grpcSeedProvider) String() string {
	return fmt.Sprintf("gRPC seed provider: host=`%s`", c.seed)
}

func (c *grpcSeedProvider) sync(ctx context.Context) {
	ticker := time.NewTicker(ping)
	go func() {
		for {
			select {
			case <-ticker.C:
				if err := c.ping(ctx, nil); err != nil {
					log.Printf("Ping failed to %s: %s", c.seed, err)
					return
				}
			case <-ctx.Done():
				log.Printf("Client service cancelled: %s", ctx.Err())
				return
			}
		}
	}()
	log.Printf("Discovery seed provider sync started with host=`%s`", c.seed)
}

var errInvalidSeedAddr = errors.New("invalid seed address, should contain IP and TCP components")

const reqTimeout = time.Second * 5

const conTimeout = time.Second * 5

func grpcClientCon(ctx context.Context, maddr ma.Multiaddr) (*grpc.ClientConn, error) {
	ctx, cancel := context.WithTimeout(ctx, conTimeout)
	defer cancel()
	addr := new(MaNetworkAddr)
	if err := addr.Parse(maddr); err != nil {
		return nil, err
	}
	return grpc.DialContext(ctx, addr.String(), grpc.WithInsecure())
}

func (c *grpcSeedProvider) ping(ctx context.Context, done chan struct{}) error {
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
		c.peers.update(p, done)
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
