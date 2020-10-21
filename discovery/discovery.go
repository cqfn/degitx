// MIT License. Copyright (c) 2020 CQFN
// https://github.com/cqfn/degitx/blob/master/LICENSE

// Package discovery provides discovery protocol interfaces and its implementations.
package discovery

import (
	"bytes"
	"context"
	"errors"
	"fmt"
	"time"

	"cqfn.org/degitx/locators"
	"cqfn.org/degitx/misc"
	pb "cqfn.org/degitx/proto/go/degitxpb"
	ma "github.com/multiformats/go-multiaddr"
	"google.golang.org/grpc"
)

// Discovery interface
type Discovery interface {
	Ping(ma.Multiaddr) error
}

// Peer node
type Peer struct {
	Locator locators.Locator
	Addr    ma.Multiaddr
}

func (p *Peer) fromGRPCCoord(c *pb.NodeCoord) error {
	addr, err := ma.NewMultiaddr(c.Address)
	if err != nil {
		return err
	}
	loc, err := locators.FromBytes(c.Locator)
	if err != nil {
		return err
	}
	p.Addr = addr
	p.Locator = loc
	return nil
}

// Peers local storage
type Peers struct {
	peers []*Peer
}

func (prs *Peers) merge(upd []*Peer) error {
	// @todo #44:90min Improve merge implementation.
	//  Make it faster - don't use double for loop,
	//  and rollback to initial state in case of error.
	for _, p := range upd {
		var found bool
		for _, local := range prs.peers {
			hash, err := local.Locator.Multihash()
			if err != nil {
				return err
			}
			loc, err := p.Locator.Multihash()
			if err != nil {
				return err
			}
			if bytes.Equal(loc, hash) {
				local.Addr = p.Addr
				found = true
				break
			}
		}
		if !found {
			prs.peers = append(prs.peers, p)
		}
	}
	return nil
}

type pbDiscovery struct {
	ctx   context.Context
	peers *Peers
	self  locators.Locator
}

func coordFromLocator(l locators.Locator) (*pb.NodeCoord, error) {
	c := new(pb.NodeCoord)
	hash, err := l.Multihash()
	if err != nil {
		return nil, err
	}
	c.Locator = hash
	return c, nil
}

func (d *pbDiscovery) Ping(addr ma.Multiaddr) error {
	con, err := grpcConnection(d.ctx, addr)
	if err != nil {
		return err
	}

	defer misc.CloseWithLog(con)
	coord, err := coordFromLocator(d.self)
	if err != nil {
		return err
	}

	svc := pb.NewDiscoveryServiceClient(con)
	ctx, cancel := context.WithTimeout(d.ctx, reqTimeout)
	defer cancel()

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
		upd[i] = p
	}
	return d.peers.merge(upd)
}

var errInvalidSeedAddr = errors.New("invalid seed address, should contain IP and TCP components")

const reqTimeout = time.Second * 5

const conTimeout = time.Second * 5

func grpcConnection(ctx context.Context, addr ma.Multiaddr) (*grpc.ClientConn, error) {
	prts := addr.Protocols()
	if len(prts) < 2 { //nolint:gomnd // 2 parts is verbose enough here
		return nil, errInvalidSeedAddr
	}
	pip := prts[0]
	var prefix string
	switch pip.Code {
	case ma.P_IP4:
		prefix = "ipv4"
	case ma.P_IP6:
		prefix = "ipv6"
	default:
		return nil, errInvalidSeedAddr
	}
	ptcp := prts[1]
	if ptcp.Code != ma.P_TCP {
		return nil, errInvalidSeedAddr
	}
	ip, err := addr.ValueForProtocol(pip.Code)
	if err != nil {
		return nil, fmt.Errorf("failed to find IP component: %w", err)
	}
	tcp, err := addr.ValueForProtocol(ptcp.Code)
	if err != nil {
		return nil, fmt.Errorf("failed to find TCP component: %w", err)
	}
	ctx, cancel := context.WithTimeout(ctx, conTimeout)
	defer cancel()
	return grpc.DialContext(ctx, fmt.Sprintf("%s:%s:%s", prefix, ip, tcp))
}

// NewGrpc creates new gRPC discovery implementation
func NewGrpc(ctx context.Context, self locators.Locator, peers *Peers) Discovery {
	return &pbDiscovery{ctx, peers, self}
}
