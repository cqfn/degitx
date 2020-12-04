// MIT License. Copyright (c) 2020 CQFN
// https://github.com/cqfn/degitx/blob/master/LICENSE

// Package discovery provides discovery protocol interfaces and its implementations.
package discovery

import (
	"bytes"
	"context"
	mh "github.com/multiformats/go-multihash"
)

// Discovery protocol
type Discovery struct {
	peers *Peers
	prov  Provider
}

// NewDiscovery creates discovery protocol encapsulating
// peers table and discovery providers
func NewDiscovery(peers *Peers, prov Provider) *Discovery {
	return &Discovery{peers, prov}
}

func (d *Discovery) Resolve(ctx context.Context,
	loc mh.Multihash) (*Peer, error) {
	for _, p := range d.peers.Peers() {
		if bytes.Equal(loc, p.Locator.ID) {
			return p, nil
		}
	}
	return d.prov.Resolve(ctx, loc)
}
