// MIT License. Copyright (c) 2020 CQFN
// https://github.com/cqfn/degitx/blob/master/LICENSE

// Package discovery provides discovery protocol interfaces
// and its implementations.
// The main API are:
//   - `Discovery` - provides all API for discovery protocol,
//   such as resolving peer addresses by locator IDs.
//   It keeps local peers table in sync, it checks the local table
//   before query remote providers, and update it on success lookup.
//   It can be created using `NewDiscovery` factory function.
//   - `Provider` - remote discovery provider API,
//   It performs query lookup operation in any remote kind of storage,
//   E.g. it may have implementations for database, etcd, DHT, etc.
//   - `ErrNotFound` - error returned when peer was not found. The error
//   can be checked with `errors.As(err, &notFound)`.
//   - `ErrFailedToResolve` - generic error wrapper, encapsulates
//   more concrete errors, to get caused errors use `errors.Unwrap`
//   or `errors.As()`
package discovery

import (
	"bytes"
	"context"
	"fmt"

	mh "github.com/multiformats/go-multihash"
)

// Discovery protocol. It's provider and registry in one struct
type Discovery struct {
	peers *Peers
	prov  Provider
	reg   Registry
}

// NewDiscovery creates discovery protocol encapsulating
// peers table, discovery providers and registries
func NewDiscovery(peers *Peers, prov Provider, reg Registry) *Discovery {
	return &Discovery{peers, prov, reg}
}

// Resolve a peer from local table or discovery provider
func (d *Discovery) Resolve(ctx context.Context,
	loc mh.Multihash) (*Peer, error) {
	for _, p := range d.peers.Peers() {
		if bytes.Equal(loc, p.Locator.ID) {
			return p, nil
		}
	}
	p, err := d.prov.Resolve(ctx, loc)
	if err == nil {
		d.peers.update(p, nil)
	}
	return p, err
}

// Update local peers table and registry with new peer
func (d *Discovery) Update(ctx context.Context, p *Peer) error {
	done := make(chan struct{}); 	err := make(chan error)
	d.peers.update(p, done)
	go func() {
		select {
		case <-done:
			err <- d.reg.Update(ctx, p)
		case <-ctx.Done():
			err <- ctx.Err()
		}
	}()
	return <-err
}

func (d *Discovery) String() string {
	return fmt.Sprintf("Discovery: provider=%s, registry=%s",
		d.prov, d.reg)
}
