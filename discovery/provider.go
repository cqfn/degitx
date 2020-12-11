// MIT License. Copyright (c) 2020 CQFN
// https://github.com/cqfn/degitx/blob/master/LICENSE

package discovery

import (
	"context"
	"errors"
	"fmt"
	"strings"

	mh "github.com/multiformats/go-multihash"
)

// ErrPeerNotFound returned by provider if provider
// successfully tried to resulve the peer location,
// but didn't find it.
type ErrPeerNotFound struct {
	p   Provider
	loc mh.Multihash
}

func (e *ErrPeerNotFound) Error() string {
	return fmt.Sprintf("Peer `%s` was not found with %s",
		e.loc.HexString(), e.p)
}

// ErrFailedToResolve returned by provider if it failed to resolve the peer
// due to some other reason provided with `errors.Unwrap()` method
type ErrFailedToResolve struct {
	origin error
	p      Provider
	loc    mh.Multihash
}

func (e *ErrFailedToResolve) Error() string {
	return fmt.Sprintf("Failed to resolve peer `%s` with %s",
		e.loc.HexString(), e.p)
}

func (e *ErrFailedToResolve) Unwrap() error {
	return e.origin
}

// Provider of peer nodes addresses
type Provider interface {
	// Resolve peer by locator hash
	Resolve(context.Context, mh.Multihash) (*Peer, error)

	// String representation
	String() string
}

type pChain struct {
	providers []Provider
}

// NewProviderChain creates a chained provider by joining multiple providers together
func NewProviderChain(pp ...Provider) Provider {
	return &pChain{pp}
}

func (c *pChain) Resolve(ctx context.Context, loc mh.Multihash) (*Peer, error) {
	var enf *ErrPeerNotFound
	for _, p := range c.providers {
		peer, err := p.Resolve(ctx, loc)
		if err == nil {
			return peer, nil
		}
		if errors.As(err, &enf) {
			continue
		}
		return nil, err
	}
	return nil, &ErrPeerNotFound{c, loc}
}

func (c *pChain) String() string {
	ps := make([]string, len(c.providers))
	for i, p := range c.providers {
		ps[i] = p.String()
	}
	return fmt.Sprintf("ProviderChain: [%s]", strings.Join(ps, ";"))
}
