// MIT License. Copyright (c) 2020 CQFN
// https://github.com/cqfn/degitx/blob/master/LICENSE

// Package discovery provides discovery protocol interfaces and its implementations.
package discovery

import (
	"context"
	"log"

	ma "github.com/multiformats/go-multiaddr"
	mh "github.com/multiformats/go-multihash"
)

// Discovery interface
type Discovery interface {
	Lookup(mh.Multihash, context.Context) (ma.Multiaddr, error)
}

// Service is a discovery client or server daemon to synchornize
// or provide peers information
type Service interface {
	Start(context.Context) error
}

// StubService of discovery. Does nothing.
type StubService struct{}

func (s *StubService) Start(_ context.Context) error {
	log.Print("No discovery server/client started: running stub")
	return nil
}
