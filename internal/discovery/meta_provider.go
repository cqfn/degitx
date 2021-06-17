// MIT License. Copyright (c) 2020 CQFN
// https://github.com/cqfn/degitx/blob/master/LICENSE

package discovery

import (
	"bytes"
	"context"
	"fmt"
	"time"

	"cqfn.org/degitx/internal/locators"
	"cqfn.org/degitx/internal/meta"

	mh "github.com/multiformats/go-multihash"
)

type metaProvider struct {
	meta meta.Storage
}

const keyPrefix = "cqfn.org/degitx/internal/discovery/node/"

const resolveTimeout = 30 * time.Second

// Resolve peer from metadata storage
func (p *metaProvider) Resolve(ctx context.Context,
	loc mh.Multihash) (*Peer, error) {
	buf := bytes.NewBuffer([]byte(keyPrefix))
	if _, err := buf.WriteString(loc.HexString()); err != nil {
		// byte.Buffer doesn't return errors on write
		panic(err)
	}
	ctx, cancel := context.WithTimeout(ctx, resolveTimeout)
	defer cancel()
	rsp := <-p.meta.Get(ctx, buf.String())
	if rsp.Error != nil {
		return nil, rsp.Error
	}
	node := new(locators.Node)
	if err := node.UnmarshalBinary(rsp.Value.Slice()); err != nil {
		return nil, err
	}
	peer := &Peer{node, node.Addr}
	return peer, nil
}

func (p *metaProvider) String() string {
	return fmt.Sprintf("MetaData discovery provider: %s", p.meta)
}

// NewMetaProvider creates new discovery provider over metadata storage
func NewMetaProvider(meta meta.Storage) Provider {
	return &metaProvider{meta}
}
