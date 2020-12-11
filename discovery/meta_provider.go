// MIT License. Copyright (c) 2020 CQFN
// https://github.com/cqfn/degitx/blob/master/LICENSE

package discovery

import (
	"bytes"
	"context"
	"fmt"
	"time"

	"cqfn.org/degitx/locators"
	"cqfn.org/degitx/meta"

	mh "github.com/multiformats/go-multihash"
)

type metaProvider struct {
	meta meta.Storage
}

const keyPrefix = "cqfn.org/degitx/discovery/node/"

const resolveTimeout = 30 * time.Second

// @todo #105:90min Implement discovery registration mechanism.
//  There should be common interface to introduce a node to the network
//  and register itself in storage. For MVP it should be registration
//  in metadata key-value storage by updating network address of
//  node locator. Keep in mind, that other discovery techicues could
//  be used later.

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
