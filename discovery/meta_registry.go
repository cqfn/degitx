// MIT License. Copyright (c) 2020 CQFN
// https://github.com/cqfn/degitx/blob/master/LICENSE

package discovery

import (
	"bytes"
	"context"
	"fmt"

	"cqfn.org/degitx/meta"
)

type metaRegistry struct {
	meta meta.Storage
}

// Update metadata storage with new peer
func (r *metaRegistry) Update(ctx context.Context, p *Peer) error {
	cto, cancel := context.WithTimeout(ctx, resolveTimeout)
	defer cancel()
	bin, err := p.Locator.MarshalBinary()
	if err != nil {
		return err
	}
	buf := bytes.NewBuffer([]byte(keyPrefix))
	if _, err := buf.Write([]byte(p.Locator.ID.HexString())); err != nil {
		// byte.Buffer doesn't return errors on write
		panic(err)
	}
	rsp := <-r.meta.Set(cto, buf.String(), meta.Data(bin))
	return rsp.Error
}

func (r *metaRegistry) String() string {
	return fmt.Sprintf("MetaData discovery registry: %s", r.meta)
}

// NewMetaRegistry creates new discovery registry over metadata storage
func NewMetaRegistry(meta meta.Storage) Registry {
	return &metaRegistry{meta}
}
