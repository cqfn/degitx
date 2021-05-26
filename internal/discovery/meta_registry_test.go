// MIT License. Copyright (c) 2020 CQFN
// https://github.com/cqfn/degitx/blob/master/LICENSE

package discovery

import (
	"context"
	"testing"

	"cqfn.org/degitx/internal/meta"
	matcher "github.com/g4s8/go-matchers"
)

func Test_Resolve(t *testing.T) {
	assert := matcher.Assert(t)
	st := meta.NewInMemStorage()
	peer := testPeer(1, "1.1.1.1")
	bin, err := peer.Locator.MarshalBinary()
	if err != nil {
		panic(err)
	}
	if err := meta.SetSync(st,
		"cqfn.org/degitx/internal/discovery/node/"+peer.Locator.ID.HexString(),
		meta.Data(bin)); err != nil {
		panic(err)
	}
	pr := NewMetaProvider(st)
	resolve, err := pr.Resolve(context.Background(), peer.Locator.ID)
	assert.That("Resolved without errors", err, matcher.Nil())
	assert.That("Resolved correct peer", resolve.Addr.Bytes(),
		matcher.Eq(peer.Addr.Bytes()))
}
