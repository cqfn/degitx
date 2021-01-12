// MIT License. Copyright (c) 2020 CQFN
// https://github.com/cqfn/degitx/blob/master/LICENSE

package discovery

import (
	"context"
	"testing"

	"cqfn.org/degitx/locators"
	"cqfn.org/degitx/meta"
	m "github.com/g4s8/go-matchers"
)

func Test_Update(t *testing.T) {
	assert := m.Assert(t)
	st := meta.NewInMemStorage()
	peer := testPeer(1, "1.1.1.1")
	reg := NewMetaRegistry(st)
	err := reg.Update(context.Background(), peer)
	assert.That("Updated successfully", err, m.Nil())
	data, err := meta.GetSync(st,
		"cqfn.org/degitx/discovery/node/"+peer.Locator.ID.HexString())
	assert.That("Get peer data successfully", err, m.Nil())
	updated := peer.Copy()
	updated.Locator = new(locators.Node)
	if err := updated.Locator.UnmarshalBinary(data.Slice()); err != nil {
		panic(err)
	}
	assert.That("Peer's data is OK", updated, peerMatcher(peer))
}
