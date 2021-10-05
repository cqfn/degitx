// MIT License. Copyright (c) 2020 CQFN
// https://github.com/cqfn/degitx/blob/master/LICENSE

package discovery

import (
	"bytes"
	"fmt"

	"cqfn.org/degitx/pkg/locators"

	m "github.com/g4s8/go-matchers"
	ma "github.com/multiformats/go-multiaddr"
	mh "github.com/multiformats/go-multihash"
)

func testAddr(name string) ma.Multiaddr {
	a, err := ma.NewMultiaddr("/ip4/" + name)
	if err != nil {
		panic(err)
	}
	return a
}

func testPeer(loc byte, addr string) *Peer {
	hash, err := mh.Encode([]byte{loc}, mh.IDENTITY)
	if err != nil {
		panic(err)
	}
	a := testAddr(addr)
	return &Peer{
		Locator: &locators.Node{
			ID:     hash,
			Addr:   a,
			PubKey: []byte{loc},
		},
		Addr: a,
	}
}

type mPeerEq struct {
	expect *Peer
}

func peerMatcher(expect *Peer) m.Matcher {
	return &mPeerEq{expect}
}

func (m *mPeerEq) Check(actual interface{}) bool {
	other, ok := actual.(*Peer)
	if !ok {
		return false
	}
	matches := other.Addr.Equal(m.expect.Addr) && bytes.Equal(other.Locator.ID, m.expect.Locator.ID)
	return matches
}

func (m *mPeerEq) String() string {
	return fmt.Sprintf("peer equal to `%s`", m.expect)
}
