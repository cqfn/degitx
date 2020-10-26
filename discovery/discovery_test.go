// MIT License. Copyright (c) 2020 CQFN
// https://github.com/cqfn/degitx/blob/master/LICENSE

package discovery

import (
	"cqfn.org/degitx/locators"
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
	return &Peer{
		Locator: &locators.Node{ID: hash},
		Addr:    testAddr(addr),
	}
}
