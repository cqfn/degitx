// MIT License. Copyright (c) 2020 CQFN
// https://github.com/cqfn/degitx/blob/master/LICENSE

package discovery

import (
	"bytes"
	"testing"

	"cqfn.org/degitx/locators"
	"github.com/allisson/go-assert"
	ma "github.com/multiformats/go-multiaddr"
	mh "github.com/multiformats/go-multihash"
)

type testLocator struct {
	src []byte
}

func (l *testLocator) Multihash() (mh.Multihash, error) {
	h, err := mh.Encode(l.src, mh.IDENTITY)
	if err != nil {
		return nil, err
	}
	return mh.Multihash(h), nil
}

func (l *testLocator) Equal(h mh.Multihash) bool {
	res, err := l.Multihash()
	if err != nil {
		panic(err)
	}
	return bytes.Equal(res, h)
}

func testAddr(name string) ma.Multiaddr {
	a, err := ma.NewMultiaddr("/ip4/" + name)
	if err != nil {
		panic(err)
	}
	return a
}

func testPeer(loc byte, addr string) *Peer {
	return &Peer{
		Locator: &testLocator{[]byte{loc}},
		Addr:    testAddr(addr),
	}
}

func assertAddr(target ma.Multiaddr, expect string) func(*testing.T) {
	return func(t *testing.T) {
		assert.Equal(t, target.Equal(testAddr(expect)), true)
	}
}

func testLocatorEqual(expected byte, loc locators.Locator) bool {
	hash, err := loc.Multihash()
	if err != nil {
		panic(err)
	}
	return (&testLocator{[]byte{expected}}).Equal(hash)
}
