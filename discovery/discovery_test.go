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

func Test_peersMerge(t *testing.T) {
	var prs Peers
	prs.peers = []*Peer{
		testPeer(1, "1.1.1.1"),
		testPeer(2, "1.1.1.2"),
	}
	update := []*Peer{
		testPeer(2, "2.2.2.2"),
		testPeer(3, "3.3.3.3"),
	}
	t.Run("Merge completed without error", func(t *testing.T) { assert.Nil(t, prs.merge(update)) })
	t.Run("There are 3 peers after merge", func(t *testing.T) { assert.Equal(t, len(prs.peers), 3) })
	var first, second, third *Peer
	for _, p := range prs.peers {
		if testLocatorEqual(1, p.Locator) { //nolint:gocritic
			first = p
		} else if testLocatorEqual(2, p.Locator) { //nolint:gocritic
			second = p
		} else if testLocatorEqual(3, p.Locator) { //nolint:gocritic
			third = p
		}
	}
	t.Run("First peer has `1.1.1.1` address", assertAddr(first.Addr, "1.1.1.1"))
	t.Run("Second peer has `2.2.2.2` address", assertAddr(second.Addr, "2.2.2.2"))
	t.Run("Third peer has `3.3.3.3` address", assertAddr(third.Addr, "3.3.3.3"))
}
