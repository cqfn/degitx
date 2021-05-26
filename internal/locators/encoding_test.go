// MIT License. Copyright (c) 2020 CQFN
// https://github.com/cqfn/degitx/blob/master/LICENSE
package locators

import (
	"testing"

	m "github.com/g4s8/go-matchers"
	ma "github.com/multiformats/go-multiaddr"
	mh "github.com/multiformats/go-multihash"
)

func panicerr(err error) {
	if err != nil {
		panic(err)
	}
}

func Test_Encode(t *testing.T) {
	assert := m.Assert(t)
	addr, err := ma.NewMultiaddr("/ip4/1.1.1.1")
	panicerr(err)
	loc, err := mh.Encode([]byte{0x01}, mh.IDENTITY)
	panicerr(err)
	kpub, kpriv := []byte{0xa0}, []byte{0xb0}
	node := &Node{
		ID:      loc,
		PubKey:  kpub,
		PrivKey: kpriv,
		Addr:    addr,
	}
	enc, err := node.MarshalBinary()
	assert.That("Node encoded without error", err, m.Nil())
	dec := new(Node)
	assert.That("Node decoded without error",
		dec.UnmarshalBinary(enc), m.Nil())
	assert.That("Decoded locator",
		[]byte(dec.ID), m.EqBytes([]byte{0x00, 0x01, 0x01}))
	assert.That("Decoded public-key",
		dec.PubKey, m.EqBytes([]byte{0xa0}))
	assert.That("Ignores private-key",
		dec.PrivKey, m.Nil())
	assert.That("Decodes address correctly",
		dec.Addr.Bytes(), m.EqBytes(addr.Bytes()))
}
