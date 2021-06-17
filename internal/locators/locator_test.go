// MIT License. Copyright (c) 2020 CQFN
// https://github.com/cqfn/degitx/blob/master/LICENSE

package locators

import (
	"testing"

	m "github.com/g4s8/go-matchers"
	mh "github.com/multiformats/go-multihash"
)

func Test_HashLocator(t *testing.T) {
	assert := m.Assert(t)
	node, err := FromKeys([]byte{0x00, 0x01, 0x02, 0x03}, []byte{})
	assert.That("creates Node without error", err, m.Nil())
	t.Logf("Multihash=%s\n", node.ID.HexString())
	info, err := mh.Decode(node.ID)
	assert.That("decoded multihash without error", err, m.Nil())
	assert.That("multihash code is SHA1", info.Code, m.Is(uint64(mh.SHA1)))
	assert.That("mutihahs digest is correct", info.Digest,
		m.Eq([]byte{
			0xa0, 0x2a, 0x05, 0xb0,
			0x25, 0xb9, 0x28, 0xc0,
			0x39, 0xcf, 0x1a, 0xe7,
			0xe8, 0xee, 0x04, 0xe7,
			0xc1, 0x90, 0xc0, 0xdb,
		}))
}
