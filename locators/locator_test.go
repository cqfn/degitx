// MIT License. Copyright (c) 2020 CQFN
// https://github.com/cqfn/degitx/blob/master/LICENSE

package locators

import (
	"testing"

	assert "github.com/allisson/go-assert"
	mh "github.com/multiformats/go-multihash"
)

func assertNil(val interface{}) func(*testing.T) {
	return func(t *testing.T) { assert.Nil(t, val) }
}

func Test_HashLocator(t *testing.T) {
	loc, err := NewHash([]byte{0x00, 0x01, 0x02, 0x03}, "sha1")
	t.Run("Creating locator", assertNil(err))
	target, err := loc.Multihash()
	t.Run("Generating multihash", assertNil(err))
	info, err := mh.Decode(target)
	t.Run("Decoding multihash", assertNil(err))
	t.Run("Testing MH code", func(t *testing.T) { assert.Equal(t, info.Code, uint64(mh.SHA1)) })
	t.Run("Testing MH digest", func(t *testing.T) {
		assert.Equal(t, info.Digest,
			[]byte{
				0xa0, 0x2a, 0x05, 0xb0,
				0x25, 0xb9, 0x28, 0xc0,
				0x39, 0xcf, 0x1a, 0xe7,
				0xe8, 0xee, 0x04, 0xe7,
				0xc1, 0x90, 0xc0, 0xdb,
			})
	})
}
