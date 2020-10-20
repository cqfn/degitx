// MIT License. Copyright (c) 2020 CQFN
// https://github.com/cqfn/degitx/blob/master/LICENSE

package main

import (
	"encoding/hex"
	"testing"

	assert "github.com/allisson/go-assert"
)

func Test_fromYaml(tst *testing.T) {
	config := new(NodeConfig)
	err := config.fromFile("testdata/test_pos.yaml")
	assert.Nil(tst, err)
	assert.Equal(tst, "42", config.Version)
	assert.Equal(tst, "rsa-1024", config.Keys.Alg)
	assert.Equal(tst,
		"./cmd/node/testdata/public",
		config.Keys.PathToPublic)
	assert.Equal(tst,
		"./cmd/node/testdata/private",
		config.Keys.PathToPrivate)
}

func Test_generateNodeID(tst *testing.T) {
	config := NodeConfig{
		"",
		&Keys{
			"",
			"",
			"testdata/stub",
		},
		&Locator{
			HashFunc: "sha1",
		},
	}
	loc, err := config.Locator()
	assert.Nil(tst, err)
	mh, err := loc.Multihash()
	assert.Nil(tst, err)
	assert.Equal(tst, "11148a173fd3e32c0fa78b90fe42d305f202244e2739", hex.EncodeToString(mh))
}
