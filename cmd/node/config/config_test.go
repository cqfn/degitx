// MIT License. Copyright (c) 2020 CQFN
// https://github.com/cqfn/degitx/blob/master/LICENSE

package config

import (
	"testing"

	assert "github.com/allisson/go-assert"
)

func Test_FromYaml(tst *testing.T) {
	config := new(NodeConfig)
	err := config.FromFile("testdata/test_pos.yaml")
	assert.Nil(tst, err)
	assert.Equal(tst, "42", config.Version)
	assert.Equal(tst, "expected_alg_name", config.Keys.Alg)
	assert.Equal(tst, "expected_pk_location", config.Keys.Public)
	assert.Equal(tst, "expected_sk_location", config.Keys.Private)
}
