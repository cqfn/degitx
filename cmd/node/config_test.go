// MIT License. Copyright (c) 2020 CQFN
// https://github.com/cqfn/degitx/blob/master/LICENSE

package main

import (
	"testing"

	"cqfn.org/degitx/logging"

	m "github.com/g4s8/go-matchers"
)

func Test_fromYaml(t *testing.T) {
	assert := m.Assert(t)
	config := new(NodeConfig)
	err := config.fromFile("testdata/test_pos.yaml")
	assert.That("config parsed without error", err, m.Nil())
	assert.That("config version parsed", config.Version, m.Eq("42"))
	assert.That("config alg parsed", config.Keys.Alg, m.Eq("rsa-1024"))
	assert.That("public key path parsed", config.Keys.PathToPublic, m.Eq("./cmd/node/testdata/public"))
	assert.That("private key path parsed", config.Keys.PathToPrivate, m.Eq("./cmd/node/testdata/private"))
	assert.That("logger outputs parsed", config.LogConfig.Outputs, m.LenIs(1))
	assert.That("logger output paths parsed", config.LogConfig.Outputs[0].Path, m.LenIs(1))
	assert.That("logger output paths parsed", config.LogConfig.Outputs[0].Path[0], m.Eq("stdout"))
	assert.That("logger log level parsed", config.LogConfig.Outputs[0].Level, m.Eq("DEBUG"))
	assert.That("logger output paths parsed", config.LogConfig.Outputs[0].Format, m.Eq("plain"))
	assert.That("zap logger errors output parsed", config.LogConfig.ErrorsOut, m.LenIs(1))
	assert.That("zap logger errors output parsed", config.LogConfig.ErrorsOut[0], m.Eq("stderr"))
}

func Test_generateNodeID(t *testing.T) {
	assert := m.Assert(t)
	config := NodeConfig{
		"",
		&Keys{
			Alg:           "",
			PathToPrivate: "testdata/stub",
			PathToPublic:  "testdata/stub",
		},
		new(logging.LogConfig),
	}
	loc, err := config.Node()
	assert.That("node parsed without err", err, m.Nil())
	assert.That("node id parsed", loc.ID.String(), m.Eq("11148a173fd3e32c0fa78b90fe42d305f202244e2739"))
}
