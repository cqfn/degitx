// MIT License. Copyright (c) 2020 CQFN
// https://github.com/cqfn/degitx/blob/master/LICENSE

package main

import (
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
		"AAAAB3NzaC1yc2EAAAADAQABAAAAgQCnM9WswOrpJBjlXLVYaZlSNWpIfFwR5Kv4Q"+
			"LcL+1RqAEuHCVl9h0KUc6vlfnf6j6DL7YtdkOtIDNf8DA8OTG0t0ceCpobvmGxFRs"+
			"Eb1/hoG2M6AMPN+OszjOA6/TarMPI2daH1BSlSCkb0HlSc+jGLsx04qwaf5dAexR5"+
			"SwNGnnw==",
		config.Keys.Public)
	assert.Equal(tst,
		"MIICXAIBAAKBgQCnM9WswOrpJBjlXLVYaZlSNWpIfFwR5Kv4QLcL+1RqAEuHCVl9"+
			"h0KUc6vlfnf6j6DL7YtdkOtIDNf8DA8OTG0t0ceCpobvmGxFRsEb1/hoG2M6AMPN"+
			"+OszjOA6/TarMPI2daH1BSlSCkb0HlSc+jGLsx04qwaf5dAexR5SwNGnnwIDAQAB"+
			"AoGALSO8Uwg+IzUAl6Ngvf68Sspq6CjSvm3q03m9MTnn/zoXKdynUVFb8zILPUjY"+
			"YUe3VHbMAjWmn2wAP2aOBgEyFBXoa2PdiYp0sq53z31NEJ+lHUkuHp7BIxF/E67D"+
			"PzzoYvP0VD8wtJBKxzGGp2X4CpGtIRp78pbF5rJCqAH4C0ECQQDUNhAgFLWo6SUy"+
			"oMjjgn3rz9voNI9GlsptCiuCNCON+WRMyrwlGOaTMQPrDuPSoT+qNwoZ8hwZs4g6"+
			"XRpNIrV/AkEAybQ2SV+kab4r2p6NXVpS0LwzOFPd9W0NzSTMVQtTtIOJiOHAsC/Z"+
			"mm2zQKEjta+v3Ef3cgdnpQnM7btqIR9d4QJAUWQq6yMGSbKiQbjJU/lIspkWjwkZ"+
			"qslK+mdcKKQ2vs1YWtunLdNPHEVAa3daif6unGpfxXPGs1TYewoafFtDoQJAZiyB"+
			"q11lfaM1t8LFPVq5xL7w+0GQl/gsG5TeZN4eArz2+H3TC+zRP+b9/GkkG67pWJ6j"+
			"/AFAQVvbkTl0o16uQQJBAJ1l8+kCCHPdbnbHEkZge8HNlFZM2bw3dyyph7KCjo2L"+
			"7uTs05kBqarL2JldFsi0xxourTISuMJep1t+cDkJjWU=",
		config.Keys.Private)
}

func Test_generateNodeID(tst *testing.T) {
	config := NodeConfig{
		"",
		&Keys{
			"",
			"",
			"Merkle–Damgård",
		},
	}
	nodeID, err := config.generateNodeID()
	assert.Nil(tst, err)
	assert.Equal(tst, "11148a173fd3e32c0fa78b90fe42d305f202244e2739", nodeID)
}
