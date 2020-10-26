// MIT License. Copyright (c) 2020 CQFN
// https://github.com/cqfn/degitx/blob/master/LICENSE

package discovery

import (
	"testing"

	ma "github.com/multiformats/go-multiaddr"
	"github.com/stretchr/testify/assert"
)

func Test_convertAddr(t *testing.T) {
	maddr, err := ma.NewMultiaddr("/ip4/192.168.1.4/tcp/80")
	if err != nil {
		panic(err)
	}
	addr := new(MaNetworkAddr)
	err = addr.Parse(maddr)
	assert.Nil(t, err, "parses valid multiaddr without issues")
	assert.Equal(t, "ipv4", addr.Network())
	assert.Equal(t, "192.168.1.4:80", addr.String())
}
