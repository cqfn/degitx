// MIT License. Copyright (c) 2020 CQFN
// https://github.com/cqfn/degitx/blob/master/LICENSE

package discovery

import (
	"context"
	"testing"

	pb "cqfn.org/degitx/proto/go/degitxpb"
	mh "github.com/multiformats/go-multihash"
	"github.com/stretchr/testify/assert"
)

func testLocString(d byte) []byte {
	h, err := mh.Encode([]byte{d}, mh.IDENTITY)
	if err != nil {
		panic(err)
	}
	return h
}

func Test_ReceivePing(t *testing.T) {
	svc := new(hostService)
	ctx, cancel := context.WithCancel(context.Background())
	defer cancel()
	svc.ctx = ctx
	svc.peers = NewPeers(ctx)
	coord := &pb.NodeCoord{
		Address: "/ip4/127.0.0.1",
		Locator: testLocString(1),
	}
	rsp, err := svc.Ping(context.Background(), coord)
	assert.Nil(t, err, "ping respond without any error")
	assert.Len(t, rsp.GetPeers(), 1, "response has the only coord")
	assert.Equal(t, rsp.GetPeers()[0], coord, "response has self coord")
}
