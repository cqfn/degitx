// MIT License. Copyright (c) 2020 CQFN
// https://github.com/cqfn/degitx/blob/master/LICENSE

package discovery

import (
	"context"
	"testing"

	m "github.com/g4s8/go-matchers"
)

func blockingUpdate(prs *Peers, upd *Peer) {
	done := make(chan struct{})
	prs.update(upd, done)
	<-done
}

func Test_peersMerge(t *testing.T) {
	assert := m.Assert(t)
	ctx, cancel := context.WithCancel(context.Background())
	defer cancel()
	prs := NewPeers(ctx)
	blockingUpdate(prs, testPeer(1, "1.1.1.1"))
	blockingUpdate(prs, testPeer(2, "1.1.1.2"))
	blockingUpdate(prs, testPeer(2, "2.2.2.2"))
	blockingUpdate(prs, testPeer(3, "3.3.3.3"))
	peers := prs.Peers()
	assert.That("there are 3 peers after update", peers, m.LenIs(3))
	assert.That("has all peers", peers,
		m.AllOf(m.HasItemEq(testPeer(1, "1.1.1.1")),
			m.HasItemEq(testPeer(2, "2.2.2.2")),
			m.HasItemEq(testPeer(3, "3.3.3.3"))))
}
