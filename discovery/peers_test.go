// MIT License. Copyright (c) 2020 CQFN
// https://github.com/cqfn/degitx/blob/master/LICENSE

package discovery

import (
	"context"
	"testing"

	"github.com/stretchr/testify/assert"
)

func blockingUpdate(prs *Peers, upd *Peer) error {
	done := make(chan struct{})
	if err := prs.Update(upd, done); err != nil {
		return err
	}
	<-done
	return nil
}

func Test_peersMerge(t *testing.T) {
	ctx, cancel := context.WithCancel(context.Background())
	defer cancel()
	prs := NewPeers(ctx)
	err := blockingUpdate(prs, testPeer(1, "1.1.1.1"))
	assert.Nil(t, err, "updates 1 without error")
	err = blockingUpdate(prs, testPeer(2, "1.1.1.2"))
	assert.Nil(t, err, "updates 2 without error")
	err = blockingUpdate(prs, testPeer(2, "2.2.2.2"))
	assert.Nil(t, err, "updates 2 (new data) without error")
	err = blockingUpdate(prs, testPeer(3, "3.3.3.3"))
	assert.Nil(t, err, "updates 3 without error")

	assert.Len(t, prs.peers, 3, "there are 3 peers after update")
	var first, second, third *Peer
	for _, p := range prs.Peers() {
		if testLocatorEqual(1, p.Locator) { //nolint:gocritic
			first = p
		} else if testLocatorEqual(2, p.Locator) { //nolint:gocritic
			second = p
		} else if testLocatorEqual(3, p.Locator) { //nolint:gocritic
			third = p
		}
	}
	t.Run("First peer has `1.1.1.1` address", assertAddr(first.Addr, "1.1.1.1"))
	t.Run("Second peer has `2.2.2.2` address", assertAddr(second.Addr, "2.2.2.2"))
	t.Run("Third peer has `3.3.3.3` address", assertAddr(third.Addr, "3.3.3.3"))
}
