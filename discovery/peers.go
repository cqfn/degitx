// MIT License. Copyright (c) 2020 CQFN
// https://github.com/cqfn/degitx/blob/master/LICENSE

package discovery

import (
	"context"

	"cqfn.org/degitx/locators"
	ma "github.com/multiformats/go-multiaddr"
	mh "github.com/multiformats/go-multihash"
)

// Peers local storage
type Peers struct {
	peers   map[string]*Peer
	updates chan *updateMsg
}

const chanSize = 16

// NewPeers initialises and start queue for peers processing
func NewPeers(ctx context.Context) *Peers {
	p := new(Peers)
	p.peers = make(map[string]*Peer)
	p.updates = make(chan *updateMsg, chanSize)
	go p.runLoop(ctx)
	return p
}

func (p *Peers) runLoop(ctx context.Context) {
	for {
		select {
		case <-ctx.Done():
			return
		case upd := <-p.updates:
			p.merge(upd)
			if upd.done != nil {
				close(upd.done)
			}
		}
	}
}

// Peers slice
func (p *Peers) Peers() []*Peer {
	res := make([]*Peer, 0, len(p.peers))
	for _, peer := range p.peers {
		res = append(res, peer.Copy())
	}
	return res
}

// Update peers with new peer, notifies optional done channel on complete
func (p *Peers) Update(peer *Peer, done chan struct{}) error {
	hash, err := peer.Locator.Multihash()
	if err != nil {
		return err
	}
	upd := &updateMsg{
		id:   hash.HexString(),
		hash: hash,
		addr: peer.Addr,
		done: done,
	}
	p.updates <- upd
	return nil
}

// Peer node
type Peer struct {
	Locator locators.Locator
	Addr    ma.Multiaddr
}

// Copy peer to new structure
func (p *Peer) Copy() *Peer {
	cpy := new(Peer)
	cpy.Addr = p.Addr
	cpy.Locator = p.Locator
	return cpy
}

type updateMsg struct {
	id   string
	hash mh.Multihash
	addr ma.Multiaddr
	done chan struct{}
}

func (p *Peers) merge(upd *updateMsg) {
	if peer, found := p.peers[upd.id]; found {
		peer.Addr = upd.addr
	} else {
		p.peers[upd.id] = &Peer{
			Locator: locators.FromMultihash(upd.hash),
			Addr:    upd.addr,
		}
	}
}
