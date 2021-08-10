// MIT License. Copyright (c) 2020 CQFN
// https://github.com/cqfn/degitx/blob/master/LICENSE

package discovery

import (
	"context"
	"fmt"
	"log"

	"cqfn.org/degitx/internal/locators"
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
// `ctx' cancellation will stop this queue
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

type errPeerNotFound struct{ peer mh.Multihash }

func (e *errPeerNotFound) Error() string {
	return fmt.Sprintf("Peer `%s` not found locally", e.peer.HexString())
}

// Address of peer node
func (p *Peers) Address(hash mh.Multihash) (ma.Multiaddr, error) {
	if peer, found := p.peers[hash.HexString()]; found {
		return peer.Addr, nil
	}
	return nil, &errPeerNotFound{hash}
}

// update peers with new peer, notifies optional done channel on complete
func (p *Peers) update(peer *Peer, done chan struct{}) {
	hash := peer.Locator.ID
	upd := &updateMsg{
		id:   hash.HexString(),
		hash: hash,
		addr: peer.Addr,
		done: done,
	}
	p.updates <- upd
}

// Peer node
type Peer struct {
	Locator *locators.Node
	Addr    ma.Multiaddr
}

func (p *Peer) String() string {
	return fmt.Sprintf("Peer(`%s`, `%s`)", p.Locator, p.Addr)
}

// GoString returns debug information for `%#v` format option
func (p *Peer) GoString() string {
	return fmt.Sprintf("Peer(Locator(%#v), Addr(%#v))",
		p.Locator, p.Addr)
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
		log.Printf("updated peer %s", peer)
	} else {
		peer = &Peer{
			Locator: &locators.Node{ID: upd.hash},
			Addr:    upd.addr,
		}
		p.peers[upd.id] = peer
		log.Printf("added new peer %s", peer)
	}
}
