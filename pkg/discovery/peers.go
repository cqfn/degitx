// MIT License. Copyright (c) 2020 CQFN
// https://github.com/cqfn/degitx/blob/master/LICENSE

package discovery

import (
	"fmt"

	"cqfn.org/degitx/pkg/locators"
	ma "github.com/multiformats/go-multiaddr"
	mh "github.com/multiformats/go-multihash"
)

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

// PeerTable stores addresses for known peers
type PeerTable interface {
	// Update peer table with a new entry
	Update(Peer)

	// Lookup for peer by it's locator ID
	Lookup(mh.Multihash) (Peer, bool)
}

// LocalTable is a local in memory peer table
type LocalTable struct {
	peers map[string]Peer
}

// NewLocalTable peer table
func NewLocalTable() *LocalTable {
	t := new(LocalTable)
	t.peers = make(map[string]Peer)
	return t
}

// Update local table with a new peer
func (t *LocalTable) Update(p Peer) {
	t.peers[p.Addr.String()] = p
}

// Lookup for peer by it's locator ID
func (t *LocalTable) Lookup(id mh.Multihash) (res Peer, found bool) {
	p, ok := t.peers[id.String()]
	if ok {
		res = p
	}
	found = ok
	return //nolint:nakedret // naked return for found is OK here
}
