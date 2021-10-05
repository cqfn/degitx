// MIT License. Copyright (c) 2020 CQFN
// https://github.com/cqfn/degitx/blob/master/LICENSE

package locators

import (
	"bytes"
	"encoding/binary"
	"fmt"

	"github.com/g4s8/go-bundle"
	ma "github.com/multiformats/go-multiaddr"
	mh "github.com/multiformats/go-multihash"
)

var version = [...]byte{0x00, 0x01}

var byteOrder = binary.BigEndian //nolint:gochecknoglobals //package private constant

// MarshalBinary is a binary encoding implementation
func (n *Node) MarshalBinary() ([]byte, error) {
	out := bundle.NewOut(byteOrder)
	out.PutBytes(version[:])
	out.PutBytes(n.ID)
	out.PutBytes(n.PubKey)
	out.PutBinary(n.Addr)
	return out.MarshalBinary()
}

// ErrUnsupportedVersion error if binary versio is not supported
type ErrUnsupportedVersion struct {
	version []byte
}

// Version which is not supported
func (e *ErrUnsupportedVersion) Version() []byte {
	return e.version
}

func (e *ErrUnsupportedVersion) Error() string {
	return fmt.Sprintf("Unsupported version `%s`", e.version)
}

// UnmarshalBinary is a binary decoding implementation
func (n *Node) UnmarshalBinary(data []byte) error {
	inp := bundle.NewInput(byteOrder)
	if err := inp.UnmarshalBinary(data); err != nil {
		return err
	}
	var v, rawID, pk, rawAddr []byte
	inp.GetBytes(&v)
	inp.GetBytes(&rawID)
	inp.GetBytes(&pk)
	inp.GetBytes(&rawAddr)

	if err := inp.Error(); err != nil {
		return err
	}

	if !bytes.Equal(version[:], v) {
		return &ErrUnsupportedVersion{v}
	}

	loc, err := mh.Cast(rawID)
	if err != nil {
		return err
	}
	addr, err := ma.NewMultiaddrBytes(rawAddr)
	if err != nil {
		return err
	}
	n.ID = loc
	n.PubKey = pk
	n.Addr = addr
	return nil
}
