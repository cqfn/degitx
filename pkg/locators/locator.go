// MIT License. Copyright (c) 2020 CQFN
// https://github.com/cqfn/degitx/blob/master/LICENSE

// Package locators represents node identities,
// it's hash function representing in
// Multihash format: https://multiformats.io/multihash/
package locators

import (
	"crypto/sha1" //nolint:gosec //testing
	"fmt"
	"hash"
	"strings"

	mh "github.com/multiformats/go-multihash"
)

// Node core identities
type Node struct {
	ID      mh.Multihash
	PubKey  []byte
	PrivKey []byte
}

func (n *Node) String() string {
	return fmt.Sprintf("Node(`%s`)", n.ID.HexString())
}

// GoString returns debug information for `%#v` format option
func (n *Node) GoString() string {
	return fmt.Sprintf("Node(ID(%#v), PubKey(%#v))",
		n.ID, n.PubKey)
}

const hname = "sha1"

// FromKeys creates new Node struct from public and private keys
// by generating node id as multihash of SHA1 of public key
func FromKeys(pub, priv []byte) (*Node, error) {
	hfunc, err := hashFunc(hname)
	if err != nil {
		return nil, err
	}
	_, err = hfunc.Write(pub)
	if err != nil {
		return nil, err
	}
	hsum := hfunc.Sum(nil)
	hash, err := mh.EncodeName(hsum, hname)
	if err != nil {
		return nil, err
	}
	return &Node{
		ID:      mh.Multihash(hash),
		PubKey:  pub,
		PrivKey: priv,
	}, nil
}

// UnsupportedHashError if hashing algorithm specified is not supported
type UnsupportedHashError struct {
	// Name of hash algorithm
	Name string
}

func (e *UnsupportedHashError) Error() string {
	return fmt.Sprintf("Unsupported hash-func name: `%s`", e.Name)
}

func hashFunc(name string) (hash.Hash, error) {
	name = strings.ToUpper(name)
	switch name {
	case "SHA1":
		return sha1.New(), nil //nolint:gosec //testing
	default:
		return nil, &UnsupportedHashError{name}
	}
}
