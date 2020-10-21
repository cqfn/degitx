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

// Locator of node
type Locator interface {
	// Multihash of current locator
	Multihash() (mh.Multihash, error)
}

type hashLoc struct {
	hash []byte
	name string
}

func (l *hashLoc) Multihash() (mh.Multihash, error) {
	bts, err := mh.EncodeName(l.hash, l.name)
	if err != nil {
		return nil, err
	}
	h := mh.Multihash(bts)
	return h, nil
}

type unsupportedHashError struct {
	name string
}

func (e *unsupportedHashError) Error() string {
	return fmt.Sprintf("Unsupported hash-func name: `%s`", e.name)
}

func hashFunc(name string) (hash.Hash, error) {
	name = strings.ToUpper(name)
	switch name {
	case "SHA1":
		return sha1.New(), nil //nolint:gosec //testing
	default:
		return nil, &unsupportedHashError{name}
	}
}

// NewHash locator for binary data and hash-func name
func NewHash(data []byte, name string) (Locator, error) {
	hf, err := hashFunc(name)
	if err != nil {
		return nil, err
	}
	if _, err := hf.Write(data); err != nil {
		return nil, err
	}
	hash := hf.Sum(nil)
	return &hashLoc{hash, name}, nil
}

type mhLocator struct {
	hash mh.Multihash
}

func (l *mhLocator) Multihash() (mh.Multihash, error) {
	return l.hash, nil
}

// FromBytes creates new multihash locator from bytes, returns error if invalid
func FromBytes(data []byte) (Locator, error) {
	hash, err := mh.Cast(data)
	if err != nil {
		return nil, err
	}
	return &mhLocator{hash}, nil
}
