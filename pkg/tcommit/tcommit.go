// MIT License. Copyright (c) 2020 CQFN
// https://github.com/cqfn/degitx/blob/master/LICENSE

// Package tcommit provides API interfaces and base primitives
// for transacrion commit protocol. Base types are `Manager`
// which specify interface for transaction manager (TM)
// and `Resource` for resource manager (RM).
// This API assumes that RM votes on the transaction that can be
// either prepared or aborted. RM also may know votes of other RMs
// but it's not required.
package tcommit

import (
	"errors"
)

// Vote of RM
//go:generate stringer -type=Vote
type Vote uint8

// ErrInvalidVote is thrown in case of a vote is not valid
var ErrInvalidVote = errors.New("invalid Vote")

const (
	// VoteUnkown means that RM was not decided yet
	VoteUnkown Vote = iota
	// VotePrepared means that RM was prepared to commit
	VotePrepared
	// VoteAborted means that RM failed to prepare
	VoteAborted
)

// Validate the vote value
// Returns ErrInvalidVote in case if the Value is invalid
func (v Vote) Validate() error {
	if v > VoteAborted {
		return ErrInvalidVote
	}

	return nil
}

// TxID is unique identifier of the transacion
type TxID string

// NodeID unique identifier of the RM
type NodeID string

// Votes is a map of votes by node
type Votes map[NodeID]Vote

// Meta is an optional additional transaction metadata that could be sent by RM
// and used by TM.
type Meta string
