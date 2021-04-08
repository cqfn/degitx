// MIT License. Copyright (c) 2020 CQFN
// https://github.com/cqfn/degitx/blob/master/LICENSE

package transaction

import "cqfn.org/degitx/locators"

// Vote of RM
type Vote uint8

const (
	// VotePrepared means that RM was prepared to commit
	VotePrepared Vote = iota
	// VoteAborted means that RM failed to prepare
	VoteAborted
	// VoteUnkown means that RM was not decided yet
	VoteUnkown
)

// Scope of the transaction
type Scope struct {
	// Acceptors for this transaction
	Acceptors []*locators.Node
	// TM nodes (first is primary)
	TM []locators.Node
}

// Transaction metadata
type Transaction struct {
	ID string
	Scope
}

// Votes of all RMs
type Votes struct {
	// Table of votes by RM id
	Table map[*locators.Node]Vote
}
