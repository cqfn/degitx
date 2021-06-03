// MIT License. Copyright (c) 2020 CQFN
// https://github.com/cqfn/degitx/blob/master/LICENSE

package tcommit

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

// TxID is unique identifier of the transacion
type TxID string

// NodeID unique identifier of the RM
type NodeID string
