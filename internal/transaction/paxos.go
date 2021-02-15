// MIT License. Copyright (c) 2020 CQFN
// https://github.com/cqfn/degitx/blob/master/LICENSE

package transaction

import (
	"context"
)

// Ballot number of proposals in Paxos algorithm
type Ballot uint16

// Proposal for Paxos protocol
type Proposal struct {
	// Ballot number of the proposal
	Ballot
	// Proposer ID, it should be unique number for each
	// proposer participating in the transaction.
	Proposer uint16
}

// PxAcceptor - Paxos acceptor API for proposer
type PxAcceptor interface {
	// Prepare takes Paxos 1A message and sends 1B message to the proposer
	Prepare(ctx context.Context, p Proposal) error
	// Accept takes Paxos 2A message and sends 2B message to proposer
	Accept(ctx context.Context, p Proposal, v Vote) error
}

// PxProposer - Paxos proposer API for acceptor
type PxProposer interface {
	// Promise is sent by acceptor as 1B message if acceptor
	// was prepared succesffully, it includes a proposal ballot
	// number. Promise means that acceptor promises to proposer
	// to reject all next messages if ballot number of such message
	// are less than ballot number of promise.
	Promise(ctx context.Context, b Ballot) error

	// Reject 1B message from acceptor. The acceptor sends such message
	// if it already accepted a value from proposer. The reject message
	// includes the ballot number of accepted value and the actual value.
	Reject(ctx context.Context, b Ballot, v Vote) error

	// Accepted message is sent by acceptor as a 2B message, if it
	// successfully accepted 2A message from a proposer.
	Accepted(ctx context.Context, b Ballot) error
}

// RMProposer - proposer API for resource manager
type RMProposer interface {
	// Propose a vote
	Propose(ctx context.Context, v Vote) error
}
