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

// Compare two proposals
func (p Proposal) Compare(o Proposal) int {
	var r int
	r = int(p.Ballot - o.Ballot)
	if r == 0 {
		r = int(p.Proposer - o.Proposer)
	}
	return r
}

// Px1A - Paxos 1A message sent from proposer to acceptor
type Px1A struct {
	Proposal
}

// Px2A - Paxos 2A message sent from proposer to acceptor
type Px2A struct {
	Proposal
	// Value to accept
	Value Vote
}

// PxAcceptor - Paxos acceptor API for proposer
type PxAcceptor interface {
	// Prepare takes Paxos 1A message. The proposer chooses ballot number
	// that it believes to be larger than any ballot number for which
	// phase 1 has been performed, and sends it to every acceptor for prepare.
	Prepare(ctx context.Context, msg Px1A) error

	// Accept takes Paxos 2A message. The proposer uses ballot number it has
	// already prepared and acceptor promised to reject all proposals fewer than
	// prepared one. It tries to accept a vote by proposal. If the bigger ballot
	// number was prepared by acceptor between these two operations, acceptor may
	// respond with reject.
	Accept(ctx context.Context, msg Px2A) error
}

// Px1B - Paxos 1B message sent from acceptor to proposer
type Px1B struct {
	Max, Acc Ballot
	Value    Vote
}

// Px2B - Paxos 2B message sent from acceptor to proposer
type Px2B struct {
	Ballot
}

// PxProposer - Paxos proposer API for acceptor
type PxProposer interface {
	// Promise is a 1B message from acceptor.
	// was prepared succesffully, it includes a proposal ballot
	// number. Promise means that acceptor promises to proposer
	// to reject all next messages if ballot number of such message
	// are less than ballot number of promise.
	Promise(ctx context.Context, msg Px1B) error

	// Accepted message is sent by acceptor as a 2B message, if it
	// successfully accepted 2A message from a proposer.
	Accepted(ctx context.Context, msg Px1B) error

	// Reject is a optimization of Paxos. Instead of ignoring 1A message with
	// small ballot numbers (less than ballot number that acceptor perofrmed any action),
	// acceptor may send a reject message to avoid proposer restarts by timeout and
	// sends a hint with ballot number to help choosing proposer next ballot number
	// greater than any received: bal=max([]rejects)+1
	Reject(ctx context.Context, bal Ballot) error
}

// RMProposer - proposer API for resource manager
type RMProposer interface {
	// Propose a vote
	Propose(ctx context.Context, v Vote) error
}
