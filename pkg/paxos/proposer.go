// MIT License. Copyright (c) 2020 CQFN
// https://github.com/cqfn/degitx/blob/master/LICENSE

package paxos

import (
	"context"
)

// Proposer - Paxos proposer API for acceptor
type Proposer interface {
	// Promise is a 1B message from acceptor.
	// was prepared successfully, it includes a proposal ballot
	// number. Promise means that acceptor promises to proposer
	// to reject all next messages if ballot number of such message
	// are less than ballot number of promise.
	Promise(ctx context.Context, msg Px1B) error

	// Accepted message is sent by acceptor as a 2B message, if it
	// successfully accepted 2A message from a proposer.
	Accepted(ctx context.Context, msg Px2B) error

	// Reject is a optimization of Paxos. Instead of ignoring 1A message with
	// small ballot numbers (less than ballot number that acceptor perofrmed any action),
	// acceptor may send a reject message to avoid proposer restarts by timeout and
	// sends a hint with ballot number to help choosing proposer next ballot number
	// greater than any received: bal=max([]rejects)+1
	Reject(ctx context.Context, bal Ballot) error
}
