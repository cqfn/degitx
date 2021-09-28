// MIT License. Copyright (c) 2020 CQFN
// https://github.com/cqfn/degitx/blob/master/LICENSE

package tcommit

import (
	"context"
)

// Manager of the transaction (TM).
type Manager interface {
	// Begin a transaction, update votes for RMs.
	// RM starts a transaction when it's prepared. RM doesn't
	// know if the transaction was started already, so it always
	// assume it's not started yet and calls begin-transaction of
	// TM. RM includes all known votes about the transaction
	// into this message, so TM has to merge all votes
	// and manage the transaction state correctly. If TM sees that
	// It receives a quorum of `prepared` votes for each RM,
	// it can decide to commit; or if it receives a quorum
	// of `abort` at least for one RM, it can decide to abort.
	Begin(context.Context, Votes, Meta) error

	// Finish a transaction. RM notifies about finished transaction.
	// TM counts finished RM to send synchronous response to the client
	// when all RMs are finished. TM already know the state of the transaction,
	// so it needs only a notification hint from RMs without state parameters.
	Finish(context.Context, NodeID, Meta) error
}
