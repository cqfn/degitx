// MIT License. Copyright (c) 2020 CQFN
// https://github.com/cqfn/degitx/blob/master/LICENSE

// Package transaction provides API interfaces and implementations
// of atomic transaction for DeGitX. The workflow and research are
// explained in the white-paper. The brief description of files
// in this package:
//  - hook.go - interfaces for API of git reference-transaction hook
//    exposed for RM.
//  - manager.go - transaction manager (TM) API for resource manager (RM).
//  - meta.go - transaction metadata types, such as votes, scopes, identifiers.
//  - paxos.go - Paxos-commit interfaces, such as acceptors and proposers.
//  - rm.go - resource manager API for hook and TM.
package transaction

import (
	"context"

	"cqfn.org/degitx/pkg/locators"
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
	Begin(ctx context.Context, txn Transaction, vts Votes) error

	// Finish a transaction. RM notifies about finished transaction.
	// TM counts finished RM to send synchronous response to the client
	// when all RMs are finished. TM already know the state of the transaction,
	// so it needs only a notification hint from RMs without state parameters.
	Finish(ctx context.Context, node *locators.Node) error
}
