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

	"cqfn.org/degitx/locators"
)

// Manager of the transaction
type Manager interface {
	// Begin a transaction, update votes for RMs
	Begin(ctx context.Context, txn Transaction, vts Votes) error
	// Finish a transaction
	Finish(ctx context.Context, node *locators.Node) error
}
