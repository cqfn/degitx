// MIT License. Copyright (c) 2020 CQFN
// https://github.com/cqfn/degitx/blob/master/LICENSE

package tcommit

import "context"

// Resource manager API
type Resource interface {
	// Commit the transaction
	Commit(context.Context, TxID) error

	// Abort the transaction
	Abort(context.Context, TxID) error
}
