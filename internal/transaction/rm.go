// MIT License. Copyright (c) 2020 CQFN
// https://github.com/cqfn/degitx/blob/master/LICENSE

package transaction

import "context"

// Resource manager API
type Resource interface {
	// Commit the transaction
	Commit(ctx context.Context, txn string) error

	// Abort the transaction
	Abort(ctx context.Context, txn string) error
}
