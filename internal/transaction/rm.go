// MIT License. Copyright (c) 2020 CQFN
// https://github.com/cqfn/degitx/blob/master/LICENSE

package transaction

import "context"

// ResourceManager API
type ResourceManager interface {
	// Vote for decision, this method called by the webhook
	// when it's ready to prepare or it's aborted.
	Vote(ctx context.Context, txn string, v Vote) error

	// Commit the transaction
	Commit(ctx context.Context, txn string) error

	// Abort the transaction
	Abort(ctx context.Context, txn string) error
}
