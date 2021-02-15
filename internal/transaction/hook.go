// MIT License. Copyright (c) 2020 CQFN
// https://github.com/cqfn/degitx/blob/master/LICENSE

package transaction

// Hook API of git reference transaction
type Hook interface {
	// Exit transaction hook with success status
	Continue() error
	// Exit transaction hook with error abort status
	Abort() error
}
