// MIT License. Copyright (c) 2020 CQFN
// https://github.com/cqfn/degitx/blob/master/LICENSE

package paxos

// Storage for acepted value on consensus to persist
type Storage interface {
	// Get current value
	Get() ([]byte, error)
	// Put value
	Put([]byte) error
}
