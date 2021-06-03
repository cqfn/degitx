// MIT License. Copyright (c) 2020 CQFN
// https://github.com/cqfn/degitx/blob/master/LICENSE

// Package tcommit provides API interfaces and base primitives
// for transacrion commit protocol. Base types are `Manager`
// which specify interface for transaction manager (TM)
// and `Resource` for resource manager (RM).
// This API assumes that RM votes on the transaction that can be
// either prepared or aborted. RM also may know votes of other RMs
// but it's not required.
package tcommit
