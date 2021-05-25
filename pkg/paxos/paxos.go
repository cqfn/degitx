// MIT License. Copyright (c) 2020 CQFN
// https://github.com/cqfn/degitx/blob/master/LICENSE

// Package paxos is a Paxos-simple protocol implementation for Go.
// It abstract away from transport layer and storage implementation
// by providing interfaces for proposer and acceptor nodes.
// Each node should implement transport over network via API
// to expose API to nodes. Some standard storage implementations
// are available at `storage.go` file, or custom storage could be used.
package paxos
