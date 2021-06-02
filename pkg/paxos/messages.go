// MIT License. Copyright (c) 2020 CQFN
// https://github.com/cqfn/degitx/blob/master/LICENSE

package paxos

import "encoding"

// Value binary of message
type Value encoding.BinaryMarshaler

// Px1A - Paxos 1A message sent from proposer to acceptor
type Px1A struct {
	Proposal
}

// Px2A - Paxos 2A message sent from proposer to acceptor
type Px2A struct {
	Proposal
	Value
}

// Px1B - Paxos 1B message sent from acceptor to proposer,
// it contains maximum and accepted proposal and optional value
type Px1B struct {
	Max, Acc Proposal
	Value
}

// Px2B - Paxos 2B message sent from acceptor to proposer
type Px2B struct {
	Ballot
}
