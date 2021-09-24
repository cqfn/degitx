// MIT License. Copyright (c) 2020 CQFN
// https://github.com/cqfn/degitx/blob/master/LICENSE

package paxos

// Ballot number of proposals in Paxos algorithm
type Ballot uint16

//nolint:gochecknoglobals // it's a zero constant
var pZero = Proposal{Ballot: Ballot(0), Proposer: 0}

// Proposal for Paxos protocol
type Proposal struct {
	// Ballot number of the proposal
	Ballot
	// Proposer ID, it should be unique number for each
	// proposer participating in the transaction.
	Proposer uint32
}

// Compare two proposals
func (p Proposal) Compare(o Proposal) int {
	var r int
	r = int(p.Ballot - o.Ballot)
	if r == 0 {
		r = int(p.Proposer - o.Proposer)
	}
	return r
}
