// MIT License. Copyright (c) 2020 CQFN
// https://github.com/cqfn/degitx/blob/master/LICENSE

package paxos

import (
	"context"
	"fmt"
	"hash/crc32"
	"sync"

	"cqfn.org/degitx/pkg/tcommit"
	"github.com/hashicorp/go-multierror"
)

type tmClient struct {
	accs   []Acceptor
	mux    *sync.Mutex
	remote tcommit.Manager
	votes  map[tcommit.NodeID]tcommit.Vote
	node   tcommit.NodeID
}

// NewTMClient creates a client interface for TM(s) using Paxos commit protocol
// for communication. On begin, this client proposes vote as a Paxos proposal to
// all acceptors and waits for promise message from acceptors. When vote is acceptors by
// acceptors, it performs `begin` TM remote call. Finish remote call goes directly to
// remote TM.
func NewTMClient(accs []Acceptor, tmRemote tcommit.Manager, node tcommit.NodeID) tcommit.Manager {
	return &tmClient{
		accs:   accs,
		mux:    new(sync.Mutex),
		remote: tmRemote,
		node:   node,
	}
}

func (tmc *tmClient) Begin(ctx context.Context, tid tcommit.TxID,
	vote map[tcommit.NodeID]tcommit.Vote) error {
	tmc.mux.Lock()
	defer tmc.mux.Unlock()

	tmc.mergeVotes(vote)

	hash := crc32.NewIEEE()
	if _, err := hash.Write([]byte(tmc.node)); err != nil {
		return fmt.Errorf("failed to get node id hash: %w", err)
	}
	proposal := Proposal{Ballot: Ballot(0), Proposer: hash.Sum32()}

	var me *multierror.Error
	for _, acc := range tmc.accs {
		if err := acc.Prepare(ctx, Px1A{proposal}); err != nil {
			me = multierror.Append(me, err)
		}
	}

	if err := me.ErrorOrNil(); err != nil {
		return fmt.Errorf("failed to prepare acceptors: %w", err)
	}
	return nil
}

func (tmc *tmClient) mergeVotes(vote map[tcommit.NodeID]tcommit.Vote) {
	for k, v := range vote {
		tmc.votes[k] = v
	}
}

func (tmc *tmClient) Finish(ctx context.Context, node tcommit.NodeID) error {
	return tmc.remote.Finish(ctx, node)
}
