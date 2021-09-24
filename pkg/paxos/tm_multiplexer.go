// MIT License. Copyright (c) 2020 CQFN
// https://github.com/cqfn/degitx/blob/master/LICENSE

package paxos

import (
	"context"

	"cqfn.org/degitx/pkg/tcommit"
	"github.com/hashicorp/go-multierror"
)

type tmMultiplexer struct {
	tms []tcommit.Manager
}

// MultiplexTMs sends delivers remote calls to each TM from the list.
// It could be used for fault-tolerance across TM nodes. If any TM node
// fails another can handle all operations. Since we're using distributed
// transaction state storage across Paxos acceptors, all TMs will make
// conflictless decision based on distributed vote data.
func MultiplexTMs(tms []tcommit.Manager) tcommit.Manager {
	return &tmMultiplexer{tms}
}

func (tmm *tmMultiplexer) multiplex(call func(tcommit.Manager) error) error {
	var me *multierror.Error
	for _, tm := range tmm.tms {
		if err := call(tm); err != nil {
			me = multierror.Append(err)
		}
	}
	return me.ErrorOrNil()
}

func (tmm *tmMultiplexer) Begin(ctx context.Context, tid tcommit.TxID,
	vote map[tcommit.NodeID]tcommit.Vote) error {
	return tmm.multiplex(func(tm tcommit.Manager) error {
		return tm.Begin(ctx, tid, vote)
	})
}

func (tmm *tmMultiplexer) Finish(ctx context.Context, node tcommit.NodeID) error {
	return tmm.multiplex(func(tm tcommit.Manager) error {
		return tm.Finish(ctx, node)
	})
}
