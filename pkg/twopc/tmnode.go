// MIT License. Copyright (c) 2020 CQFN
// https://github.com/cqfn/degitx/blob/master/LICENSE

package twopc

import (
	"context"
	"fmt"
	"strings"
	"sync"

	"cqfn.org/degitx/pkg/tcommit"
	"github.com/hashicorp/go-multierror"
)

// TmNode implements transaction manager node instance
// for fixed set of resource managers
type TmNode struct {
	mux   sync.Mutex
	rms   map[tcommit.NodeID]tcommit.Resource
	votes map[tcommit.TxID]map[tcommit.NodeID]tcommit.Vote
}

// NewManager node for resource managers
func NewManager(rms map[tcommit.NodeID]tcommit.Resource) *TmNode {
	tm := new(TmNode)
	tm.rms = make(map[tcommit.NodeID]tcommit.Resource, len(rms))
	for k, v := range rms {
		tm.rms[k] = v
	}
	tm.votes = make(map[tcommit.TxID]map[tcommit.NodeID]tcommit.Vote)
	return tm
}

// ErrVoteConflict shows an error on voting where TM receives invalid
// votes from resource managers
type ErrVoteConflict struct {
	Node  tcommit.NodeID
	Votes []tcommit.Vote
}

func (err *ErrVoteConflict) Error() string {
	strs := make([]string, len(err.Votes))
	for i, val := range err.Votes {
		strs[i] = val.String()
	}
	return fmt.Sprintf("detected conflict on voting for node=`%s`: [%s]",
		err.Node, strings.Join(strs, ", "))
}

// Begin transaction, see tcommit.Manager intercace
func (tm *TmNode) Begin(ctx context.Context, tid tcommit.TxID,
	votes map[tcommit.NodeID]tcommit.Vote) error {
	tm.mux.Lock()
	defer tm.mux.Unlock()
	var cpy map[tcommit.NodeID]tcommit.Vote
	if val, has := tm.votes[tid]; has {
		cpy = make(map[tcommit.NodeID]tcommit.Vote, len(val))
		for k, v := range val {
			cpy[k] = v
		}
	} else {
		cpy = make(map[tcommit.NodeID]tcommit.Vote, len(votes))
		for id := range tm.rms {
			cpy[id] = tcommit.VoteUnkown
		}
	}
	for node, vte := range votes {
		if old := cpy[node]; conflicts(old, vte) {
			return &ErrVoteConflict{Node: node, Votes: []tcommit.Vote{old, vte}}
		}
		cpy[node] = vte
	}
	tm.votes[tid] = cpy
	return tm.decide(ctx, tid)
}

// Finish transaction, see tcommit.Manager intercace
func (tm *TmNode) Finish(ctx context.Context, id tcommit.NodeID) error {
	return nil
}

func (tm *TmNode) decide(ctx context.Context, tid tcommit.TxID) error {
	anyAbort := false
	allPrepared := true
	for _, vote := range tm.votes[tid] {
		if vote == tcommit.VoteAborted {
			anyAbort = true
			break
		}
		if vote != tcommit.VotePrepared {
			allPrepared = false
		}
	}
	if anyAbort {
		return tm.performAsync(ctx, func(rm tcommit.Resource) error {
			return rm.Abort(ctx, tid)
		})
	}
	if allPrepared {
		return tm.performAsync(ctx, func(rm tcommit.Resource) error {
			return rm.Commit(ctx, tid)
		})
	}
	return nil
}

func (tm *TmNode) performAsync(ctx context.Context,
	apply func(tcommit.Resource) error) error {
	var result *multierror.Error
	errchan := make(chan error)
	var wg sync.WaitGroup
	wg.Add(len(tm.rms))
	go func(errs chan<- error) {
		wg.Wait()
		close(errs)
	}(errchan)
	for _, rm := range tm.rms {
		go func(rm tcommit.Resource, errs chan<- error) {
			defer wg.Done()
			if err := apply(rm); err != nil {
				errs <- err
			}
		}(rm, errchan)
	}
LOOP:
	for {
		select {
		case err, open := <-errchan:
			if open {
				result = multierror.Append(result, err)
			} else {
				break LOOP
			}
		case <-ctx.Done():
			return ctx.Err()
		}
	}
	return result.ErrorOrNil()
}

func conflicts(old, update tcommit.Vote) bool {
	return !(old == update || old == tcommit.VoteUnkown)
}
