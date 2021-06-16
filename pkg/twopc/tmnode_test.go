// MIT License. Copyright (c) 2020 CQFN
// https://github.com/cqfn/degitx/blob/master/LICENSE

package twopc

import (
	"context"
	"sync"
	"testing"

	tc "cqfn.org/degitx/pkg/tcommit"
	m "github.com/g4s8/go-matchers"
)

type testCase struct {
	name   string
	msg    string
	ids    []tc.NodeID
	votes  map[tc.NodeID]tc.Vote
	expect string
}

func TestTmDecideCommit(t *testing.T) {
	for _, tcase := range []*testCase{
		{
			name: "Vote all prepared",
			msg:  "TM decide to commit if all RMs are prepared",
			ids: []tc.NodeID{
				tc.NodeID("1.1"),
				tc.NodeID("1.2"),
				tc.NodeID("1.3"),
			},
			votes: map[tc.NodeID]tc.Vote{
				tc.NodeID("1.1"): tc.VotePrepared,
				tc.NodeID("1.2"): tc.VotePrepared,
				tc.NodeID("1.3"): tc.VotePrepared,
			},
			expect: "commit",
		},
		{
			name: "Vote one aborted",
			msg:  "TM abort if any RM abort",
			ids: []tc.NodeID{
				tc.NodeID("2.1"),
				tc.NodeID("2.2"),
				tc.NodeID("2.3"),
			},
			votes: map[tc.NodeID]tc.Vote{
				tc.NodeID("2.1"): tc.VotePrepared,
				tc.NodeID("2.2"): tc.VotePrepared,
				tc.NodeID("2.3"): tc.VoteAborted,
			},
			expect: "abort",
		},
	} {
		t.Run(tcase.name, testForCase(tcase))
	}
}

func testForCase(tcase *testCase) func(t *testing.T) {
	return func(t *testing.T) {
		rms := make([]*rmStub, len(tcase.ids))
		for i, id := range tcase.ids {
			rm := new(rmStub)
			rm.id = id
			rms[i] = rm
		}
		rmmap := make(map[tc.NodeID]tc.Resource)
		for _, rm := range rms {
			rmmap[rm.id] = rm
		}
		tm := NewManager(rmmap)
		for _, rm := range rms {
			rm.tm = tm
		}
		var wg sync.WaitGroup
		wg.Add(len(rms))
		for _, rm := range rms {
			go func(rm *rmStub, v tc.Vote) {
				rm.run(v)
				wg.Done()
			}(rm, tcase.votes[rm.id])
		}
		wg.Wait()
		results := make([]string, len(rms))
		for i, rm := range rms {
			results[i] = rm.decision
		}
		expect := make([]string, len(rms))
		for i := range expect {
			expect[i] = tcase.expect
		}
		m.Assert(t).That(tcase.msg, results, m.Eq(expect))
	}
}

type rmStub struct {
	id       tc.NodeID
	tm       tc.Manager
	decision string
	mux      sync.Mutex
}

func (rm *rmStub) Commit(ctx context.Context, tid tc.TxID) error {
	rm.mux.Lock()
	rm.decision = "commit"
	rm.mux.Unlock()
	return nil
}

func (rm *rmStub) Abort(ctx context.Context, tid tc.TxID) error {
	rm.mux.Lock()
	rm.decision = "abort"
	rm.mux.Unlock()
	return nil
}

func (rm *rmStub) run(v tc.Vote) {
	vts := make(map[tc.NodeID]tc.Vote)
	vts[rm.id] = v
	if err := rm.tm.Begin(context.Background(), tc.TxID("txn"), vts); err != nil {
		panic(err)
	}
}
