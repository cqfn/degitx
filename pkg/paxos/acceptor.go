// MIT License. Copyright (c) 2020 CQFN
// https://github.com/cqfn/degitx/blob/master/LICENSE

package paxos

import (
	"context"
	"fmt"
	"sync"
)

// Acceptor - Paxos acceptor API for proposer
type Acceptor interface {
	// Prepare takes Paxos 1A message. The proposer chooses ballot number
	// that it believes to be larger than any ballot number for which
	// phase 1 has been performed, and sends it to every acceptor for prepare.
	Prepare(ctx context.Context, msg Px1A) error

	// Accept takes Paxos 2A message. The proposer uses ballot number it has
	// already prepared and acceptor promised to reject all proposals fewer than
	// prepared one. It tries to accept a vote by proposal. If the bigger ballot
	// number was prepared by acceptor between these two operations, acceptor may
	// respond with reject.
	Accept(ctx context.Context, msg Px2A) error
}

type accInst struct {
	mux      sync.Mutex
	min, acc Proposal
	prop     Proposer
	storage  Storage
}

// NewAcceptorNode creates a node for acceptor with provided storage
// and proposer API
func NewAcceptorNode(prop Proposer, storage Storage) Acceptor {
	return &accInst{prop: prop, storage: storage}
}

type encodedValue struct {
	raw []byte
}

func (v *encodedValue) MarshalBinary() ([]byte, error) {
	return v.raw, nil
}

func (inst *accInst) Prepare(ctx context.Context, msg Px1A) error {
	inst.mux.Lock()
	defer inst.mux.Unlock()

	if msg.Proposal.Compare(inst.min) >= 0 {
		return inst.prop.Reject(ctx, inst.min.Ballot)
	}
	//nolint:nestif // consider refactoring
	if inst.acc.Compare(pZero) > 0 {
		val, err := inst.storage.Get()
		if err != nil {
			return fmt.Errorf("failed to get current value: %w", err)
		}
		if err := inst.prop.Promise(ctx, Px1B{
			Max:   inst.min,
			Acc:   inst.acc,
			Value: &encodedValue{val},
		}); err != nil {
			return fmt.Errorf("proposer failed at 1B msg: %w", err)
		}
	} else {
		inst.min = msg.Proposal
		if err := inst.prop.Promise(ctx, Px1B{Max: inst.min}); err != nil {
			return fmt.Errorf("proposer failed: %w", err)
		}
	}
	return nil
}

func (inst *accInst) Accept(ctx context.Context, msg Px2A) error {
	inst.mux.Lock()
	defer inst.mux.Unlock()

	if msg.Proposal.Compare(inst.min) < 0 {
		return nil
	}
	val, err := msg.Value.MarshalBinary()
	if err != nil {
		return fmt.Errorf("failed to encode value: %w", err)
	}
	if err := inst.storage.Put(val); err != nil {
		return fmt.Errorf("failed to write to storage: %w", err)
	}
	inst.acc = msg.Proposal
	if err := inst.prop.Accepted(ctx, Px2B{Ballot: inst.acc.Ballot}); err != nil {
		return fmt.Errorf("proposer failed at 2B msg: %w", err)
	}
	return nil
}
