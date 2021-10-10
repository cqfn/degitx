// MIT License. Copyright (c) 2020 CQFN
// https://github.com/cqfn/degitx/blob/master/LICENSE

package paxos

import (
	"context"

	"cqfn.org/degitx/pkg/paxos/grpc/pb"
	"cqfn.org/degitx/pkg/tcommit"
	"google.golang.org/grpc/metadata"
)

// AcceptorClient implemets paxos.Acceptor interface.
// It is assumed to be a part of the resource manager
// for remote procedure calls.
type AcceptorClient struct {
	client pb.AcceptorServiceClient
	NodeID tcommit.NodeID
	TxID   tcommit.TxID
}

// NewAcceptorClient with a given gRPC client.
// NodeID and TxID are necessary to identify Paxos instance in a multi-transactional model.
func NewAcceptorClient(grpcClient pb.AcceptorServiceClient, nodeID tcommit.NodeID,
	txID tcommit.TxID) *AcceptorClient {
	return &AcceptorClient{grpcClient, nodeID, txID}
}

// Prepare message RPC
func (ac *AcceptorClient) Prepare(ctx context.Context, msg Px1A) error {
	req := new(pb.PrepareRequest)
	m := new(pb.Px1A)
	m.Proposal.Ballot.Ballot = uint32(msg.Ballot)
	m.Proposal.Proposer = msg.Proposer
	req.Msg = m
	md := metadata.Pairs("node_id", string(ac.NodeID), "tx_id", string(ac.TxID))
	ctx = metadata.NewOutgoingContext(ctx, md)
	_, err := ac.client.Prepare(ctx, req)
	return err
}

// Accept message RPC
func (ac *AcceptorClient) Accept(ctx context.Context, msg Px2A) error {
	req := new(pb.AcceptRequest)
	m := new(pb.Px2A)
	m.Proposal.Ballot.Ballot = uint32(msg.Ballot)
	m.Proposal.Proposer = msg.Proposer
	val, err := msg.Value.MarshalBinary()
	if err != nil {
		return err
	}
	m.Value = val
	req.Msg = m
	md := metadata.Pairs("node_id", string(ac.NodeID), "tx_id", string(ac.TxID))
	ctx = metadata.NewOutgoingContext(ctx, md)
	_, err = ac.client.Accept(ctx, req)
	return err
}
