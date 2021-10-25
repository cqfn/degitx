// MIT License. Copyright (c) 2020 CQFN
// https://github.com/cqfn/degitx/blob/master/LICENSE

package paxos

import (
	"context"

	"cqfn.org/degitx/pkg/paxos/grpc/pb"
	"cqfn.org/degitx/pkg/tcommit"
	"google.golang.org/grpc/metadata"
)

// ProposerClient implemets paxos.Proposer interface.
// It is assumed to be a part of the resource manager
// for remote procedure calls.
type ProposerClient struct {
	client pb.ProposerServiceClient
	NodeID tcommit.NodeID
	TxID   tcommit.TxID
}

// NewProposerClient with a given gRPC client.
// NodeID and TxID are necessary to identify Paxos instance in a multi-transactional model.
func NewProposerClient(grpcClient pb.ProposerServiceClient, nodeID tcommit.NodeID,
	txID tcommit.TxID) *ProposerClient {
	return &ProposerClient{grpcClient, nodeID, txID}
}

// Promise message RPC
func (pc *ProposerClient) Promise(ctx context.Context, msg Px1B) error {
	req := new(pb.PromiseRequest)
	max := new(pb.Proposal)
	acc := new(pb.Proposal)
	max.Ballot.Ballot = uint32(msg.Max.Ballot)
	acc.Ballot.Ballot = uint32(msg.Acc.Ballot)
	max.Proposer = msg.Max.Proposer
	acc.Proposer = msg.Acc.Proposer
	val, err := msg.Value.MarshalBinary()
	if err != nil {
		return err
	}
	m := &pb.Px1B{Max: max, Acc: acc, Value: val}
	req.Msg = m
	md := metadata.Pairs("node_id", string(pc.NodeID), "tx_id", string(pc.TxID))
	ctx = metadata.NewOutgoingContext(ctx, md)
	_, err = pc.client.Promise(ctx, req)
	return err
}

// Accepted message RPC
func (pc *ProposerClient) Accepted(ctx context.Context, msg Px2B) error {
	req := new(pb.AcceptedRequest)
	m := new(pb.Px2B)
	m.Ballot.Ballot = uint32(msg.Ballot)
	req.Msg = m
	md := metadata.Pairs("node_id", string(pc.NodeID), "tx_id", string(pc.TxID))
	ctx = metadata.NewOutgoingContext(ctx, md)
	_, err := pc.client.Accepted(ctx, req)
	return err
}

// Reject message RPC
func (pc *ProposerClient) Reject(ctx context.Context, bal Ballot) error {
	req := new(pb.RejectRequest)
	req.Ballot.Ballot = uint32(bal)
	md := metadata.Pairs("node_id", string(pc.NodeID), "tx_id", string(pc.TxID))
	ctx = metadata.NewOutgoingContext(ctx, md)
	_, err := pc.client.Reject(ctx, req)
	return err
}
