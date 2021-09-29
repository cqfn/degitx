// MIT License. Copyright (c) 2020 CQFN
// https://github.com/cqfn/degitx/blob/master/LICENSE

// Package tclient implements transaction commit clients for remote procedure calls.
package tclient

import (
	"context"

	"cqfn.org/degitx/pkg/tcommit"
	pb "cqfn.org/degitx/proto/go/tcommitpb"
)

// ManagerClient implemets tcommit.Manager interface.
// It is assumed to be a part of the resource manager
// for remote procedure calls.
type ManagerClient struct {
	client pb.ManagerServiceClient
}

// NewManagerClient with a given gRPC client.
func NewManagerClient(grpcClient pb.ManagerServiceClient) *ManagerClient {
	return &ManagerClient{grpcClient}
}

// Begin transaction RPC
func (r *ManagerClient) Begin(ctx context.Context, votes tcommit.Votes,
	meta tcommit.Meta) error {
	req := new(pb.BeginRequest)
	req.Meta.Meta = string(meta)
	vts := new(pb.Votes)
	for k, v := range votes {
		vote := new(pb.Vote)
		vote.Vote = uint32(v)
		vts.Votes[string(k)] = vote
	}
	req.Votes = vts
	_, err := r.client.Begin(ctx, req)
	return err
}

// Finish transaction RPC
func (r *ManagerClient) Finish(ctx context.Context, nodeID tcommit.NodeID,
	meta tcommit.Meta) error {
	req := new(pb.FinishRequest)
	req.NodeId = string(nodeID)
	req.Meta.Meta = string(meta)
	_, err := r.client.Finish(ctx, req)
	return err
}
