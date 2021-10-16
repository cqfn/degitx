// MIT License. Copyright (c) 2020 CQFN
// https://github.com/cqfn/degitx/blob/master/LICENSE

// Package client implements transaction protocols using gRPC
package client

import (
	"context"

	"cqfn.org/degitx/pkg/tcommit"
	"cqfn.org/degitx/pkg/tcommit/grpc/marshall"
	"cqfn.org/degitx/pkg/tcommit/grpc/pb"
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
func (r *ManagerClient) Begin(
	ctx context.Context, votes tcommit.Votes, meta tcommit.Meta,
) error {
	req := &pb.BeginRequest{
		Votes: marshall.ToProtoVotes(votes),
		Meta:  &pb.Meta{Meta: string(meta)},
	}
	_, err := r.client.Begin(ctx, req)
	return err
}

// Finish transaction RPC
func (r *ManagerClient) Finish(
	ctx context.Context, nodeID tcommit.NodeID, meta tcommit.Meta,
) error {
	req := &pb.FinishRequest{
		NodeId: string(nodeID),
		Meta:   &pb.Meta{Meta: string(meta)},
	}
	_, err := r.client.Finish(ctx, req)
	return err
}
