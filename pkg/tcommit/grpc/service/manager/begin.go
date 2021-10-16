// MIT License. Copyright (c) 2020 CQFN
// https://github.com/cqfn/degitx/blob/master/LICENSE

package manager

import (
	"context"

	"cqfn.org/degitx/pkg/tcommit/grpc/marshall"
	"cqfn.org/degitx/pkg/tcommit/grpc/pb"
	"google.golang.org/grpc/codes"
	"google.golang.org/grpc/status"
)

// Begin transaction
// Votes and Meta are validated before the actual calling of the tcommit.Manager
// Any errors from the tcommit.Manager are passed as the Internal
func (s *Service) Begin(ctx context.Context, req *pb.BeginRequest) (*pb.BeginResponse, error) {
	votes, err := marshall.FromProtoVotes(req.GetVotes())
	if err != nil {
		return nil, status.Error(codes.InvalidArgument, err.Error())
	}

	meta, err := marshall.FromProtoMeta(req.GetMeta())
	if err != nil {
		return nil, status.Error(codes.InvalidArgument, err.Error())
	}

	if err := s.tm.Begin(ctx, votes, meta); err != nil {
		return nil, status.Error(codes.Internal, err.Error())
	}

	return &pb.BeginResponse{}, nil
}
