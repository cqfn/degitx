// MIT License. Copyright (c) 2020 CQFN
// https://github.com/cqfn/degitx/blob/master/LICENSE

package resource

import (
	"context"

	"cqfn.org/degitx/pkg/tcommit/grpc/pb"
	"google.golang.org/grpc/codes"
	"google.golang.org/grpc/status"
)

// Commit transaction
// Any errors from the tcommit.Resource are passed as the Internal
func (s *Service) Commit(ctx context.Context, _ *pb.CommitRequest) (*pb.CommitResponse, error) {
	if err := s.rm.Commit(ctx); err != nil {
		return nil, status.Error(codes.Internal, err.Error())
	}

	return &pb.CommitResponse{}, nil
}
