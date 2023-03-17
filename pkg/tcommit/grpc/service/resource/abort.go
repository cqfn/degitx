// MIT License. Copyright (c) 2020 CQFN
// https://github.com/cqfn/degitx/blob/master/LICENSE

package resource

import (
	"context"

	"cqfn.org/degitx/pkg/tcommit/grpc/pb"
	"google.golang.org/grpc/codes"
	"google.golang.org/grpc/status"
)

// Abort transaction
// Any errors from the tcommit.Resource are passed as the Internal
func (s *Service) Abort(ctx context.Context, _ *pb.AbortRequest) (*pb.AbortResponse, error) {
	if err := s.rm.Abort(ctx); err != nil {
		return nil, status.Errorf(codes.Internal, err.Error())
	}

	return &pb.AbortResponse{}, nil
}
