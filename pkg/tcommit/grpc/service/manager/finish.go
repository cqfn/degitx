// MIT License. Copyright (c) 2020 CQFN
// https://github.com/cqfn/degitx/blob/master/LICENSE

package manager

import (
	"context"

	"cqfn.org/degitx/pkg/tcommit"
	"cqfn.org/degitx/pkg/tcommit/grpc/marshall"
	"cqfn.org/degitx/pkg/tcommit/grpc/pb"
	"google.golang.org/grpc/codes"
	"google.golang.org/grpc/status"
)

// Finish transaction
// Meta is validated before the actual calling of the tcommit.Manager
// Any errors from the tcommit.Manager are passed as the Internal
func (s *Service) Finish(ctx context.Context, req *pb.FinishRequest) (*pb.FinishResponse, error) {
	meta, err := marshall.FromProtoMeta(req.GetMeta())
	if err != nil {
		return nil, status.Error(codes.InvalidArgument, err.Error())
	}

	node := tcommit.NodeID(req.GetNodeId())

	if err := s.tm.Finish(ctx, node, meta); err != nil {
		return nil, status.Error(codes.Internal, err.Error())
	}

	return &pb.FinishResponse{}, nil
}
