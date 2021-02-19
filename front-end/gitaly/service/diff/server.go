// MIT License. Copyright (c) 2020 CQFN
// https://github.com/cqfn/degitx/blob/master/LICENSE

// Package diff contains server for gRPC Diff service
package diff

import (
	"cqfn.org/degitx/logging"

	"gitlab.com/gitlab-org/gitaly-proto/go/gitalypb"

	"google.golang.org/grpc/codes"
	"google.golang.org/grpc/status"
)

type server struct {
	log *logging.Logger
}

// NewServer creates new DiffServiceServer
func NewServer(log *logging.Logger) gitalypb.DiffServiceServer {
	return &server{
		log: log,
	}
}

func (server *server) CommitPatch(
	*gitalypb.CommitPatchRequest,
	gitalypb.DiffService_CommitPatchServer,
) error {
	server.log.Info("CommitPatch RPC was called")
	return status.Errorf(codes.Unimplemented, "method CommitPatch not implemented")
}

func (server *server) CommitDiff(
	*gitalypb.CommitDiffRequest,
	gitalypb.DiffService_CommitDiffServer,
) error {
	server.log.Info("CommitDiff RPC was called")
	return status.Errorf(codes.Unimplemented, "method CommitDiff not implemented")
}

func (server *server) CommitDelta(
	*gitalypb.CommitDeltaRequest,
	gitalypb.DiffService_CommitDeltaServer,
) error {
	server.log.Info("CommitDelta RPC was called")
	return status.Errorf(codes.Unimplemented, "method CommitDelta not implemented")
}

func (server *server) RawDiff(
	*gitalypb.RawDiffRequest,
	gitalypb.DiffService_RawDiffServer,
) error {
	server.log.Info("RawDiff RPC was called")
	return status.Errorf(codes.Unimplemented, "method RawDiff not implemented")
}

func (server *server) RawPatch(
	*gitalypb.RawPatchRequest,
	gitalypb.DiffService_RawPatchServer,
) error {
	server.log.Info("RawPatch RPC was called")
	return status.Errorf(codes.Unimplemented, "method RawPatch not implemented")
}

func (server *server) DiffStats(
	*gitalypb.DiffStatsRequest,
	gitalypb.DiffService_DiffStatsServer,
) error {
	server.log.Info("DiffStats RPC was called")
	return status.Errorf(codes.Unimplemented, "method DiffStats not implemented")
}
