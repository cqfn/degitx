// MIT License. Copyright (c) 2020 CQFN
// https://github.com/cqfn/degitx/blob/master/LICENSE

// Package conflicts contains server for gRPC Conflicts service
package conflicts

import (
	"cqfn.org/degitx/logging"

	"gitlab.com/gitlab-org/gitaly-proto/go/gitalypb"

	"google.golang.org/grpc/codes"
	"google.golang.org/grpc/status"
)

type server struct {
	log *logging.Logger
}

// NewServer creates new ConflictsServiceServer
func NewServer(log *logging.Logger) gitalypb.ConflictsServiceServer {
	return &server{
		log: log,
	}
}

func (server *server) ListConflictFiles(
	*gitalypb.ListConflictFilesRequest,
	gitalypb.ConflictsService_ListConflictFilesServer,
) error {
	server.log.Info("ListConflictFiles RPC was called")
	return status.Errorf(codes.Unimplemented, "method ListConflictFiles not implemented")
}

func (server *server) ResolveConflicts(gitalypb.ConflictsService_ResolveConflictsServer) error {
	server.log.Info("ResolveConflicts RPC was called")
	return status.Errorf(codes.Unimplemented, "method ResolveConflicts not implemented")
}
