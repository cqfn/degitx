// MIT License. Copyright (c) 2020 CQFN
// https://github.com/cqfn/degitx/blob/master/LICENSE

// Package cleanup contains server for gRPC Cleanup service
package cleanup

import (
	"cqfn.org/degitx/internal/logging"

	"gitlab.com/gitlab-org/gitaly-proto/go/gitalypb"

	context "golang.org/x/net/context"
	"google.golang.org/grpc/codes"
	"google.golang.org/grpc/status"
)

type server struct {
	log *logging.Logger
}

// NewServer creates new CleanupServiceServer
func NewServer(log *logging.Logger) gitalypb.CleanupServiceServer {
	return &server{
		log: log,
	}
}

func (server *server) ApplyBfgObjectMapStream(gitalypb.CleanupService_ApplyBfgObjectMapStreamServer) error {
	server.log.Info("ApplyBfgObjectMapStream RPC was called")
	return status.Errorf(codes.Unimplemented, "method ApplyBfgObjectMapStream not implemented")
}

func (server *server) ApplyBfgObjectMap(gitalypb.CleanupService_ApplyBfgObjectMapServer) error {
	server.log.Info("ApplyBfgObjectMap RPC was called")
	return status.Errorf(codes.Unimplemented, "method ApplyBfgObjectMap not implemented")
}

func (server *server) CloseSession(
	context.Context,
	*gitalypb.CloseSessionRequest,
) (*gitalypb.CloseSessionResponse, error) {
	server.log.Info("CloseSession RPC was called")
	return nil, status.Errorf(codes.Unimplemented, "method CloseSession not implemented")
}
