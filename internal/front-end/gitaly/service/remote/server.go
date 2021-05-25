// MIT License. Copyright (c) 2020 CQFN
// https://github.com/cqfn/degitx/blob/master/LICENSE

// Package remote contains server for gRPC Remote service
package remote

import (
	"cqfn.org/degitx/internal/logging"

	"gitlab.com/gitlab-org/gitaly-proto/go/gitalypb"

	"golang.org/x/net/context"
	"google.golang.org/grpc/codes"
	"google.golang.org/grpc/status"
)

type server struct {
	log *logging.Logger
}

// NewServer creates new RemoteServiceServer
func NewServer(log *logging.Logger) gitalypb.RemoteServiceServer {
	return &server{
		log: log,
	}
}

func (server *server) AddRemote(
	context.Context,
	*gitalypb.AddRemoteRequest,
) (*gitalypb.AddRemoteResponse, error) {
	server.log.Info("AddRemote RPC was called")
	return nil, status.Errorf(codes.Unimplemented, "method AddRemote not implemented")
}

func (server *server) FetchInternalRemote(
	context.Context,
	*gitalypb.FetchInternalRemoteRequest,
) (*gitalypb.FetchInternalRemoteResponse, error) {
	server.log.Info("FetchInternalRemote RPC was called")
	return nil, status.Errorf(codes.Unimplemented, "method FetchInternalRemote not implemented")
}

func (server *server) RemoveRemote(
	context.Context,
	*gitalypb.RemoveRemoteRequest,
) (*gitalypb.RemoveRemoteResponse, error) {
	server.log.Info("RemoveRemote RPC was called")
	return nil, status.Errorf(codes.Unimplemented, "method RemoveRemote not implemented")
}

func (server *server) UpdateRemoteMirror(gitalypb.RemoteService_UpdateRemoteMirrorServer) error {
	server.log.Info("UpdateRemoteMirror RPC was called")
	return status.Errorf(codes.Unimplemented, "method UpdateRemoteMirror not implemented")
}

func (server *server) FindRemoteRepository(
	context.Context,
	*gitalypb.FindRemoteRepositoryRequest,
) (*gitalypb.FindRemoteRepositoryResponse, error) {
	server.log.Info("FindRemoteRepository RPC was called")
	return nil, status.Errorf(codes.Unimplemented, "method FindRemoteRepository not implemented")
}

func (server *server) FindRemoteRootRef(
	context.Context,
	*gitalypb.FindRemoteRootRefRequest,
) (*gitalypb.FindRemoteRootRefResponse, error) {
	server.log.Info("FindRemoteRootRef RPC was called")
	return nil, status.Errorf(codes.Unimplemented, "method FindRemoteRootRef not implemented")
}

func (server *server) ListRemotes(
	*gitalypb.ListRemotesRequest,
	gitalypb.RemoteService_ListRemotesServer,
) error {
	server.log.Info("ListRemotes RPC was called")
	return status.Errorf(codes.Unimplemented, "method ListRemotes not implemented")
}
