// MIT License. Copyright (c) 2020 CQFN
// https://github.com/cqfn/degitx/blob/master/LICENSE

// Package objectpool contains server for gRPC ObjectPool service
package objectpool

import (
	"cqfn.org/degitx/logging"

	"gitlab.com/gitlab-org/gitaly-proto/go/gitalypb"

	"golang.org/x/net/context"
	"google.golang.org/grpc/codes"
	"google.golang.org/grpc/status"
)

type server struct {
	log *logging.Logger
}

// NewServer creates new ObjectPoolServiceServer
func NewServer(log *logging.Logger) gitalypb.ObjectPoolServiceServer {
	return &server{
		log: log,
	}
}

func (server *server) CreateObjectPool(
	context.Context,
	*gitalypb.CreateObjectPoolRequest,
) (*gitalypb.CreateObjectPoolResponse, error) {
	server.log.Info("CreateObjectPool RPC was called")
	return nil, status.Errorf(codes.Unimplemented, "method CreateObjectPool not implemented")
}

func (server *server) DeleteObjectPool(
	context.Context,
	*gitalypb.DeleteObjectPoolRequest,
) (*gitalypb.DeleteObjectPoolResponse, error) {
	server.log.Info("DeleteObjectPool RPC was called")
	return nil, status.Errorf(codes.Unimplemented, "method DeleteObjectPool not implemented")
}

func (server *server) LinkRepositoryToObjectPool(
	context.Context,
	*gitalypb.LinkRepositoryToObjectPoolRequest,
) (*gitalypb.LinkRepositoryToObjectPoolResponse, error) {
	server.log.Info("LinkRepositoryToObjectPool RPC was called")
	return nil, status.Errorf(codes.Unimplemented, "method LinkRepositoryToObjectPool not implemented")
}

func (server *server) UnlinkRepositoryFromObjectPool(
	context.Context,
	*gitalypb.UnlinkRepositoryFromObjectPoolRequest,
) (*gitalypb.UnlinkRepositoryFromObjectPoolResponse, error) {
	server.log.Info("UnlinkRepositoryFromObjectPool RPC was called")
	return nil, status.Errorf(codes.Unimplemented, "method UnlinkRepositoryFromObjectPool not implemented")
}

func (server *server) ReduplicateRepository(
	context.Context,
	*gitalypb.ReduplicateRepositoryRequest,
) (*gitalypb.ReduplicateRepositoryResponse, error) {
	server.log.Info("ReduplicateRepository RPC was called")
	return nil, status.Errorf(codes.Unimplemented, "method ReduplicateRepository not implemented")
}

func (server *server) DisconnectGitAlternates(
	context.Context,
	*gitalypb.DisconnectGitAlternatesRequest,
) (*gitalypb.DisconnectGitAlternatesResponse, error) {
	server.log.Info("DisconnectGitAlternates RPC was called")
	return nil, status.Errorf(codes.Unimplemented, "method DisconnectGitAlternates not implemented")
}

func (server *server) FetchIntoObjectPool(
	context.Context,
	*gitalypb.FetchIntoObjectPoolRequest,
) (*gitalypb.FetchIntoObjectPoolResponse, error) {
	server.log.Info("FetchIntoObjectPool RPC was called")
	return nil, status.Errorf(codes.Unimplemented, "method FetchIntoObjectPool not implemented")
}
