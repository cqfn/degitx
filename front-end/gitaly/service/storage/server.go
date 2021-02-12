// MIT License. Copyright (c) 2020 CQFN
// https://github.com/cqfn/degitx/blob/master/LICENSE

// Package storage contains server for gRPC Storage service
package storage

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

// NewServer creates new StorageServiceServer
func NewServer(log *logging.Logger) gitalypb.StorageServiceServer {
	return &server{
		log: log,
	}
}

func (server *server) ListDirectories(
	*gitalypb.ListDirectoriesRequest,
	gitalypb.StorageService_ListDirectoriesServer,
) error {
	server.log.Info("ListDirectories RPC was called")
	return status.Errorf(codes.Unimplemented, "method ListDirectories not implemented")
}

func (server *server) DeleteAllRepositories(
	context.Context,
	*gitalypb.DeleteAllRepositoriesRequest,
) (*gitalypb.DeleteAllRepositoriesResponse, error) {
	server.log.Info("DeleteAllRepositories RPC was called")
	return nil, status.Errorf(codes.Unimplemented, "method DeleteAllRepositories not implemented")
}
