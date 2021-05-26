// MIT License. Copyright (c) 2020 CQFN
// https://github.com/cqfn/degitx/blob/master/LICENSE

// Package namespace contains server for gRPC Namespace service
package namespace

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

// NewServer creates new NamespaceServiceServer
func NewServer(log *logging.Logger) gitalypb.NamespaceServiceServer {
	return &server{
		log: log,
	}
}

func (server *server) AddNamespace(
	context.Context,
	*gitalypb.AddNamespaceRequest,
) (*gitalypb.AddNamespaceResponse, error) {
	server.log.Info("AddNamespace RPC was called")
	return nil, status.Errorf(codes.Unimplemented, "method AddNamespace not implemented")
}

func (server *server) RemoveNamespace(
	context.Context,
	*gitalypb.RemoveNamespaceRequest,
) (*gitalypb.RemoveNamespaceResponse, error) {
	server.log.Info("RemoveNamespace RPC was called")
	return nil, status.Errorf(codes.Unimplemented, "method RemoveNamespace not implemented")
}

func (server *server) RenameNamespace(
	context.Context,
	*gitalypb.RenameNamespaceRequest,
) (*gitalypb.RenameNamespaceResponse, error) {
	server.log.Info("RenameNamespace RPC was called")
	return nil, status.Errorf(codes.Unimplemented, "method RenameNamespace not implemented")
}

func (server *server) NamespaceExists(
	context.Context,
	*gitalypb.NamespaceExistsRequest,
) (*gitalypb.NamespaceExistsResponse, error) {
	server.log.Info("NamespaceExists RPC was called")
	return nil, status.Errorf(codes.Unimplemented, "method NamespaceExists not implemented")
}
