// MIT License. Copyright (c) 2020 CQFN
// https://github.com/cqfn/degitx/blob/master/LICENSE

// Package smarthttp contains server for gRPC SmartHTTP service
package smarthttp

import (
	"cqfn.org/degitx/logging"

	"gitlab.com/gitlab-org/gitaly-proto/go/gitalypb"

	"google.golang.org/grpc/codes"
	"google.golang.org/grpc/status"
)

type server struct {
	log *logging.Logger
}

// NewServer creates new SmartHTTPServiceServer
func NewServer(log *logging.Logger) gitalypb.SmartHTTPServiceServer {
	return &server{
		log: log,
	}
}

func (server *server) InfoRefsUploadPack(
	*gitalypb.InfoRefsRequest,
	gitalypb.SmartHTTPService_InfoRefsUploadPackServer,
) error {
	server.log.Info("InfoRefsUploadPack RPC was called")
	return status.Errorf(codes.Unimplemented, "method InfoRefsUploadPack not implemented")
}

func (server *server) InfoRefsReceivePack(
	*gitalypb.InfoRefsRequest,
	gitalypb.SmartHTTPService_InfoRefsReceivePackServer,
) error {
	server.log.Info("InfoRefsReceivePack RPC was called")
	return status.Errorf(codes.Unimplemented, "method InfoRefsReceivePack not implemented")
}

func (server *server) PostUploadPack(gitalypb.SmartHTTPService_PostUploadPackServer) error {
	server.log.Info("PostUploadPack RPC was called")
	return status.Errorf(codes.Unimplemented, "method PostUploadPack not implemented")
}

func (server *server) PostReceivePack(gitalypb.SmartHTTPService_PostReceivePackServer) error {
	server.log.Info("PostReceivePack RPC was called")
	return status.Errorf(codes.Unimplemented, "method PostReceivePack not implemented")
}
