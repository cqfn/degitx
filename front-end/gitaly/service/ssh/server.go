// MIT License. Copyright (c) 2020 CQFN
// https://github.com/cqfn/degitx/blob/master/LICENSE

// Package ssh contains server for gRPC SSH service
package ssh

import (
	"cqfn.org/degitx/logging"

	"gitlab.com/gitlab-org/gitaly-proto/go/gitalypb"

	"google.golang.org/grpc/codes"
	"google.golang.org/grpc/status"
)

type server struct {
	log *logging.Logger
}

func NewServer(log *logging.Logger) gitalypb.SSHServiceServer {
	return &server{
		log: log,
	}
}

func (server *server) SSHUploadPack(gitalypb.SSHService_SSHUploadPackServer) error {
	server.log.Info("SSHUploadPack RPC was called")
	return status.Errorf(codes.Unimplemented, "method SSHUploadPack not implemented")
}

func (server *server) SSHReceivePack(gitalypb.SSHService_SSHReceivePackServer) error {
	server.log.Info("SSHReceivePack RPC was called")
	return status.Errorf(codes.Unimplemented, "method SSHReceivePack not implemented")
}

func (server *server) SSHUploadArchive(gitalypb.SSHService_SSHUploadArchiveServer) error {
	server.log.Info("SSHUploadArchive RPC was called")
	return status.Errorf(codes.Unimplemented, "method SSHUploadArchive not implemented")
}
