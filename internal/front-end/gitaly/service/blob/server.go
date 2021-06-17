// MIT License. Copyright (c) 2020 CQFN
// https://github.com/cqfn/degitx/blob/master/LICENSE

// Package blob contains server for gRPC Blob service
package blob

import (
	"cqfn.org/degitx/internal/logging"

	"gitlab.com/gitlab-org/gitaly-proto/go/gitalypb"

	"google.golang.org/grpc/codes"
	"google.golang.org/grpc/status"
)

type server struct {
	log *logging.Logger
}

// NewServer creates new BlobServiceServer
func NewServer(log *logging.Logger) gitalypb.BlobServiceServer {
	return &server{
		log: log,
	}
}

func (server *server) GetBlob(
	*gitalypb.GetBlobRequest,
	gitalypb.BlobService_GetBlobServer,
) error {
	server.log.Info("GetBlob RPC was called")
	return status.Errorf(codes.Unimplemented, "method GetBlob not implemented")
}

func (server *server) GetBlobs(
	*gitalypb.GetBlobsRequest,
	gitalypb.BlobService_GetBlobsServer,
) error {
	server.log.Info("GetBlobs RPC was called")
	return status.Errorf(codes.Unimplemented, "method GetBlobs not implemented")
}

func (server *server) GetLFSPointers(
	*gitalypb.GetLFSPointersRequest,
	gitalypb.BlobService_GetLFSPointersServer,
) error {
	server.log.Info("GetLFSPointers RPC was called")
	return status.Errorf(codes.Unimplemented, "method GetLFSPointers not implemented")
}

func (server *server) GetNewLFSPointers(
	*gitalypb.GetNewLFSPointersRequest,
	gitalypb.BlobService_GetNewLFSPointersServer,
) error {
	server.log.Info("GetLFSPointers RPC was called")
	return status.Errorf(codes.Unimplemented, "method GetNewLFSPointers not implemented")
}

func (server *server) GetAllLFSPointers(
	*gitalypb.GetAllLFSPointersRequest,
	gitalypb.BlobService_GetAllLFSPointersServer,
) error {
	server.log.Info("GetAllLFSPointers RPC was called")
	return status.Errorf(codes.Unimplemented, "method GetAllLFSPointers not implemented")
}
