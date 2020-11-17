// MIT License. Copyright (c) 2020 CQFN
// https://github.com/cqfn/degitx/blob/master/LICENSE

// Package wiki contains server for gRPC Wiki service
package wiki

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

func NewServer(log *logging.Logger) gitalypb.WikiServiceServer {
	return &server{
		log: log,
	}
}

func (server *server) WikiGetFormattedData(
	*gitalypb.WikiGetFormattedDataRequest,
	gitalypb.WikiService_WikiGetFormattedDataServer,
) error {
	server.log.Info("WikiGetFormattedData RPC was called")
	return status.Errorf(codes.Unimplemented, "method WikiGetFormattedData not implemented")
}

func (server *server) WikiGetPageVersions(
	*gitalypb.WikiGetPageVersionsRequest,
	gitalypb.WikiService_WikiGetPageVersionsServer,
) error {
	server.log.Info("WikiGetPageVersions RPC was called")
	return status.Errorf(codes.Unimplemented, "method WikiGetPageVersions not implemented")
}

func (server *server) WikiWritePage(gitalypb.WikiService_WikiWritePageServer) error {
	server.log.Info("WikiWritePage RPC was called")
	return status.Errorf(codes.Unimplemented, "method WikiWritePage not implemented")
}

func (server *server) WikiUpdatePage(gitalypb.WikiService_WikiUpdatePageServer) error {
	server.log.Info("WikiUpdatePage RPC was called")
	return status.Errorf(codes.Unimplemented, "method WikiUpdatePage not implemented")
}

func (server *server) WikiDeletePage(
	context.Context,
	*gitalypb.WikiDeletePageRequest,
) (*gitalypb.WikiDeletePageResponse, error) {
	server.log.Info("WikiDeletePage RPC was called")
	return nil, status.Errorf(codes.Unimplemented, "method WikiDeletePage not implemented")
}

func (server *server) WikiFindPage(
	*gitalypb.WikiFindPageRequest,
	gitalypb.WikiService_WikiFindPageServer,
) error {
	server.log.Info("WikiFindPage RPC was called")
	return status.Errorf(codes.Unimplemented, "method WikiFindPage not implemented")
}

func (server *server) WikiFindFile(
	*gitalypb.WikiFindFileRequest,
	gitalypb.WikiService_WikiFindFileServer,
) error {
	server.log.Info("WikiFindFile RPC was called")
	return status.Errorf(codes.Unimplemented, "method WikiFindFile not implemented")
}

func (server *server) WikiGetAllPages(
	*gitalypb.WikiGetAllPagesRequest,
	gitalypb.WikiService_WikiGetAllPagesServer,
) error {
	server.log.Info("WikiGetAllPages RPC was called")
	return status.Errorf(codes.Unimplemented, "method WikiGetAllPages not implemented")
}

func (server *server) WikiListPages(
	*gitalypb.WikiListPagesRequest,
	gitalypb.WikiService_WikiListPagesServer,
) error {
	server.log.Info("WikiListPages RPC was called")
	return status.Errorf(codes.Unimplemented, "method WikiListPages not implemented")
}
