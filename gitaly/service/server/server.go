// MIT License. Copyright (c) 2020 CQFN
// https://github.com/cqfn/degitx/blob/master/LICENSE

// Package server contains server for gRPC server service
package server

import (
	"fmt"

	"golang.org/x/net/context"
	"google.golang.org/grpc/codes"
	"google.golang.org/grpc/status"

	"cqfn.org/degitx/logging"
	"cqfn.org/degitx/proto/go/degitxpb"
)

type server struct {
	version string
	log     *logging.Logger
}

func NewServer(log *logging.Logger, degitxVersion string) degitxpb.ServerServiceServer {
	return &server{
		version: fmt.Sprintf("degitx-v%s (gitaly-v1.27.1)", degitxVersion),
		log:     log,
	}
}

// Doesn't exist in v1.27.1
func (server *server) DiskStatistics(
	context.Context,
	*degitxpb.DiskStatisticsRequest,
) (*degitxpb.DiskStatisticsResponse, error) {
	server.log.Error("DiskStatistics RPC was called but doesn't exist in gitaly v1.27.1")
	return nil, status.Errorf(codes.Unimplemented, "method DiskStatistics not implemented")
}
