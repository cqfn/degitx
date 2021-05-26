// MIT License. Copyright (c) 2020 CQFN
// https://github.com/cqfn/degitx/blob/master/LICENSE

// Package server contains server for gRPC server service
package server

import (
	"fmt"

	"cqfn.org/degitx/internal/logging"

	"gitlab.com/gitlab-org/gitaly-proto/go/gitalypb"
)

type server struct {
	version string
	log     *logging.Logger
}

// NewServer creates new ServerServiceServer
func NewServer(log *logging.Logger, degitxVersion string) gitalypb.ServerServiceServer {
	return &server{
		version: fmt.Sprintf("degitx-v%s (gitaly-v1.27.1)", degitxVersion),
		log:     log,
	}
}
