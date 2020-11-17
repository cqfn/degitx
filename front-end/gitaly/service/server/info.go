// MIT License. Copyright (c) 2020 CQFN
// https://github.com/cqfn/degitx/blob/master/LICENSE

package server

import (
	"gitlab.com/gitlab-org/gitaly-proto/go/gitalypb"

	"golang.org/x/net/context"
)

func (server *server) ServerInfo(
	context.Context,
	*gitalypb.ServerInfoRequest,
) (*gitalypb.ServerInfoResponse, error) {
	server.log.Info("ServerInfo RPC was called")
	return &gitalypb.ServerInfoResponse{
		ServerVersion:   server.version,
		GitVersion:      "not-implemented",
		StorageStatuses: []*gitalypb.ServerInfoResponse_StorageStatus{},
	}, nil
}
