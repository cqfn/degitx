// MIT License. Copyright (c) 2020 CQFN
// https://github.com/cqfn/degitx/blob/master/LICENSE

package server

import (
	"cqfn.org/degitx/proto/go/degitxpb"

	"golang.org/x/net/context"
)

func (server *server) ServerInfo(
	context.Context,
	*degitxpb.ServerInfoRequest,
) (*degitxpb.ServerInfoResponse, error) {
	server.log.Info("ServerInfo RPC was called")
	return &degitxpb.ServerInfoResponse{
		ServerVersion:   server.version,
		GitVersion:      "not-implemented",
		StorageStatuses: []*degitxpb.ServerInfoResponse_StorageStatus{},
	}, nil
}
