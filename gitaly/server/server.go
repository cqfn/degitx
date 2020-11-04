// MIT License. Copyright (c) 2020 CQFN
// https://github.com/cqfn/degitx/blob/master/LICENSE

// Package server provide interface to start and stop server
// that contains all gRPC service servers that are borrowed from gitaly.
package server

import (
	"context"
	"net"

	"cqfn.org/degitx/discovery"
	"cqfn.org/degitx/gitaly/service/server"
	"cqfn.org/degitx/locators"
	"cqfn.org/degitx/logging"
	"cqfn.org/degitx/proto/go/degitxpb"
	"cqfn.org/degitx/version"

	"google.golang.org/grpc"
	"google.golang.org/grpc/reflection"
)

type Server interface {
	Start(context.Context, *locators.Node) error
	Stop()
}

type GrpcServer struct {
	server *grpc.Server
}

func (s *GrpcServer) Start(_ context.Context, node *locators.Node) error {
	grpcServer := grpc.NewServer()
	logger, err := logging.NewLogger("gRPC")
	if err != nil {
		return err
	}

	degitxpb.RegisterBlobServiceServer(grpcServer, &degitxpb.UnimplementedBlobServiceServer{})
	degitxpb.RegisterCleanupServiceServer(grpcServer, &degitxpb.UnimplementedCleanupServiceServer{})
	degitxpb.RegisterCommitServiceServer(grpcServer, &degitxpb.UnimplementedCommitServiceServer{})
	degitxpb.RegisterDiffServiceServer(grpcServer, &degitxpb.UnimplementedDiffServiceServer{})
	degitxpb.RegisterNamespaceServiceServer(grpcServer, &degitxpb.UnimplementedNamespaceServiceServer{})
	degitxpb.RegisterOperationServiceServer(grpcServer, &degitxpb.UnimplementedOperationServiceServer{})
	degitxpb.RegisterRefServiceServer(grpcServer, &degitxpb.UnimplementedRefServiceServer{})
	degitxpb.RegisterRepositoryServiceServer(grpcServer, &degitxpb.UnimplementedRepositoryServiceServer{})
	degitxpb.RegisterSSHServiceServer(grpcServer, &degitxpb.UnimplementedSSHServiceServer{})
	degitxpb.RegisterSmartHTTPServiceServer(grpcServer, &degitxpb.UnimplementedSmartHTTPServiceServer{})
	degitxpb.RegisterWikiServiceServer(grpcServer, &degitxpb.UnimplementedWikiServiceServer{})
	degitxpb.RegisterConflictsServiceServer(grpcServer, &degitxpb.UnimplementedConflictsServiceServer{})
	degitxpb.RegisterRemoteServiceServer(grpcServer, &degitxpb.UnimplementedRemoteServiceServer{})
	degitxpb.RegisterServerServiceServer(grpcServer, server.NewServer(logger, version.GetVersion()))
	degitxpb.RegisterObjectPoolServiceServer(grpcServer, &degitxpb.UnimplementedObjectPoolServiceServer{})
	degitxpb.RegisterHookServiceServer(grpcServer, &degitxpb.UnimplementedHookServiceServer{})
	degitxpb.RegisterInternalGitalyServer(grpcServer, &degitxpb.UnimplementedInternalGitalyServer{})

	reflection.Register(grpcServer)

	addr := new(discovery.MaNetworkAddr)
	if err := addr.Parse(node.Addr); err != nil {
		panic(err)
	}
	l, err := net.Listen("tcp", addr.String())
	if err != nil {
		return err
	}

	if err := grpcServer.Serve(l); err != nil {
		return err
	}
	s.server = grpcServer
	return nil
}

func (s *GrpcServer) Stop() {
	if s.server != nil {
		s.server.Stop()
	}
}
