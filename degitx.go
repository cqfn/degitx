// MIT License. Copyright (c) 2020 CQFN
// https://github.com/cqfn/degitx/blob/master/LICENSE

// Package degitx provide a degitx server start point.
package degitx

import (
	"context"
	"log"
	"net"

	"cqfn.org/degitx/discovery"
	"cqfn.org/degitx/locators"
	"cqfn.org/degitx/proto/go/degitxpb"
	"google.golang.org/grpc"
	"google.golang.org/grpc/reflection"
)

// Start DeGitX node or return error
func Start(ctx context.Context, node *locators.Node,
	disc discovery.Service) error {
	log.Printf("Starting %s", node)

	if err := disc.Start(ctx); err != nil {
		return err
	}

	grpcServer := grpc.NewServer()

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
	degitxpb.RegisterServerServiceServer(grpcServer, &degitxpb.UnimplementedServerServiceServer{})
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
	return nil
}
