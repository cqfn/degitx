// MIT License. Copyright (c) 2020 CQFN
// https://github.com/cqfn/degitx/blob/master/LICENSE

// Package degitx provide a degitx server start point.
package degitx

import (
	"log"
	"net"

	"google.golang.org/grpc"
	"google.golang.org/grpc/reflection"

	"org.cqfn/degitx/proto/go/degitxpb"
)

func Start() {
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

	l, err := net.Listen("tcp", ":8080") //nolint:gosec // It's only a stub
	if err != nil {
		log.Fatal(err)
	}

	if err := grpcServer.Serve(l); err != nil {
		log.Fatal(err)
	}
}
