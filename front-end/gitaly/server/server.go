// MIT License. Copyright (c) 2020 CQFN
// https://github.com/cqfn/degitx/blob/master/LICENSE

// Package server provide interface to start and stop server
// that contains all gRPC service servers that are borrowed from gitaly.
package server

import (
	"context"
	"log"
	"net"

	ma "github.com/multiformats/go-multiaddr"

	"cqfn.org/degitx/discovery"
	"cqfn.org/degitx/front-end/gitaly/service/server"
	"cqfn.org/degitx/logging"
	"cqfn.org/degitx/proto/go/degitxpb"
	"cqfn.org/degitx/version"

	"google.golang.org/grpc"
	"google.golang.org/grpc/reflection"
)

type Server interface {
	Start(context.Context) error
}

type grpcServer struct {
	addr net.Addr
}

// NewGrpcServer for Gitaly gRPC
func NewGrpcServer(maddr ma.Multiaddr) (Server, error) {
	addr := new(discovery.MaNetworkAddr)
	if err := addr.Parse(maddr); err != nil { //nolint:dupl // just parsing an address
		return nil, err
	}
	srv := new(grpcServer)
	srv.addr = addr
	return srv, nil
}

func (s *grpcServer) Start(ctx context.Context) error {
	grpcServer := grpc.NewServer()
	logger, err := logging.NewLogger("Gitaly")
	if err != nil {
		return err
	}

	RegisterAll(grpcServer, logger)
	reflection.Register(grpcServer)
	l, err := net.Listen("tcp", s.addr.String())
	if err != nil {
		return err
	}

	go func() {
		if err := grpcServer.Serve(l); err != nil {
			log.Printf("Front-end failed: %s", err)
		}
	}()

	go func() {
		<-ctx.Done()
		grpcServer.GracefulStop()
	}()
	log.Printf("Front-end started at %s", s.addr)
	return nil
}

// RegisterAll registers all Gitaly service servers
func RegisterAll(grpcServer *grpc.Server, logger *logging.Logger) {
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
}
