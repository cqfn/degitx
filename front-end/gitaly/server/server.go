// MIT License. Copyright (c) 2020 CQFN
// https://github.com/cqfn/degitx/blob/master/LICENSE

// Package server provide interface to start and stop server
// that contains all gRPC service servers that are borrowed from gitaly.
package server

import (
	"context"
	"log"
	"net"

	"cqfn.org/degitx/discovery"
	"cqfn.org/degitx/front-end/gitaly/service/blob"
	"cqfn.org/degitx/front-end/gitaly/service/cleanup"
	"cqfn.org/degitx/front-end/gitaly/service/commit"
	"cqfn.org/degitx/front-end/gitaly/service/conflicts"
	"cqfn.org/degitx/front-end/gitaly/service/diff"
	"cqfn.org/degitx/front-end/gitaly/service/namespace"
	"cqfn.org/degitx/front-end/gitaly/service/objectpool"
	"cqfn.org/degitx/front-end/gitaly/service/operations"
	"cqfn.org/degitx/front-end/gitaly/service/ref"
	"cqfn.org/degitx/front-end/gitaly/service/remote"
	"cqfn.org/degitx/front-end/gitaly/service/repository"
	"cqfn.org/degitx/front-end/gitaly/service/server"
	"cqfn.org/degitx/front-end/gitaly/service/smarthttp"
	"cqfn.org/degitx/front-end/gitaly/service/ssh"
	"cqfn.org/degitx/front-end/gitaly/service/storage"
	"cqfn.org/degitx/front-end/gitaly/service/wiki"
	"cqfn.org/degitx/front-end/healthcheckstub"
	"cqfn.org/degitx/logging"
	"cqfn.org/degitx/version"

	"gitlab.com/gitlab-org/gitaly-proto/go/gitalypb"

	ma "github.com/multiformats/go-multiaddr"

	"google.golang.org/grpc"
	healthpb "google.golang.org/grpc/health/grpc_health_v1"
	"google.golang.org/grpc/reflection"
)

// Server interface
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
	/**
	 * @todo #74 Implement channels and goroutines
	 * Let's Move Serve and add GracefulStop in goroutines in all places around the project.
	 * To be able to start servers in goroutines,
	 * it's needed to add Channels and handle them via select in main.
	 */
	if err := grpcServer.Serve(l); err != nil {
		log.Printf("Front-end failed: %s", err)
	}
	log.Printf("Front-end started at %s", s.addr)
	return nil
}

// RegisterAll registers all Gitaly service servers
func RegisterAll(grpcServer *grpc.Server, logger *logging.Logger) {
	gitalypb.RegisterBlobServiceServer(grpcServer, blob.NewServer(logger))
	gitalypb.RegisterCleanupServiceServer(grpcServer, cleanup.NewServer(logger))
	gitalypb.RegisterCommitServiceServer(grpcServer, commit.NewServer(logger))
	gitalypb.RegisterDiffServiceServer(grpcServer, diff.NewServer(logger))
	gitalypb.RegisterNamespaceServiceServer(grpcServer, namespace.NewServer(logger))
	gitalypb.RegisterOperationServiceServer(grpcServer, operations.NewServer(logger))
	gitalypb.RegisterRefServiceServer(grpcServer, ref.NewServer(logger))
	gitalypb.RegisterRepositoryServiceServer(grpcServer, repository.NewServer(logger))
	gitalypb.RegisterSSHServiceServer(grpcServer, ssh.NewServer(logger))
	gitalypb.RegisterSmartHTTPServiceServer(grpcServer, smarthttp.NewServer(logger))
	gitalypb.RegisterWikiServiceServer(grpcServer, wiki.NewServer(logger))
	gitalypb.RegisterConflictsServiceServer(grpcServer, conflicts.NewServer(logger))
	gitalypb.RegisterRemoteServiceServer(grpcServer, remote.NewServer(logger))
	gitalypb.RegisterServerServiceServer(grpcServer, server.NewServer(logger, version.GetVersion()))
	gitalypb.RegisterStorageServiceServer(grpcServer, storage.NewServer(logger))
	gitalypb.RegisterObjectPoolServiceServer(grpcServer, objectpool.NewServer(logger))
	healthpb.RegisterHealthServer(grpcServer, healthcheckstub.NewServer(logger))
}
