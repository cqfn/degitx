// MIT License. Copyright (c) 2020 CQFN
// https://github.com/cqfn/degitx/blob/master/LICENSE

// Package grpc provides gRPC clients and servers for discovery protocol
package grpc

import (
	"cqfn.org/degitx/internal/discovery/grpc/pb"
	"google.golang.org/grpc"
)

type discoveryService struct {
	pb.UnimplementedDiscoveryServiceServer
}

// NewService creates gRPC seed service
func NewService(server *grpc.Server) pb.DiscoveryServiceServer {
	return &discoveryService{}
}
