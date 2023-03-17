// MIT License. Copyright (c) 2020 CQFN
// https://github.com/cqfn/degitx/blob/master/LICENSE

// Package manager implements transaction protocols as a gRPC service
package manager

import (
	"cqfn.org/degitx/pkg/tcommit"
	"cqfn.org/degitx/pkg/tcommit/grpc/pb"
)

// Service implements tcommit.Manager interface as the gRPC service
type Service struct {
	tm tcommit.Manager

	*pb.UnimplementedManagerServiceServer
}

// NewService with a given tcommit.Manager
func NewService(tm tcommit.Manager) *Service {
	return &Service{tm: tm}
}
