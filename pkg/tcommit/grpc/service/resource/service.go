// MIT License. Copyright (c) 2020 CQFN
// https://github.com/cqfn/degitx/blob/master/LICENSE

// Package resource implements transaction protocols as a gRPC service
package resource

import (
	"cqfn.org/degitx/pkg/tcommit"
	"cqfn.org/degitx/pkg/tcommit/grpc/pb"
)

// Service implements tcommit.Resource interface as the gRPC service
type Service struct {
	rm tcommit.Resource

	*pb.UnimplementedResourceServiceServer
}

// NewService with a given tcommit.Resource
func NewService(rm tcommit.Resource) *Service {
	return &Service{rm: rm}
}
