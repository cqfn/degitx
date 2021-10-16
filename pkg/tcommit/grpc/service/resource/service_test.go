// MIT License. Copyright (c) 2020 CQFN
// https://github.com/cqfn/degitx/blob/master/LICENSE

package resource

import (
	"context"
	"testing"

	"cqfn.org/degitx/pkg/tcommit/grpc/pb"
	"cqfn.org/degitx/pkg/tcommit/grpc/service/test"
	"github.com/stretchr/testify/mock"
	"github.com/stretchr/testify/suite"
	"google.golang.org/grpc"
)

type MockResource struct {
	mock.Mock
}

func (m *MockResource) Commit(_ context.Context) error {
	args := m.Called()
	return args.Error(0)
}

func (m *MockResource) Abort(_ context.Context) error {
	args := m.Called()
	return args.Error(0)
}

type ServiceSuite struct {
	suite.Suite

	ctx    context.Context
	conn   *grpc.ClientConn
	srv    *grpc.Server
	svc    *Service
	client pb.ResourceServiceClient
	rm     *MockResource
}

func TestServiceSuite(t *testing.T) {
	suite.Run(t, &ServiceSuite{})
}

func (s *ServiceSuite) SetupSuite() {
	s.ctx = context.Background()
	s.svc = NewService(nil)
	s.srv, s.conn = test.StartServer(s.ctx, func(srv *grpc.Server) {
		pb.RegisterResourceServiceServer(srv, s.svc)
	})
	s.client = pb.NewResourceServiceClient(s.conn)
}

func (s *ServiceSuite) SetupTest() {
	s.rm = &MockResource{}
	s.svc.rm = s.rm
}

func (s *ServiceSuite) TeardownSuite() {
	s.NoError(s.conn.Close())
	s.srv.Stop()
}
