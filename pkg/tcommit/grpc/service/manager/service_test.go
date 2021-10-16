// MIT License. Copyright (c) 2020 CQFN
// https://github.com/cqfn/degitx/blob/master/LICENSE

package manager

import (
	"context"
	"testing"

	"cqfn.org/degitx/pkg/tcommit"
	"cqfn.org/degitx/pkg/tcommit/grpc/pb"
	"cqfn.org/degitx/pkg/tcommit/grpc/service/test"
	"github.com/stretchr/testify/mock"
	"github.com/stretchr/testify/suite"
	"google.golang.org/grpc"
)

type MockManager struct {
	mock.Mock
}

func (m *MockManager) Begin(_ context.Context, votes tcommit.Votes, meta tcommit.Meta) error {
	args := m.Called(votes, meta)
	return args.Error(0)
}

func (m *MockManager) Finish(_ context.Context, id tcommit.NodeID, meta tcommit.Meta) error {
	args := m.Called(id, meta)
	return args.Error(0)
}

type ServiceSuite struct {
	suite.Suite

	ctx    context.Context
	conn   *grpc.ClientConn
	srv    *grpc.Server
	svc    *Service
	client pb.ManagerServiceClient
	tm     *MockManager
}

func TestServiceSuite(t *testing.T) {
	suite.Run(t, &ServiceSuite{})
}

func (s *ServiceSuite) SetupSuite() {
	s.ctx = context.Background()
	s.svc = NewService(nil)
	s.srv, s.conn = test.StartServer(s.ctx, func(srv *grpc.Server) {
		pb.RegisterManagerServiceServer(srv, s.svc)
	})
	s.client = pb.NewManagerServiceClient(s.conn)
}

func (s *ServiceSuite) SetupTest() {
	s.tm = &MockManager{}
	s.svc.tm = s.tm
}

func (s *ServiceSuite) TeardownSuite() {
	s.NoError(s.conn.Close())
	s.srv.Stop()
}
