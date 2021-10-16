// MIT License. Copyright (c) 2020 CQFN
// https://github.com/cqfn/degitx/blob/master/LICENSE

//nolint:dupl // Due to lack of logic of the commit method, the test code similar to the abort
package resource

import (
	"fmt"

	"cqfn.org/degitx/pkg/tcommit/grpc/pb"
	"google.golang.org/grpc/codes"
	"google.golang.org/grpc/status"
)

func (s *ServiceSuite) commitRequest() *pb.CommitRequest {
	return &pb.CommitRequest{}
}

func (s *ServiceSuite) OnCommitReturn(result error) {
	s.rm.On("Commit").Return(result)
}

func (s *ServiceSuite) TestService_Commit_internalError() {
	req := s.commitRequest()
	//nolint:goerr113 // Error for the test
	s.OnCommitReturn(fmt.Errorf("panic"))

	result, err := s.svc.Commit(s.ctx, req)

	s.Require().Equal(status.Code(err), codes.Internal)
	s.Contains(err.Error(), "panic")
	s.Nil(result)
	s.rm.AssertNumberOfCalls(s.T(), "Commit", 1)
}

func (s *ServiceSuite) TestService_Commit() {
	req := s.commitRequest()
	s.OnCommitReturn(nil)

	result, err := s.svc.Commit(s.ctx, req)

	s.NoError(err)
	s.NotNil(result)
	s.rm.AssertNumberOfCalls(s.T(), "Commit", 1)
}
