// MIT License. Copyright (c) 2020 CQFN
// https://github.com/cqfn/degitx/blob/master/LICENSE

//nolint:dupl // Due to lack of logic of the abort method, the test code similar to the commit
package resource

import (
	"fmt"

	"cqfn.org/degitx/pkg/tcommit/grpc/pb"
	"google.golang.org/grpc/codes"
	"google.golang.org/grpc/status"
)

func (s *ServiceSuite) abortRequest() *pb.AbortRequest {
	return &pb.AbortRequest{}
}

func (s *ServiceSuite) OnAbortReturn(result error) {
	s.rm.On("Abort").Return(result)
}

func (s *ServiceSuite) TestService_Abort_internalError() {
	req := s.abortRequest()
	//nolint:goerr113 // Error for the test
	s.OnAbortReturn(fmt.Errorf("panic"))

	result, err := s.svc.Abort(s.ctx, req)

	s.Require().Equal(status.Code(err), codes.Internal)
	s.Contains(err.Error(), "panic")
	s.Nil(result)
	s.rm.AssertNumberOfCalls(s.T(), "Abort", 1)
}

func (s *ServiceSuite) TestService_Abort() {
	req := s.abortRequest()
	s.OnAbortReturn(nil)

	result, err := s.svc.Abort(s.ctx, req)

	s.NoError(err)
	s.NotNil(result)
	s.rm.AssertNumberOfCalls(s.T(), "Abort", 1)
}
