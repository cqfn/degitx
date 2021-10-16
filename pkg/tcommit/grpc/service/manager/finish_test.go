// MIT License. Copyright (c) 2020 CQFN
// https://github.com/cqfn/degitx/blob/master/LICENSE

package manager

import (
	"fmt"

	"cqfn.org/degitx/pkg/tcommit"
	"cqfn.org/degitx/pkg/tcommit/grpc/marshall"
	"cqfn.org/degitx/pkg/tcommit/grpc/pb"
	"google.golang.org/grpc/codes"
	"google.golang.org/grpc/status"
)

func (s *ServiceSuite) finishRequest() *pb.FinishRequest {
	return &pb.FinishRequest{
		Meta:   &pb.Meta{Meta: "meta"},
		NodeId: "1.1",
	}
}

func (s *ServiceSuite) OnFinishReturn(req *pb.FinishRequest, result error) {
	meta, err := marshall.FromProtoMeta(req.Meta)
	s.Require().NoError(err)
	s.tm.On("Finish", tcommit.NodeID(req.NodeId), meta).Return(result)
}

func (s *ServiceSuite) TestService_Finish_internalError() {
	req := s.finishRequest()
	//nolint:goerr113 // Error for the test
	s.OnFinishReturn(req, fmt.Errorf("panic"))

	result, err := s.client.Finish(s.ctx, req)

	s.Equal(status.Code(err), codes.Internal)
	s.Nil(result)
	s.tm.AssertNumberOfCalls(s.T(), "Finish", 1)
}

func (s *ServiceSuite) TestService_Finish() {
	req := s.finishRequest()
	s.OnFinishReturn(req, nil)

	result, err := s.client.Finish(s.ctx, req)

	s.NoError(err)
	s.NotNil(result)
	s.tm.AssertNumberOfCalls(s.T(), "Finish", 1)
}
