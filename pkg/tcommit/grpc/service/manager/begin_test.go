// MIT License. Copyright (c) 2020 CQFN
// https://github.com/cqfn/degitx/blob/master/LICENSE

package manager

import (
	"fmt"

	"cqfn.org/degitx/pkg/tcommit/grpc/marshall"
	"cqfn.org/degitx/pkg/tcommit/grpc/pb"
	"google.golang.org/grpc/codes"
	"google.golang.org/grpc/status"
)

func (s *ServiceSuite) beginRequest() *pb.BeginRequest {
	return &pb.BeginRequest{
		Meta: &pb.Meta{Meta: "meta"},
		Votes: &pb.Votes{
			Votes: map[string]*pb.Vote{
				"1.1": {Vote: 0},
				"1.2": {Vote: 1},
				"1.3": {Vote: 2},
			},
		},
	}
}

func (s *ServiceSuite) OnBeginReturn(req *pb.BeginRequest, result error) {
	votes, err := marshall.FromProtoVotes(req.Votes)
	s.Require().NoError(err)
	meta, err := marshall.FromProtoMeta(req.Meta)
	s.Require().NoError(err)
	s.tm.On("Begin", votes, meta).Return(result)
}

func (s *ServiceSuite) TestService_Begin_votesMissed() {
	req := s.beginRequest()
	req.Votes = nil

	result, err := s.client.Begin(s.ctx, req)

	s.Equal(status.Code(err), codes.InvalidArgument)
	s.Nil(result)
	s.tm.AssertNumberOfCalls(s.T(), "Begin", 0)
}

func (s *ServiceSuite) TestService_Begin_internalError() {
	req := s.beginRequest()
	//nolint:goerr113 // Error for the test
	s.OnBeginReturn(req, fmt.Errorf("panic"))

	result, err := s.client.Begin(s.ctx, req)

	s.Require().Equal(status.Code(err), codes.Internal)
	s.Contains(err.Error(), "panic")
	s.Nil(result)
	s.tm.AssertNumberOfCalls(s.T(), "Begin", 1)
}

func (s *ServiceSuite) TestService_Begin() {
	req := s.beginRequest()
	s.OnBeginReturn(req, nil)

	result, err := s.client.Begin(s.ctx, req)

	s.NoError(err)
	s.NotNil(result)
	s.tm.AssertNumberOfCalls(s.T(), "Begin", 1)
}
