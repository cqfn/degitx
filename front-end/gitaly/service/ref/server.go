// MIT License. Copyright (c) 2020 CQFN
// https://github.com/cqfn/degitx/blob/master/LICENSE

// Package ref contains server for gRPC Ref service
package ref

import (
	"cqfn.org/degitx/logging"

	"gitlab.com/gitlab-org/gitaly-proto/go/gitalypb"

	"golang.org/x/net/context"
	"google.golang.org/grpc/codes"
	"google.golang.org/grpc/status"
)

type server struct {
	log *logging.Logger
}

func NewServer(log *logging.Logger) gitalypb.RefServiceServer {
	return &server{
		log: log,
	}
}

func (server *server) CreateBranch(
	context.Context,
	*gitalypb.CreateBranchRequest,
) (*gitalypb.CreateBranchResponse, error) {
	server.log.Info("CreateBranch RPC was called")
	return nil, status.Errorf(codes.Unimplemented, "method CreateBranch not implemented")
}

func (server *server) DeleteBranch(
	context.Context,
	*gitalypb.DeleteBranchRequest,
) (*gitalypb.DeleteBranchResponse, error) {
	server.log.Info("DeleteBranch RPC was called")
	return nil, status.Errorf(codes.Unimplemented, "method DeleteBranch not implemented")
}

func (server *server) FindDefaultBranchName(
	context.Context,
	*gitalypb.FindDefaultBranchNameRequest,
) (*gitalypb.FindDefaultBranchNameResponse, error) {
	server.log.Info("FindDefaultBranchName RPC was called")
	return nil, status.Errorf(codes.Unimplemented, "method FindDefaultBranchName not implemented")
}

func (server *server) FindAllBranchNames(
	*gitalypb.FindAllBranchNamesRequest,
	gitalypb.RefService_FindAllBranchNamesServer,
) error {
	server.log.Info("FindAllBranchNames RPC was called")
	return status.Errorf(codes.Unimplemented, "method FindAllBranchNames not implemented")
}

func (server *server) FindAllTagNames(
	*gitalypb.FindAllTagNamesRequest,
	gitalypb.RefService_FindAllTagNamesServer,
) error {
	server.log.Info("FindAllTagNames RPC was called")
	return status.Errorf(codes.Unimplemented, "method FindAllTagNames not implemented")
}

func (server *server) FindRefName(
	context.Context,
	*gitalypb.FindRefNameRequest,
) (*gitalypb.FindRefNameResponse, error) {
	server.log.Info("FindRefName RPC was called")
	return nil, status.Errorf(codes.Unimplemented, "method FindRefName not implemented")
}

func (server *server) FindLocalBranches(
	*gitalypb.FindLocalBranchesRequest,
	gitalypb.RefService_FindLocalBranchesServer,
) error {
	server.log.Info("FindLocalBranches RPC was called")
	return status.Errorf(codes.Unimplemented, "method FindLocalBranches not implemented")
}

func (server *server) FindAllBranches(
	*gitalypb.FindAllBranchesRequest,
	gitalypb.RefService_FindAllBranchesServer,
) error {
	server.log.Info("FindAllBranches RPC was called")
	return status.Errorf(codes.Unimplemented, "method FindAllBranches not implemented")
}

func (server *server) FindAllTags(
	*gitalypb.FindAllTagsRequest,
	gitalypb.RefService_FindAllTagsServer,
) error {
	server.log.Info("FindAllTags RPC was called")
	return status.Errorf(codes.Unimplemented, "method FindAllTags not implemented")
}

func (server *server) FindAllRemoteBranches(
	*gitalypb.FindAllRemoteBranchesRequest,
	gitalypb.RefService_FindAllRemoteBranchesServer,
) error {
	server.log.Info("FindAllRemoteBranches RPC was called")
	return status.Errorf(codes.Unimplemented, "method FindAllRemoteBranches not implemented")
}

func (server *server) RefExists(
	context.Context,
	*gitalypb.RefExistsRequest,
) (*gitalypb.RefExistsResponse, error) {
	server.log.Info("RefExists RPC was called")
	return nil, status.Errorf(codes.Unimplemented, "method RefExists not implemented")
}

func (server *server) FindBranch(
	context.Context,
	*gitalypb.FindBranchRequest,
) (*gitalypb.FindBranchResponse, error) {
	server.log.Info("FindBranch RPC was called")
	return nil, status.Errorf(codes.Unimplemented, "method FindBranch not implemented")
}

func (server *server) DeleteRefs(
	context.Context,
	*gitalypb.DeleteRefsRequest,
) (*gitalypb.DeleteRefsResponse, error) {
	server.log.Info("DeleteRefs RPC was called")
	return nil, status.Errorf(codes.Unimplemented, "method DeleteRefs not implemented")
}

func (server *server) ListBranchNamesContainingCommit(
	*gitalypb.ListBranchNamesContainingCommitRequest,
	gitalypb.RefService_ListBranchNamesContainingCommitServer,
) error {
	server.log.Info("ListBranchNamesContainingCommit RPC was called")
	return status.Errorf(codes.Unimplemented, "method ListBranchNamesContainingCommit not implemented")
}

func (server *server) ListTagNamesContainingCommit(
	*gitalypb.ListTagNamesContainingCommitRequest,
	gitalypb.RefService_ListTagNamesContainingCommitServer,
) error {
	server.log.Info("ListTagNamesContainingCommit RPC was called")
	return status.Errorf(codes.Unimplemented, "method ListTagNamesContainingCommit not implemented")
}

func (server *server) GetTagMessages(
	*gitalypb.GetTagMessagesRequest,
	gitalypb.RefService_GetTagMessagesServer,
) error {
	server.log.Info("GetTagMessages RPC was called")
	return status.Errorf(codes.Unimplemented, "method GetTagMessages not implemented")
}

func (server *server) ListNewCommits(
	*gitalypb.ListNewCommitsRequest,
	gitalypb.RefService_ListNewCommitsServer,
) error {
	server.log.Info("ListNewCommits RPC was called")
	return status.Errorf(codes.Unimplemented, "method ListNewCommits not implemented")
}

func (server *server) ListNewBlobs(
	*gitalypb.ListNewBlobsRequest,
	gitalypb.RefService_ListNewBlobsServer,
) error {
	server.log.Info("ListNewBlobs RPC was called")
	return status.Errorf(codes.Unimplemented, "method ListNewBlobs not implemented")
}

func (server *server) PackRefs(
	context.Context,
	*gitalypb.PackRefsRequest,
) (*gitalypb.PackRefsResponse, error) {
	server.log.Info("PackRefs RPC was called")
	return nil, status.Errorf(codes.Unimplemented, "method PackRefs not implemented")
}
