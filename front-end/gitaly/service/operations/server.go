// MIT License. Copyright (c) 2020 CQFN
// https://github.com/cqfn/degitx/blob/master/LICENSE

// Package operations contains server for gRPC Operation service
package operations

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

// NewServer creates new OperationServiceServer
func NewServer(log *logging.Logger) gitalypb.OperationServiceServer {
	return &server{
		log: log,
	}
}

func (server *server) UserRebase(
	context.Context,
	*gitalypb.UserRebaseRequest, //nolint:staticcheck // backward compatibility
) (*gitalypb.UserRebaseResponse, error) { //nolint:staticcheck // backward compatibility
	server.log.Info("UserRebase RPC was called")
	return nil, status.Errorf(codes.Unimplemented, "method UserRebase not implemented & deprecated")
}

func (server *server) UserCreateBranch(
	context.Context,
	*gitalypb.UserCreateBranchRequest,
) (*gitalypb.UserCreateBranchResponse, error) {
	server.log.Info("UserCreateBranch RPC was called")
	return nil, status.Errorf(codes.Unimplemented, "method UserCreateBranch not implemented")
}

func (server *server) UserUpdateBranch(
	context.Context,
	*gitalypb.UserUpdateBranchRequest,
) (*gitalypb.UserUpdateBranchResponse, error) {
	server.log.Info("UserUpdateBranch RPC was called")
	return nil, status.Errorf(codes.Unimplemented, "method UserUpdateBranch not implemented")
}

func (server *server) UserDeleteBranch(
	context.Context,
	*gitalypb.UserDeleteBranchRequest,
) (*gitalypb.UserDeleteBranchResponse, error) {
	server.log.Info("UserDeleteBranch RPC was called")
	return nil, status.Errorf(codes.Unimplemented, "method UserDeleteBranch not implemented")
}

func (server *server) UserCreateTag(
	context.Context,
	*gitalypb.UserCreateTagRequest,
) (*gitalypb.UserCreateTagResponse, error) {
	server.log.Info("UserCreateTag RPC was called")
	return nil, status.Errorf(codes.Unimplemented, "method UserCreateTag not implemented")
}

func (server *server) UserDeleteTag(
	context.Context,
	*gitalypb.UserDeleteTagRequest,
) (*gitalypb.UserDeleteTagResponse, error) {
	server.log.Info("UserDeleteTag RPC was called")
	return nil, status.Errorf(codes.Unimplemented, "method UserDeleteTag not implemented")
}

func (server *server) UserMergeToRef(
	context.Context,
	*gitalypb.UserMergeToRefRequest,
) (*gitalypb.UserMergeToRefResponse, error) {
	server.log.Info("UserMergeToRef RPC was called")
	return nil, status.Errorf(codes.Unimplemented, "method UserMergeToRef not implemented")
}

func (server *server) UserMergeBranch(gitalypb.OperationService_UserMergeBranchServer) error {
	server.log.Info("UserMergeBranch RPC was called")
	return status.Errorf(codes.Unimplemented, "method UserMergeBranch not implemented")
}

func (server *server) UserFFBranch(
	context.Context,
	*gitalypb.UserFFBranchRequest,
) (*gitalypb.UserFFBranchResponse, error) {
	server.log.Info("UserFFBranch RPC was called")
	return nil, status.Errorf(codes.Unimplemented, "method UserFFBranch not implemented")
}

func (server *server) UserCherryPick(
	context.Context,
	*gitalypb.UserCherryPickRequest,
) (*gitalypb.UserCherryPickResponse, error) {
	server.log.Info("UserCherryPick RPC was called")
	return nil, status.Errorf(codes.Unimplemented, "method UserCherryPick not implemented")
}

func (server *server) UserCommitFiles(gitalypb.OperationService_UserCommitFilesServer) error {
	server.log.Info("UserCommitFiles RPC was called")
	return status.Errorf(codes.Unimplemented, "method UserCommitFiles not implemented")
}

func (server *server) UserRebaseConfirmable(gitalypb.OperationService_UserRebaseConfirmableServer) error {
	server.log.Info("UserRebaseConfirmable RPC was called")
	return status.Errorf(codes.Unimplemented, "method UserRebaseConfirmable not implemented")
}

func (server *server) UserRevert(
	context.Context,
	*gitalypb.UserRevertRequest,
) (*gitalypb.UserRevertResponse, error) {
	server.log.Info("UserRevert RPC was called")
	return nil, status.Errorf(codes.Unimplemented, "method UserRevert not implemented")
}

func (server *server) UserSquash(
	context.Context,
	*gitalypb.UserSquashRequest,
) (*gitalypb.UserSquashResponse, error) {
	server.log.Info("UserSquash RPC was called")
	return nil, status.Errorf(codes.Unimplemented, "method UserSquash not implemented")
}

func (server *server) UserApplyPatch(gitalypb.OperationService_UserApplyPatchServer) error {
	server.log.Info("UserApplyPatch RPC was called")
	return status.Errorf(codes.Unimplemented, "method UserApplyPatch not implemented")
}

func (server *server) UserUpdateSubmodule(
	context.Context,
	*gitalypb.UserUpdateSubmoduleRequest,
) (*gitalypb.UserUpdateSubmoduleResponse, error) {
	server.log.Info("UserUpdateSubmodule RPC was called")
	return nil, status.Errorf(codes.Unimplemented, "method UserUpdateSubmodule not implemented")
}
