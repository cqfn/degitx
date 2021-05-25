// MIT License. Copyright (c) 2020 CQFN
// https://github.com/cqfn/degitx/blob/master/LICENSE

// Package repository contains server for gRPC Repository service
package repository

import (
	"cqfn.org/degitx/internal/logging"

	"gitlab.com/gitlab-org/gitaly-proto/go/gitalypb"

	"golang.org/x/net/context"
	"google.golang.org/grpc/codes"
	"google.golang.org/grpc/status"
)

type server struct {
	log *logging.Logger
}

// NewServer creates new RepositoryServiceServer
func NewServer(log *logging.Logger) gitalypb.RepositoryServiceServer {
	return &server{
		log: log,
	}
}

func (server *server) PreFetch(
	context.Context,
	*gitalypb.PreFetchRequest,
) (*gitalypb.PreFetchResponse, error) {
	server.log.Info("PreFetch RPC was called")
	return nil, status.Errorf(codes.Unimplemented, "method PreFetch not implemented")
}

func (server *server) WriteConfig(
	context.Context,
	*gitalypb.WriteConfigRequest,
) (*gitalypb.WriteConfigResponse, error) {
	server.log.Info("WriteConfig RPC was called")
	return nil, status.Errorf(codes.Unimplemented, "method WriteConfig not implemented")
}

func (server *server) RepositoryExists(
	context.Context,
	*gitalypb.RepositoryExistsRequest,
) (*gitalypb.RepositoryExistsResponse, error) {
	server.log.Info("RepositoryExists RPC was called")
	return nil, status.Errorf(codes.Unimplemented, "method RepositoryExists not implemented")
}

func (server *server) RepackIncremental(
	context.Context,
	*gitalypb.RepackIncrementalRequest,
) (*gitalypb.RepackIncrementalResponse, error) {
	server.log.Info("RepackIncremental RPC was called")
	return nil, status.Errorf(codes.Unimplemented, "method RepackIncremental not implemented")
}

func (server *server) RepackFull(
	context.Context,
	*gitalypb.RepackFullRequest,
) (*gitalypb.RepackFullResponse, error) {
	server.log.Info("RepackFull RPC was called")
	return nil, status.Errorf(codes.Unimplemented, "method RepackFull not implemented")
}

func (server *server) GarbageCollect(
	context.Context,
	*gitalypb.GarbageCollectRequest,
) (*gitalypb.GarbageCollectResponse, error) {
	server.log.Info("GarbageCollect RPC was called")
	return nil, status.Errorf(codes.Unimplemented, "method GarbageCollect not implemented")
}

func (server *server) RepositorySize(
	context.Context,
	*gitalypb.RepositorySizeRequest,
) (*gitalypb.RepositorySizeResponse, error) {
	server.log.Info("RepositorySize RPC was called")
	return nil, status.Errorf(codes.Unimplemented, "method RepositorySize not implemented")
}

func (server *server) ApplyGitattributes(
	context.Context,
	*gitalypb.ApplyGitattributesRequest,
) (*gitalypb.ApplyGitattributesResponse, error) {
	server.log.Info("ApplyGitattributes RPC was called")
	return nil, status.Errorf(codes.Unimplemented, "method ApplyGitattributes not implemented")
}

func (server *server) FetchRemote(
	context.Context,
	*gitalypb.FetchRemoteRequest,
) (*gitalypb.FetchRemoteResponse, error) {
	server.log.Info("FetchRemote RPC was called")
	return nil, status.Errorf(codes.Unimplemented, "method FetchRemote not implemented")
}

func (server *server) CreateRepository(
	context.Context,
	*gitalypb.CreateRepositoryRequest,
) (*gitalypb.CreateRepositoryResponse, error) {
	server.log.Info("CreateRepository RPC was called")
	return nil, status.Errorf(codes.Unimplemented, "method CreateRepository not implemented")
}

func (server *server) GetArchive(
	*gitalypb.GetArchiveRequest,
	gitalypb.RepositoryService_GetArchiveServer,
) error {
	server.log.Info("GetArchive RPC was called")
	return status.Errorf(codes.Unimplemented, "method GetArchive not implemented")
}

func (server *server) HasLocalBranches(
	context.Context,
	*gitalypb.HasLocalBranchesRequest,
) (*gitalypb.HasLocalBranchesResponse, error) {
	server.log.Info("HasLocalBranches RPC was called")
	return nil, status.Errorf(codes.Unimplemented, "method HasLocalBranches not implemented")
}

func (server *server) FetchSourceBranch(
	context.Context,
	*gitalypb.FetchSourceBranchRequest,
) (*gitalypb.FetchSourceBranchResponse, error) {
	server.log.Info("FetchSourceBranch RPC was called")
	return nil, status.Errorf(codes.Unimplemented, "method FetchSourceBranch not implemented")
}

func (server *server) Fsck(
	context.Context,
	*gitalypb.FsckRequest,
) (*gitalypb.FsckResponse, error) {
	server.log.Info("Fsck RPC was called")
	return nil, status.Errorf(codes.Unimplemented, "method Fsck not implemented")
}

func (server *server) WriteRef(
	context.Context,
	*gitalypb.WriteRefRequest,
) (*gitalypb.WriteRefResponse, error) {
	server.log.Info("WriteRef RPC was called")
	return nil, status.Errorf(codes.Unimplemented, "method WriteRef not implemented")
}

func (server *server) FindMergeBase(
	context.Context,
	*gitalypb.FindMergeBaseRequest,
) (*gitalypb.FindMergeBaseResponse, error) {
	server.log.Info("FindMergeBase RPC was called")
	return nil, status.Errorf(codes.Unimplemented, "method FindMergeBase not implemented")
}

func (server *server) CreateFork(
	context.Context,
	*gitalypb.CreateForkRequest,
) (*gitalypb.CreateForkResponse, error) {
	server.log.Info("CreateFork RPC was called")
	return nil, status.Errorf(codes.Unimplemented, "method CreateFork not implemented")
}

func (server *server) IsRebaseInProgress(
	context.Context,
	*gitalypb.IsRebaseInProgressRequest,
) (*gitalypb.IsRebaseInProgressResponse, error) {
	server.log.Info("IsRebaseInProgress RPC was called")
	return nil, status.Errorf(codes.Unimplemented, "method IsRebaseInProgress not implemented")
}

func (server *server) IsSquashInProgress(
	context.Context,
	*gitalypb.IsSquashInProgressRequest,
) (*gitalypb.IsSquashInProgressResponse, error) {
	server.log.Info("IsSquashInProgress RPC was called")
	return nil, status.Errorf(codes.Unimplemented, "method IsSquashInProgress not implemented")
}

func (server *server) CreateRepositoryFromURL(
	context.Context,
	*gitalypb.CreateRepositoryFromURLRequest,
) (*gitalypb.CreateRepositoryFromURLResponse, error) {
	server.log.Info("CreateRepositoryFromURL RPC was called")
	return nil, status.Errorf(codes.Unimplemented, "method CreateRepositoryFromURL not implemented")
}

func (server *server) CreateBundle(
	*gitalypb.CreateBundleRequest,
	gitalypb.RepositoryService_CreateBundleServer,
) error {
	server.log.Info("CreateBundle RPC was called")
	return status.Errorf(codes.Unimplemented, "method CreateBundle not implemented")
}

func (server *server) CreateRepositoryFromBundle(
	gitalypb.RepositoryService_CreateRepositoryFromBundleServer,
) error {
	server.log.Info("CreateRepositoryFromBundle RPC was called")
	return status.Errorf(codes.Unimplemented, "method CreateRepositoryFromBundle not implemented")
}

func (server *server) SetConfig(
	context.Context,
	*gitalypb.SetConfigRequest,
) (*gitalypb.SetConfigResponse, error) {
	server.log.Info("SetConfig RPC was called")
	return nil, status.Errorf(codes.Unimplemented, "method SetConfig not implemented")
}

func (server *server) DeleteConfig(
	context.Context,
	*gitalypb.DeleteConfigRequest,
) (*gitalypb.DeleteConfigResponse, error) {
	server.log.Info("DeleteConfig RPC was called")
	return nil, status.Errorf(codes.Unimplemented, "method DeleteConfig not implemented")
}

func (server *server) FindLicense(
	context.Context,
	*gitalypb.FindLicenseRequest,
) (*gitalypb.FindLicenseResponse, error) {
	server.log.Info("FindLicense RPC was called")
	return nil, status.Errorf(codes.Unimplemented, "method FindLicense not implemented")
}

func (server *server) GetInfoAttributes(
	*gitalypb.GetInfoAttributesRequest,
	gitalypb.RepositoryService_GetInfoAttributesServer,
) error {
	server.log.Info("GetInfoAttributes RPC was called")
	return status.Errorf(codes.Unimplemented, "method GetInfoAttributes not implemented")
}

func (server *server) CalculateChecksum(
	context.Context,
	*gitalypb.CalculateChecksumRequest,
) (*gitalypb.CalculateChecksumResponse, error) {
	server.log.Info("CalculateChecksum RPC was called")
	return nil, status.Errorf(codes.Unimplemented, "method CalculateChecksum not implemented")
}

func (server *server) Cleanup(
	context.Context,
	*gitalypb.CleanupRequest,
) (*gitalypb.CleanupResponse, error) {
	server.log.Info("Cleanup RPC was called")
	return nil, status.Errorf(codes.Unimplemented, "method Cleanup not implemented")
}

func (server *server) GetSnapshot(
	*gitalypb.GetSnapshotRequest,
	gitalypb.RepositoryService_GetSnapshotServer,
) error {
	server.log.Info("GetSnapshot RPC was called")
	return status.Errorf(codes.Unimplemented, "method GetSnapshot not implemented")
}

func (server *server) CreateRepositoryFromSnapshot(
	context.Context,
	*gitalypb.CreateRepositoryFromSnapshotRequest,
) (*gitalypb.CreateRepositoryFromSnapshotResponse, error) {
	server.log.Info("CreateRepositoryFromSnapshot RPC was called")
	return nil, status.Errorf(codes.Unimplemented, "method CreateRepositoryFromSnapshot not implemented")
}

func (server *server) GetRawChanges(
	*gitalypb.GetRawChangesRequest,
	gitalypb.RepositoryService_GetRawChangesServer,
) error {
	server.log.Info("GetRawChanges RPC was called")
	return status.Errorf(codes.Unimplemented, "method GetRawChanges not implemented")
}

func (server *server) SearchFilesByContent(
	*gitalypb.SearchFilesByContentRequest,
	gitalypb.RepositoryService_SearchFilesByContentServer,
) error {
	server.log.Info("SearchFilesByContent RPC was called")
	return status.Errorf(codes.Unimplemented, "method SearchFilesByContent not implemented")
}

func (server *server) SearchFilesByName(
	*gitalypb.SearchFilesByNameRequest,
	gitalypb.RepositoryService_SearchFilesByNameServer,
) error {
	server.log.Info("SearchFilesByName RPC was called")
	return status.Errorf(codes.Unimplemented, "method SearchFilesByName not implemented")
}

func (server *server) RestoreCustomHooks(gitalypb.RepositoryService_RestoreCustomHooksServer) error {
	server.log.Info("RestoreCustomHooks RPC was called")
	return status.Errorf(codes.Unimplemented, "method RestoreCustomHooks not implemented")
}

func (server *server) BackupCustomHooks(
	*gitalypb.BackupCustomHooksRequest,
	gitalypb.RepositoryService_BackupCustomHooksServer,
) error {
	server.log.Info("BackupCustomHooks RPC was called")
	return status.Errorf(codes.Unimplemented, "method BackupCustomHooks not implemented")
}

func (server *server) FetchHTTPRemote(
	context.Context,
	*gitalypb.FetchHTTPRemoteRequest,
) (*gitalypb.FetchHTTPRemoteResponse, error) {
	server.log.Info("FetchHTTPRemote RPC was called")
	return nil, status.Errorf(codes.Unimplemented, "method FetchHTTPRemote not implemented")
}
