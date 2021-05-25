// MIT License. Copyright (c) 2020 CQFN
// https://github.com/cqfn/degitx/blob/master/LICENSE

// Package commit contains server for gRPC Commit service
package commit

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

// NewServer creates new CommitServiceServer
func NewServer(log *logging.Logger) gitalypb.CommitServiceServer {
	return &server{
		log: log,
	}
}

func (server *server) ExtractCommitSignature(
	*gitalypb.ExtractCommitSignatureRequest,
	gitalypb.CommitService_ExtractCommitSignatureServer,
) error {
	server.log.Info("ExtractCommitSignature RPC was called")
	return status.Errorf(codes.Unimplemented, "method ExtractCommitSignature not implemented")
}

func (server *server) CommitIsAncestor(
	context.Context,
	*gitalypb.CommitIsAncestorRequest,
) (*gitalypb.CommitIsAncestorResponse, error) {
	server.log.Info("CommitIsAncestor RPC was called")
	return nil, status.Errorf(codes.Unimplemented, "method CommitIsAncestor not implemented")
}

func (server *server) TreeEntry(
	*gitalypb.TreeEntryRequest,
	gitalypb.CommitService_TreeEntryServer,
) error {
	server.log.Info("TreeEntry RPC was called")
	return status.Errorf(codes.Unimplemented, "method TreeEntry not implemented")
}

func (server *server) CommitsBetween(
	*gitalypb.CommitsBetweenRequest,
	gitalypb.CommitService_CommitsBetweenServer,
) error {
	server.log.Info("CommitsBetween RPC was called")
	return status.Errorf(codes.Unimplemented, "method CommitsBetween not implemented")
}

func (server *server) CountCommits(
	context.Context,
	*gitalypb.CountCommitsRequest,
) (*gitalypb.CountCommitsResponse, error) {
	server.log.Info("CountCommits RPC was called")
	return nil, status.Errorf(codes.Unimplemented, "method CountCommits not implemented")
}

func (server *server) CountDivergingCommits(
	context.Context,
	*gitalypb.CountDivergingCommitsRequest,
) (*gitalypb.CountDivergingCommitsResponse, error) {
	server.log.Info("CountDivergingCommits RPC was called")
	return nil, status.Errorf(codes.Unimplemented, "method CountDivergingCommits not implemented")
}

func (server *server) GetTreeEntries(
	*gitalypb.GetTreeEntriesRequest,
	gitalypb.CommitService_GetTreeEntriesServer,
) error {
	server.log.Info("GetTreeEntries RPC was called")
	return status.Errorf(codes.Unimplemented, "method GetTreeEntries not implemented")
}

func (server *server) ListFiles(
	*gitalypb.ListFilesRequest,
	gitalypb.CommitService_ListFilesServer,
) error {
	server.log.Info("ListFiles RPC was called")
	return status.Errorf(codes.Unimplemented, "method ListFiles not implemented")
}

func (server *server) FindCommit(
	context.Context,
	*gitalypb.FindCommitRequest,
) (*gitalypb.FindCommitResponse, error) {
	server.log.Info("FindCommit RPC was called")
	return nil, status.Errorf(codes.Unimplemented, "method FindCommit not implemented")
}

func (server *server) CommitStats(
	context.Context,
	*gitalypb.CommitStatsRequest,
) (*gitalypb.CommitStatsResponse, error) {
	server.log.Info("CommitStats RPC was called")
	return nil, status.Errorf(codes.Unimplemented, "method CommitStats not implemented")
}

func (server *server) FindAllCommits(
	*gitalypb.FindAllCommitsRequest,
	gitalypb.CommitService_FindAllCommitsServer,
) error {
	server.log.Info("FindAllCommits RPC was called")
	return status.Errorf(codes.Unimplemented, "method FindAllCommits not implemented")
}

func (server *server) FindCommits(
	*gitalypb.FindCommitsRequest,
	gitalypb.CommitService_FindCommitsServer,
) error {
	server.log.Info("FindCommits RPC was called")
	return status.Errorf(codes.Unimplemented, "method FindCommits not implemented")
}

func (server *server) CommitLanguages(
	context.Context,
	*gitalypb.CommitLanguagesRequest,
) (*gitalypb.CommitLanguagesResponse, error) {
	server.log.Info("CommitLanguages RPC was called")
	return nil, status.Errorf(codes.Unimplemented, "method CommitLanguages not implemented")
}

func (server *server) RawBlame(
	*gitalypb.RawBlameRequest,
	gitalypb.CommitService_RawBlameServer,
) error {
	server.log.Info("RawBlame RPC was called")
	return status.Errorf(codes.Unimplemented, "method RawBlame not implemented")
}

func (server *server) LastCommitForPath(
	context.Context,
	*gitalypb.LastCommitForPathRequest,
) (*gitalypb.LastCommitForPathResponse, error) {
	server.log.Info("LastCommitForPath RPC was called")
	return nil, status.Errorf(codes.Unimplemented, "method LastCommitForPath not implemented")
}

func (server *server) ListLastCommitsForTree(
	*gitalypb.ListLastCommitsForTreeRequest,
	gitalypb.CommitService_ListLastCommitsForTreeServer,
) error {
	server.log.Info("ListLastCommitsForTree RPC was called")
	return status.Errorf(codes.Unimplemented, "method ListLastCommitsForTree not implemented")
}

func (server *server) CommitsByMessage(
	*gitalypb.CommitsByMessageRequest,
	gitalypb.CommitService_CommitsByMessageServer,
) error {
	server.log.Info("CommitsByMessage RPC was called")
	return status.Errorf(codes.Unimplemented, "method CommitsByMessage not implemented")
}

func (server *server) ListCommitsByOid(
	*gitalypb.ListCommitsByOidRequest,
	gitalypb.CommitService_ListCommitsByOidServer,
) error {
	server.log.Info("ListCommitsByOid RPC was called")
	return status.Errorf(codes.Unimplemented, "method ListCommitsByOid not implemented")
}

func (server *server) FilterShasWithSignatures(gitalypb.CommitService_FilterShasWithSignaturesServer) error {
	server.log.Info("FilterShasWithSignatures RPC was called")
	return status.Errorf(codes.Unimplemented, "method FilterShasWithSignatures not implemented")
}

func (server *server) GetCommitSignatures(
	*gitalypb.GetCommitSignaturesRequest,
	gitalypb.CommitService_GetCommitSignaturesServer,
) error {
	server.log.Info("GetCommitSignatures RPC was called")
	return status.Errorf(codes.Unimplemented, "method GetCommitSignatures not implemented")
}

func (server *server) GetCommitMessages(
	*gitalypb.GetCommitMessagesRequest,
	gitalypb.CommitService_GetCommitMessagesServer,
) error {
	server.log.Info("GetCommitMessages RPC was called")
	return status.Errorf(codes.Unimplemented, "method GetCommitMessages not implemented")
}
