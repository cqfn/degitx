// Code generated by protoc-gen-go. DO NOT EDIT.
// versions:
// 	protoc-gen-go v1.25.0
// 	protoc        v3.6.1
// source: conflicts.proto

package degitxpb

import (
	context "context"
	proto "github.com/golang/protobuf/proto"
	grpc "google.golang.org/grpc"
	codes "google.golang.org/grpc/codes"
	status "google.golang.org/grpc/status"
	protoreflect "google.golang.org/protobuf/reflect/protoreflect"
	protoimpl "google.golang.org/protobuf/runtime/protoimpl"
	reflect "reflect"
	sync "sync"
)

const (
	// Verify that this generated code is sufficiently up-to-date.
	_ = protoimpl.EnforceVersion(20 - protoimpl.MinVersion)
	// Verify that runtime/protoimpl is sufficiently up-to-date.
	_ = protoimpl.EnforceVersion(protoimpl.MaxVersion - 20)
)

// This is a compile-time assertion that a sufficiently up-to-date version
// of the legacy proto package is being used.
const _ = proto.ProtoPackageIsVersion4

type ListConflictFilesRequest struct {
	state         protoimpl.MessageState
	sizeCache     protoimpl.SizeCache
	unknownFields protoimpl.UnknownFields

	Repository     *Repository `protobuf:"bytes,1,opt,name=repository,proto3" json:"repository,omitempty"`
	OurCommitOid   string      `protobuf:"bytes,2,opt,name=our_commit_oid,json=ourCommitOid,proto3" json:"our_commit_oid,omitempty"`
	TheirCommitOid string      `protobuf:"bytes,3,opt,name=their_commit_oid,json=theirCommitOid,proto3" json:"their_commit_oid,omitempty"`
}

func (x *ListConflictFilesRequest) Reset() {
	*x = ListConflictFilesRequest{}
	if protoimpl.UnsafeEnabled {
		mi := &file_conflicts_proto_msgTypes[0]
		ms := protoimpl.X.MessageStateOf(protoimpl.Pointer(x))
		ms.StoreMessageInfo(mi)
	}
}

func (x *ListConflictFilesRequest) String() string {
	return protoimpl.X.MessageStringOf(x)
}

func (*ListConflictFilesRequest) ProtoMessage() {}

func (x *ListConflictFilesRequest) ProtoReflect() protoreflect.Message {
	mi := &file_conflicts_proto_msgTypes[0]
	if protoimpl.UnsafeEnabled && x != nil {
		ms := protoimpl.X.MessageStateOf(protoimpl.Pointer(x))
		if ms.LoadMessageInfo() == nil {
			ms.StoreMessageInfo(mi)
		}
		return ms
	}
	return mi.MessageOf(x)
}

// Deprecated: Use ListConflictFilesRequest.ProtoReflect.Descriptor instead.
func (*ListConflictFilesRequest) Descriptor() ([]byte, []int) {
	return file_conflicts_proto_rawDescGZIP(), []int{0}
}

func (x *ListConflictFilesRequest) GetRepository() *Repository {
	if x != nil {
		return x.Repository
	}
	return nil
}

func (x *ListConflictFilesRequest) GetOurCommitOid() string {
	if x != nil {
		return x.OurCommitOid
	}
	return ""
}

func (x *ListConflictFilesRequest) GetTheirCommitOid() string {
	if x != nil {
		return x.TheirCommitOid
	}
	return ""
}

type ConflictFileHeader struct {
	state         protoimpl.MessageState
	sizeCache     protoimpl.SizeCache
	unknownFields protoimpl.UnknownFields

	CommitOid string `protobuf:"bytes,2,opt,name=commit_oid,json=commitOid,proto3" json:"commit_oid,omitempty"`
	TheirPath []byte `protobuf:"bytes,3,opt,name=their_path,json=theirPath,proto3" json:"their_path,omitempty"`
	OurPath   []byte `protobuf:"bytes,4,opt,name=our_path,json=ourPath,proto3" json:"our_path,omitempty"`
	OurMode   int32  `protobuf:"varint,5,opt,name=our_mode,json=ourMode,proto3" json:"our_mode,omitempty"`
}

func (x *ConflictFileHeader) Reset() {
	*x = ConflictFileHeader{}
	if protoimpl.UnsafeEnabled {
		mi := &file_conflicts_proto_msgTypes[1]
		ms := protoimpl.X.MessageStateOf(protoimpl.Pointer(x))
		ms.StoreMessageInfo(mi)
	}
}

func (x *ConflictFileHeader) String() string {
	return protoimpl.X.MessageStringOf(x)
}

func (*ConflictFileHeader) ProtoMessage() {}

func (x *ConflictFileHeader) ProtoReflect() protoreflect.Message {
	mi := &file_conflicts_proto_msgTypes[1]
	if protoimpl.UnsafeEnabled && x != nil {
		ms := protoimpl.X.MessageStateOf(protoimpl.Pointer(x))
		if ms.LoadMessageInfo() == nil {
			ms.StoreMessageInfo(mi)
		}
		return ms
	}
	return mi.MessageOf(x)
}

// Deprecated: Use ConflictFileHeader.ProtoReflect.Descriptor instead.
func (*ConflictFileHeader) Descriptor() ([]byte, []int) {
	return file_conflicts_proto_rawDescGZIP(), []int{1}
}

func (x *ConflictFileHeader) GetCommitOid() string {
	if x != nil {
		return x.CommitOid
	}
	return ""
}

func (x *ConflictFileHeader) GetTheirPath() []byte {
	if x != nil {
		return x.TheirPath
	}
	return nil
}

func (x *ConflictFileHeader) GetOurPath() []byte {
	if x != nil {
		return x.OurPath
	}
	return nil
}

func (x *ConflictFileHeader) GetOurMode() int32 {
	if x != nil {
		return x.OurMode
	}
	return 0
}

type ConflictFile struct {
	state         protoimpl.MessageState
	sizeCache     protoimpl.SizeCache
	unknownFields protoimpl.UnknownFields

	// Types that are assignable to ConflictFilePayload:
	//	*ConflictFile_Header
	//	*ConflictFile_Content
	ConflictFilePayload isConflictFile_ConflictFilePayload `protobuf_oneof:"conflict_file_payload"`
}

func (x *ConflictFile) Reset() {
	*x = ConflictFile{}
	if protoimpl.UnsafeEnabled {
		mi := &file_conflicts_proto_msgTypes[2]
		ms := protoimpl.X.MessageStateOf(protoimpl.Pointer(x))
		ms.StoreMessageInfo(mi)
	}
}

func (x *ConflictFile) String() string {
	return protoimpl.X.MessageStringOf(x)
}

func (*ConflictFile) ProtoMessage() {}

func (x *ConflictFile) ProtoReflect() protoreflect.Message {
	mi := &file_conflicts_proto_msgTypes[2]
	if protoimpl.UnsafeEnabled && x != nil {
		ms := protoimpl.X.MessageStateOf(protoimpl.Pointer(x))
		if ms.LoadMessageInfo() == nil {
			ms.StoreMessageInfo(mi)
		}
		return ms
	}
	return mi.MessageOf(x)
}

// Deprecated: Use ConflictFile.ProtoReflect.Descriptor instead.
func (*ConflictFile) Descriptor() ([]byte, []int) {
	return file_conflicts_proto_rawDescGZIP(), []int{2}
}

func (m *ConflictFile) GetConflictFilePayload() isConflictFile_ConflictFilePayload {
	if m != nil {
		return m.ConflictFilePayload
	}
	return nil
}

func (x *ConflictFile) GetHeader() *ConflictFileHeader {
	if x, ok := x.GetConflictFilePayload().(*ConflictFile_Header); ok {
		return x.Header
	}
	return nil
}

func (x *ConflictFile) GetContent() []byte {
	if x, ok := x.GetConflictFilePayload().(*ConflictFile_Content); ok {
		return x.Content
	}
	return nil
}

type isConflictFile_ConflictFilePayload interface {
	isConflictFile_ConflictFilePayload()
}

type ConflictFile_Header struct {
	Header *ConflictFileHeader `protobuf:"bytes,1,opt,name=header,proto3,oneof"`
}

type ConflictFile_Content struct {
	Content []byte `protobuf:"bytes,2,opt,name=content,proto3,oneof"`
}

func (*ConflictFile_Header) isConflictFile_ConflictFilePayload() {}

func (*ConflictFile_Content) isConflictFile_ConflictFilePayload() {}

type ListConflictFilesResponse struct {
	state         protoimpl.MessageState
	sizeCache     protoimpl.SizeCache
	unknownFields protoimpl.UnknownFields

	Files []*ConflictFile `protobuf:"bytes,1,rep,name=files,proto3" json:"files,omitempty"`
}

func (x *ListConflictFilesResponse) Reset() {
	*x = ListConflictFilesResponse{}
	if protoimpl.UnsafeEnabled {
		mi := &file_conflicts_proto_msgTypes[3]
		ms := protoimpl.X.MessageStateOf(protoimpl.Pointer(x))
		ms.StoreMessageInfo(mi)
	}
}

func (x *ListConflictFilesResponse) String() string {
	return protoimpl.X.MessageStringOf(x)
}

func (*ListConflictFilesResponse) ProtoMessage() {}

func (x *ListConflictFilesResponse) ProtoReflect() protoreflect.Message {
	mi := &file_conflicts_proto_msgTypes[3]
	if protoimpl.UnsafeEnabled && x != nil {
		ms := protoimpl.X.MessageStateOf(protoimpl.Pointer(x))
		if ms.LoadMessageInfo() == nil {
			ms.StoreMessageInfo(mi)
		}
		return ms
	}
	return mi.MessageOf(x)
}

// Deprecated: Use ListConflictFilesResponse.ProtoReflect.Descriptor instead.
func (*ListConflictFilesResponse) Descriptor() ([]byte, []int) {
	return file_conflicts_proto_rawDescGZIP(), []int{3}
}

func (x *ListConflictFilesResponse) GetFiles() []*ConflictFile {
	if x != nil {
		return x.Files
	}
	return nil
}

type ResolveConflictsRequestHeader struct {
	state         protoimpl.MessageState
	sizeCache     protoimpl.SizeCache
	unknownFields protoimpl.UnknownFields

	Repository       *Repository `protobuf:"bytes,1,opt,name=repository,proto3" json:"repository,omitempty"`
	OurCommitOid     string      `protobuf:"bytes,2,opt,name=our_commit_oid,json=ourCommitOid,proto3" json:"our_commit_oid,omitempty"`
	TargetRepository *Repository `protobuf:"bytes,3,opt,name=target_repository,json=targetRepository,proto3" json:"target_repository,omitempty"`
	TheirCommitOid   string      `protobuf:"bytes,4,opt,name=their_commit_oid,json=theirCommitOid,proto3" json:"their_commit_oid,omitempty"`
	SourceBranch     []byte      `protobuf:"bytes,5,opt,name=source_branch,json=sourceBranch,proto3" json:"source_branch,omitempty"`
	TargetBranch     []byte      `protobuf:"bytes,6,opt,name=target_branch,json=targetBranch,proto3" json:"target_branch,omitempty"`
	CommitMessage    []byte      `protobuf:"bytes,7,opt,name=commit_message,json=commitMessage,proto3" json:"commit_message,omitempty"`
	User             *User       `protobuf:"bytes,8,opt,name=user,proto3" json:"user,omitempty"`
}

func (x *ResolveConflictsRequestHeader) Reset() {
	*x = ResolveConflictsRequestHeader{}
	if protoimpl.UnsafeEnabled {
		mi := &file_conflicts_proto_msgTypes[4]
		ms := protoimpl.X.MessageStateOf(protoimpl.Pointer(x))
		ms.StoreMessageInfo(mi)
	}
}

func (x *ResolveConflictsRequestHeader) String() string {
	return protoimpl.X.MessageStringOf(x)
}

func (*ResolveConflictsRequestHeader) ProtoMessage() {}

func (x *ResolveConflictsRequestHeader) ProtoReflect() protoreflect.Message {
	mi := &file_conflicts_proto_msgTypes[4]
	if protoimpl.UnsafeEnabled && x != nil {
		ms := protoimpl.X.MessageStateOf(protoimpl.Pointer(x))
		if ms.LoadMessageInfo() == nil {
			ms.StoreMessageInfo(mi)
		}
		return ms
	}
	return mi.MessageOf(x)
}

// Deprecated: Use ResolveConflictsRequestHeader.ProtoReflect.Descriptor instead.
func (*ResolveConflictsRequestHeader) Descriptor() ([]byte, []int) {
	return file_conflicts_proto_rawDescGZIP(), []int{4}
}

func (x *ResolveConflictsRequestHeader) GetRepository() *Repository {
	if x != nil {
		return x.Repository
	}
	return nil
}

func (x *ResolveConflictsRequestHeader) GetOurCommitOid() string {
	if x != nil {
		return x.OurCommitOid
	}
	return ""
}

func (x *ResolveConflictsRequestHeader) GetTargetRepository() *Repository {
	if x != nil {
		return x.TargetRepository
	}
	return nil
}

func (x *ResolveConflictsRequestHeader) GetTheirCommitOid() string {
	if x != nil {
		return x.TheirCommitOid
	}
	return ""
}

func (x *ResolveConflictsRequestHeader) GetSourceBranch() []byte {
	if x != nil {
		return x.SourceBranch
	}
	return nil
}

func (x *ResolveConflictsRequestHeader) GetTargetBranch() []byte {
	if x != nil {
		return x.TargetBranch
	}
	return nil
}

func (x *ResolveConflictsRequestHeader) GetCommitMessage() []byte {
	if x != nil {
		return x.CommitMessage
	}
	return nil
}

func (x *ResolveConflictsRequestHeader) GetUser() *User {
	if x != nil {
		return x.User
	}
	return nil
}

type ResolveConflictsRequest struct {
	state         protoimpl.MessageState
	sizeCache     protoimpl.SizeCache
	unknownFields protoimpl.UnknownFields

	// Types that are assignable to ResolveConflictsRequestPayload:
	//	*ResolveConflictsRequest_Header
	//	*ResolveConflictsRequest_FilesJson
	ResolveConflictsRequestPayload isResolveConflictsRequest_ResolveConflictsRequestPayload `protobuf_oneof:"resolve_conflicts_request_payload"`
}

func (x *ResolveConflictsRequest) Reset() {
	*x = ResolveConflictsRequest{}
	if protoimpl.UnsafeEnabled {
		mi := &file_conflicts_proto_msgTypes[5]
		ms := protoimpl.X.MessageStateOf(protoimpl.Pointer(x))
		ms.StoreMessageInfo(mi)
	}
}

func (x *ResolveConflictsRequest) String() string {
	return protoimpl.X.MessageStringOf(x)
}

func (*ResolveConflictsRequest) ProtoMessage() {}

func (x *ResolveConflictsRequest) ProtoReflect() protoreflect.Message {
	mi := &file_conflicts_proto_msgTypes[5]
	if protoimpl.UnsafeEnabled && x != nil {
		ms := protoimpl.X.MessageStateOf(protoimpl.Pointer(x))
		if ms.LoadMessageInfo() == nil {
			ms.StoreMessageInfo(mi)
		}
		return ms
	}
	return mi.MessageOf(x)
}

// Deprecated: Use ResolveConflictsRequest.ProtoReflect.Descriptor instead.
func (*ResolveConflictsRequest) Descriptor() ([]byte, []int) {
	return file_conflicts_proto_rawDescGZIP(), []int{5}
}

func (m *ResolveConflictsRequest) GetResolveConflictsRequestPayload() isResolveConflictsRequest_ResolveConflictsRequestPayload {
	if m != nil {
		return m.ResolveConflictsRequestPayload
	}
	return nil
}

func (x *ResolveConflictsRequest) GetHeader() *ResolveConflictsRequestHeader {
	if x, ok := x.GetResolveConflictsRequestPayload().(*ResolveConflictsRequest_Header); ok {
		return x.Header
	}
	return nil
}

func (x *ResolveConflictsRequest) GetFilesJson() []byte {
	if x, ok := x.GetResolveConflictsRequestPayload().(*ResolveConflictsRequest_FilesJson); ok {
		return x.FilesJson
	}
	return nil
}

type isResolveConflictsRequest_ResolveConflictsRequestPayload interface {
	isResolveConflictsRequest_ResolveConflictsRequestPayload()
}

type ResolveConflictsRequest_Header struct {
	Header *ResolveConflictsRequestHeader `protobuf:"bytes,1,opt,name=header,proto3,oneof"`
}

type ResolveConflictsRequest_FilesJson struct {
	FilesJson []byte `protobuf:"bytes,2,opt,name=files_json,json=filesJson,proto3,oneof"`
}

func (*ResolveConflictsRequest_Header) isResolveConflictsRequest_ResolveConflictsRequestPayload() {}

func (*ResolveConflictsRequest_FilesJson) isResolveConflictsRequest_ResolveConflictsRequestPayload() {
}

type ResolveConflictsResponse struct {
	state         protoimpl.MessageState
	sizeCache     protoimpl.SizeCache
	unknownFields protoimpl.UnknownFields

	ResolutionError string `protobuf:"bytes,1,opt,name=resolution_error,json=resolutionError,proto3" json:"resolution_error,omitempty"`
}

func (x *ResolveConflictsResponse) Reset() {
	*x = ResolveConflictsResponse{}
	if protoimpl.UnsafeEnabled {
		mi := &file_conflicts_proto_msgTypes[6]
		ms := protoimpl.X.MessageStateOf(protoimpl.Pointer(x))
		ms.StoreMessageInfo(mi)
	}
}

func (x *ResolveConflictsResponse) String() string {
	return protoimpl.X.MessageStringOf(x)
}

func (*ResolveConflictsResponse) ProtoMessage() {}

func (x *ResolveConflictsResponse) ProtoReflect() protoreflect.Message {
	mi := &file_conflicts_proto_msgTypes[6]
	if protoimpl.UnsafeEnabled && x != nil {
		ms := protoimpl.X.MessageStateOf(protoimpl.Pointer(x))
		if ms.LoadMessageInfo() == nil {
			ms.StoreMessageInfo(mi)
		}
		return ms
	}
	return mi.MessageOf(x)
}

// Deprecated: Use ResolveConflictsResponse.ProtoReflect.Descriptor instead.
func (*ResolveConflictsResponse) Descriptor() ([]byte, []int) {
	return file_conflicts_proto_rawDescGZIP(), []int{6}
}

func (x *ResolveConflictsResponse) GetResolutionError() string {
	if x != nil {
		return x.ResolutionError
	}
	return ""
}

var File_conflicts_proto protoreflect.FileDescriptor

var file_conflicts_proto_rawDesc = []byte{
	0x0a, 0x0f, 0x63, 0x6f, 0x6e, 0x66, 0x6c, 0x69, 0x63, 0x74, 0x73, 0x2e, 0x70, 0x72, 0x6f, 0x74,
	0x6f, 0x12, 0x06, 0x64, 0x65, 0x67, 0x69, 0x74, 0x78, 0x1a, 0x0a, 0x6c, 0x69, 0x6e, 0x74, 0x2e,
	0x70, 0x72, 0x6f, 0x74, 0x6f, 0x1a, 0x0c, 0x73, 0x68, 0x61, 0x72, 0x65, 0x64, 0x2e, 0x70, 0x72,
	0x6f, 0x74, 0x6f, 0x22, 0xa4, 0x01, 0x0a, 0x18, 0x4c, 0x69, 0x73, 0x74, 0x43, 0x6f, 0x6e, 0x66,
	0x6c, 0x69, 0x63, 0x74, 0x46, 0x69, 0x6c, 0x65, 0x73, 0x52, 0x65, 0x71, 0x75, 0x65, 0x73, 0x74,
	0x12, 0x38, 0x0a, 0x0a, 0x72, 0x65, 0x70, 0x6f, 0x73, 0x69, 0x74, 0x6f, 0x72, 0x79, 0x18, 0x01,
	0x20, 0x01, 0x28, 0x0b, 0x32, 0x12, 0x2e, 0x64, 0x65, 0x67, 0x69, 0x74, 0x78, 0x2e, 0x52, 0x65,
	0x70, 0x6f, 0x73, 0x69, 0x74, 0x6f, 0x72, 0x79, 0x42, 0x04, 0x98, 0xc6, 0x2c, 0x01, 0x52, 0x0a,
	0x72, 0x65, 0x70, 0x6f, 0x73, 0x69, 0x74, 0x6f, 0x72, 0x79, 0x12, 0x24, 0x0a, 0x0e, 0x6f, 0x75,
	0x72, 0x5f, 0x63, 0x6f, 0x6d, 0x6d, 0x69, 0x74, 0x5f, 0x6f, 0x69, 0x64, 0x18, 0x02, 0x20, 0x01,
	0x28, 0x09, 0x52, 0x0c, 0x6f, 0x75, 0x72, 0x43, 0x6f, 0x6d, 0x6d, 0x69, 0x74, 0x4f, 0x69, 0x64,
	0x12, 0x28, 0x0a, 0x10, 0x74, 0x68, 0x65, 0x69, 0x72, 0x5f, 0x63, 0x6f, 0x6d, 0x6d, 0x69, 0x74,
	0x5f, 0x6f, 0x69, 0x64, 0x18, 0x03, 0x20, 0x01, 0x28, 0x09, 0x52, 0x0e, 0x74, 0x68, 0x65, 0x69,
	0x72, 0x43, 0x6f, 0x6d, 0x6d, 0x69, 0x74, 0x4f, 0x69, 0x64, 0x22, 0x8e, 0x01, 0x0a, 0x12, 0x43,
	0x6f, 0x6e, 0x66, 0x6c, 0x69, 0x63, 0x74, 0x46, 0x69, 0x6c, 0x65, 0x48, 0x65, 0x61, 0x64, 0x65,
	0x72, 0x12, 0x1d, 0x0a, 0x0a, 0x63, 0x6f, 0x6d, 0x6d, 0x69, 0x74, 0x5f, 0x6f, 0x69, 0x64, 0x18,
	0x02, 0x20, 0x01, 0x28, 0x09, 0x52, 0x09, 0x63, 0x6f, 0x6d, 0x6d, 0x69, 0x74, 0x4f, 0x69, 0x64,
	0x12, 0x1d, 0x0a, 0x0a, 0x74, 0x68, 0x65, 0x69, 0x72, 0x5f, 0x70, 0x61, 0x74, 0x68, 0x18, 0x03,
	0x20, 0x01, 0x28, 0x0c, 0x52, 0x09, 0x74, 0x68, 0x65, 0x69, 0x72, 0x50, 0x61, 0x74, 0x68, 0x12,
	0x19, 0x0a, 0x08, 0x6f, 0x75, 0x72, 0x5f, 0x70, 0x61, 0x74, 0x68, 0x18, 0x04, 0x20, 0x01, 0x28,
	0x0c, 0x52, 0x07, 0x6f, 0x75, 0x72, 0x50, 0x61, 0x74, 0x68, 0x12, 0x19, 0x0a, 0x08, 0x6f, 0x75,
	0x72, 0x5f, 0x6d, 0x6f, 0x64, 0x65, 0x18, 0x05, 0x20, 0x01, 0x28, 0x05, 0x52, 0x07, 0x6f, 0x75,
	0x72, 0x4d, 0x6f, 0x64, 0x65, 0x4a, 0x04, 0x08, 0x01, 0x10, 0x02, 0x22, 0x79, 0x0a, 0x0c, 0x43,
	0x6f, 0x6e, 0x66, 0x6c, 0x69, 0x63, 0x74, 0x46, 0x69, 0x6c, 0x65, 0x12, 0x34, 0x0a, 0x06, 0x68,
	0x65, 0x61, 0x64, 0x65, 0x72, 0x18, 0x01, 0x20, 0x01, 0x28, 0x0b, 0x32, 0x1a, 0x2e, 0x64, 0x65,
	0x67, 0x69, 0x74, 0x78, 0x2e, 0x43, 0x6f, 0x6e, 0x66, 0x6c, 0x69, 0x63, 0x74, 0x46, 0x69, 0x6c,
	0x65, 0x48, 0x65, 0x61, 0x64, 0x65, 0x72, 0x48, 0x00, 0x52, 0x06, 0x68, 0x65, 0x61, 0x64, 0x65,
	0x72, 0x12, 0x1a, 0x0a, 0x07, 0x63, 0x6f, 0x6e, 0x74, 0x65, 0x6e, 0x74, 0x18, 0x02, 0x20, 0x01,
	0x28, 0x0c, 0x48, 0x00, 0x52, 0x07, 0x63, 0x6f, 0x6e, 0x74, 0x65, 0x6e, 0x74, 0x42, 0x17, 0x0a,
	0x15, 0x63, 0x6f, 0x6e, 0x66, 0x6c, 0x69, 0x63, 0x74, 0x5f, 0x66, 0x69, 0x6c, 0x65, 0x5f, 0x70,
	0x61, 0x79, 0x6c, 0x6f, 0x61, 0x64, 0x22, 0x47, 0x0a, 0x19, 0x4c, 0x69, 0x73, 0x74, 0x43, 0x6f,
	0x6e, 0x66, 0x6c, 0x69, 0x63, 0x74, 0x46, 0x69, 0x6c, 0x65, 0x73, 0x52, 0x65, 0x73, 0x70, 0x6f,
	0x6e, 0x73, 0x65, 0x12, 0x2a, 0x0a, 0x05, 0x66, 0x69, 0x6c, 0x65, 0x73, 0x18, 0x01, 0x20, 0x03,
	0x28, 0x0b, 0x32, 0x14, 0x2e, 0x64, 0x65, 0x67, 0x69, 0x74, 0x78, 0x2e, 0x43, 0x6f, 0x6e, 0x66,
	0x6c, 0x69, 0x63, 0x74, 0x46, 0x69, 0x6c, 0x65, 0x52, 0x05, 0x66, 0x69, 0x6c, 0x65, 0x73, 0x22,
	0xfd, 0x02, 0x0a, 0x1d, 0x52, 0x65, 0x73, 0x6f, 0x6c, 0x76, 0x65, 0x43, 0x6f, 0x6e, 0x66, 0x6c,
	0x69, 0x63, 0x74, 0x73, 0x52, 0x65, 0x71, 0x75, 0x65, 0x73, 0x74, 0x48, 0x65, 0x61, 0x64, 0x65,
	0x72, 0x12, 0x38, 0x0a, 0x0a, 0x72, 0x65, 0x70, 0x6f, 0x73, 0x69, 0x74, 0x6f, 0x72, 0x79, 0x18,
	0x01, 0x20, 0x01, 0x28, 0x0b, 0x32, 0x12, 0x2e, 0x64, 0x65, 0x67, 0x69, 0x74, 0x78, 0x2e, 0x52,
	0x65, 0x70, 0x6f, 0x73, 0x69, 0x74, 0x6f, 0x72, 0x79, 0x42, 0x04, 0x98, 0xc6, 0x2c, 0x01, 0x52,
	0x0a, 0x72, 0x65, 0x70, 0x6f, 0x73, 0x69, 0x74, 0x6f, 0x72, 0x79, 0x12, 0x24, 0x0a, 0x0e, 0x6f,
	0x75, 0x72, 0x5f, 0x63, 0x6f, 0x6d, 0x6d, 0x69, 0x74, 0x5f, 0x6f, 0x69, 0x64, 0x18, 0x02, 0x20,
	0x01, 0x28, 0x09, 0x52, 0x0c, 0x6f, 0x75, 0x72, 0x43, 0x6f, 0x6d, 0x6d, 0x69, 0x74, 0x4f, 0x69,
	0x64, 0x12, 0x3f, 0x0a, 0x11, 0x74, 0x61, 0x72, 0x67, 0x65, 0x74, 0x5f, 0x72, 0x65, 0x70, 0x6f,
	0x73, 0x69, 0x74, 0x6f, 0x72, 0x79, 0x18, 0x03, 0x20, 0x01, 0x28, 0x0b, 0x32, 0x12, 0x2e, 0x64,
	0x65, 0x67, 0x69, 0x74, 0x78, 0x2e, 0x52, 0x65, 0x70, 0x6f, 0x73, 0x69, 0x74, 0x6f, 0x72, 0x79,
	0x52, 0x10, 0x74, 0x61, 0x72, 0x67, 0x65, 0x74, 0x52, 0x65, 0x70, 0x6f, 0x73, 0x69, 0x74, 0x6f,
	0x72, 0x79, 0x12, 0x28, 0x0a, 0x10, 0x74, 0x68, 0x65, 0x69, 0x72, 0x5f, 0x63, 0x6f, 0x6d, 0x6d,
	0x69, 0x74, 0x5f, 0x6f, 0x69, 0x64, 0x18, 0x04, 0x20, 0x01, 0x28, 0x09, 0x52, 0x0e, 0x74, 0x68,
	0x65, 0x69, 0x72, 0x43, 0x6f, 0x6d, 0x6d, 0x69, 0x74, 0x4f, 0x69, 0x64, 0x12, 0x23, 0x0a, 0x0d,
	0x73, 0x6f, 0x75, 0x72, 0x63, 0x65, 0x5f, 0x62, 0x72, 0x61, 0x6e, 0x63, 0x68, 0x18, 0x05, 0x20,
	0x01, 0x28, 0x0c, 0x52, 0x0c, 0x73, 0x6f, 0x75, 0x72, 0x63, 0x65, 0x42, 0x72, 0x61, 0x6e, 0x63,
	0x68, 0x12, 0x23, 0x0a, 0x0d, 0x74, 0x61, 0x72, 0x67, 0x65, 0x74, 0x5f, 0x62, 0x72, 0x61, 0x6e,
	0x63, 0x68, 0x18, 0x06, 0x20, 0x01, 0x28, 0x0c, 0x52, 0x0c, 0x74, 0x61, 0x72, 0x67, 0x65, 0x74,
	0x42, 0x72, 0x61, 0x6e, 0x63, 0x68, 0x12, 0x25, 0x0a, 0x0e, 0x63, 0x6f, 0x6d, 0x6d, 0x69, 0x74,
	0x5f, 0x6d, 0x65, 0x73, 0x73, 0x61, 0x67, 0x65, 0x18, 0x07, 0x20, 0x01, 0x28, 0x0c, 0x52, 0x0d,
	0x63, 0x6f, 0x6d, 0x6d, 0x69, 0x74, 0x4d, 0x65, 0x73, 0x73, 0x61, 0x67, 0x65, 0x12, 0x20, 0x0a,
	0x04, 0x75, 0x73, 0x65, 0x72, 0x18, 0x08, 0x20, 0x01, 0x28, 0x0b, 0x32, 0x0c, 0x2e, 0x64, 0x65,
	0x67, 0x69, 0x74, 0x78, 0x2e, 0x55, 0x73, 0x65, 0x72, 0x52, 0x04, 0x75, 0x73, 0x65, 0x72, 0x22,
	0xa0, 0x01, 0x0a, 0x17, 0x52, 0x65, 0x73, 0x6f, 0x6c, 0x76, 0x65, 0x43, 0x6f, 0x6e, 0x66, 0x6c,
	0x69, 0x63, 0x74, 0x73, 0x52, 0x65, 0x71, 0x75, 0x65, 0x73, 0x74, 0x12, 0x3f, 0x0a, 0x06, 0x68,
	0x65, 0x61, 0x64, 0x65, 0x72, 0x18, 0x01, 0x20, 0x01, 0x28, 0x0b, 0x32, 0x25, 0x2e, 0x64, 0x65,
	0x67, 0x69, 0x74, 0x78, 0x2e, 0x52, 0x65, 0x73, 0x6f, 0x6c, 0x76, 0x65, 0x43, 0x6f, 0x6e, 0x66,
	0x6c, 0x69, 0x63, 0x74, 0x73, 0x52, 0x65, 0x71, 0x75, 0x65, 0x73, 0x74, 0x48, 0x65, 0x61, 0x64,
	0x65, 0x72, 0x48, 0x00, 0x52, 0x06, 0x68, 0x65, 0x61, 0x64, 0x65, 0x72, 0x12, 0x1f, 0x0a, 0x0a,
	0x66, 0x69, 0x6c, 0x65, 0x73, 0x5f, 0x6a, 0x73, 0x6f, 0x6e, 0x18, 0x02, 0x20, 0x01, 0x28, 0x0c,
	0x48, 0x00, 0x52, 0x09, 0x66, 0x69, 0x6c, 0x65, 0x73, 0x4a, 0x73, 0x6f, 0x6e, 0x42, 0x23, 0x0a,
	0x21, 0x72, 0x65, 0x73, 0x6f, 0x6c, 0x76, 0x65, 0x5f, 0x63, 0x6f, 0x6e, 0x66, 0x6c, 0x69, 0x63,
	0x74, 0x73, 0x5f, 0x72, 0x65, 0x71, 0x75, 0x65, 0x73, 0x74, 0x5f, 0x70, 0x61, 0x79, 0x6c, 0x6f,
	0x61, 0x64, 0x22, 0x45, 0x0a, 0x18, 0x52, 0x65, 0x73, 0x6f, 0x6c, 0x76, 0x65, 0x43, 0x6f, 0x6e,
	0x66, 0x6c, 0x69, 0x63, 0x74, 0x73, 0x52, 0x65, 0x73, 0x70, 0x6f, 0x6e, 0x73, 0x65, 0x12, 0x29,
	0x0a, 0x10, 0x72, 0x65, 0x73, 0x6f, 0x6c, 0x75, 0x74, 0x69, 0x6f, 0x6e, 0x5f, 0x65, 0x72, 0x72,
	0x6f, 0x72, 0x18, 0x01, 0x20, 0x01, 0x28, 0x09, 0x52, 0x0f, 0x72, 0x65, 0x73, 0x6f, 0x6c, 0x75,
	0x74, 0x69, 0x6f, 0x6e, 0x45, 0x72, 0x72, 0x6f, 0x72, 0x32, 0xd7, 0x01, 0x0a, 0x10, 0x43, 0x6f,
	0x6e, 0x66, 0x6c, 0x69, 0x63, 0x74, 0x73, 0x53, 0x65, 0x72, 0x76, 0x69, 0x63, 0x65, 0x12, 0x62,
	0x0a, 0x11, 0x4c, 0x69, 0x73, 0x74, 0x43, 0x6f, 0x6e, 0x66, 0x6c, 0x69, 0x63, 0x74, 0x46, 0x69,
	0x6c, 0x65, 0x73, 0x12, 0x20, 0x2e, 0x64, 0x65, 0x67, 0x69, 0x74, 0x78, 0x2e, 0x4c, 0x69, 0x73,
	0x74, 0x43, 0x6f, 0x6e, 0x66, 0x6c, 0x69, 0x63, 0x74, 0x46, 0x69, 0x6c, 0x65, 0x73, 0x52, 0x65,
	0x71, 0x75, 0x65, 0x73, 0x74, 0x1a, 0x21, 0x2e, 0x64, 0x65, 0x67, 0x69, 0x74, 0x78, 0x2e, 0x4c,
	0x69, 0x73, 0x74, 0x43, 0x6f, 0x6e, 0x66, 0x6c, 0x69, 0x63, 0x74, 0x46, 0x69, 0x6c, 0x65, 0x73,
	0x52, 0x65, 0x73, 0x70, 0x6f, 0x6e, 0x73, 0x65, 0x22, 0x06, 0xfa, 0x97, 0x28, 0x02, 0x08, 0x02,
	0x30, 0x01, 0x12, 0x5f, 0x0a, 0x10, 0x52, 0x65, 0x73, 0x6f, 0x6c, 0x76, 0x65, 0x43, 0x6f, 0x6e,
	0x66, 0x6c, 0x69, 0x63, 0x74, 0x73, 0x12, 0x1f, 0x2e, 0x64, 0x65, 0x67, 0x69, 0x74, 0x78, 0x2e,
	0x52, 0x65, 0x73, 0x6f, 0x6c, 0x76, 0x65, 0x43, 0x6f, 0x6e, 0x66, 0x6c, 0x69, 0x63, 0x74, 0x73,
	0x52, 0x65, 0x71, 0x75, 0x65, 0x73, 0x74, 0x1a, 0x20, 0x2e, 0x64, 0x65, 0x67, 0x69, 0x74, 0x78,
	0x2e, 0x52, 0x65, 0x73, 0x6f, 0x6c, 0x76, 0x65, 0x43, 0x6f, 0x6e, 0x66, 0x6c, 0x69, 0x63, 0x74,
	0x73, 0x52, 0x65, 0x73, 0x70, 0x6f, 0x6e, 0x73, 0x65, 0x22, 0x06, 0xfa, 0x97, 0x28, 0x02, 0x08,
	0x01, 0x28, 0x01, 0x42, 0x23, 0x5a, 0x21, 0x6f, 0x72, 0x67, 0x2e, 0x63, 0x71, 0x66, 0x6e, 0x2f,
	0x64, 0x65, 0x67, 0x69, 0x74, 0x78, 0x2f, 0x70, 0x72, 0x6f, 0x74, 0x6f, 0x2f, 0x67, 0x6f, 0x2f,
	0x64, 0x65, 0x67, 0x69, 0x74, 0x78, 0x70, 0x62, 0x62, 0x06, 0x70, 0x72, 0x6f, 0x74, 0x6f, 0x33,
}

var (
	file_conflicts_proto_rawDescOnce sync.Once
	file_conflicts_proto_rawDescData = file_conflicts_proto_rawDesc
)

func file_conflicts_proto_rawDescGZIP() []byte {
	file_conflicts_proto_rawDescOnce.Do(func() {
		file_conflicts_proto_rawDescData = protoimpl.X.CompressGZIP(file_conflicts_proto_rawDescData)
	})
	return file_conflicts_proto_rawDescData
}

var file_conflicts_proto_msgTypes = make([]protoimpl.MessageInfo, 7)
var file_conflicts_proto_goTypes = []interface{}{
	(*ListConflictFilesRequest)(nil),      // 0: degitx.ListConflictFilesRequest
	(*ConflictFileHeader)(nil),            // 1: degitx.ConflictFileHeader
	(*ConflictFile)(nil),                  // 2: degitx.ConflictFile
	(*ListConflictFilesResponse)(nil),     // 3: degitx.ListConflictFilesResponse
	(*ResolveConflictsRequestHeader)(nil), // 4: degitx.ResolveConflictsRequestHeader
	(*ResolveConflictsRequest)(nil),       // 5: degitx.ResolveConflictsRequest
	(*ResolveConflictsResponse)(nil),      // 6: degitx.ResolveConflictsResponse
	(*Repository)(nil),                    // 7: degitx.Repository
	(*User)(nil),                          // 8: degitx.User
}
var file_conflicts_proto_depIdxs = []int32{
	7, // 0: degitx.ListConflictFilesRequest.repository:type_name -> degitx.Repository
	1, // 1: degitx.ConflictFile.header:type_name -> degitx.ConflictFileHeader
	2, // 2: degitx.ListConflictFilesResponse.files:type_name -> degitx.ConflictFile
	7, // 3: degitx.ResolveConflictsRequestHeader.repository:type_name -> degitx.Repository
	7, // 4: degitx.ResolveConflictsRequestHeader.target_repository:type_name -> degitx.Repository
	8, // 5: degitx.ResolveConflictsRequestHeader.user:type_name -> degitx.User
	4, // 6: degitx.ResolveConflictsRequest.header:type_name -> degitx.ResolveConflictsRequestHeader
	0, // 7: degitx.ConflictsService.ListConflictFiles:input_type -> degitx.ListConflictFilesRequest
	5, // 8: degitx.ConflictsService.ResolveConflicts:input_type -> degitx.ResolveConflictsRequest
	3, // 9: degitx.ConflictsService.ListConflictFiles:output_type -> degitx.ListConflictFilesResponse
	6, // 10: degitx.ConflictsService.ResolveConflicts:output_type -> degitx.ResolveConflictsResponse
	9, // [9:11] is the sub-list for method output_type
	7, // [7:9] is the sub-list for method input_type
	7, // [7:7] is the sub-list for extension type_name
	7, // [7:7] is the sub-list for extension extendee
	0, // [0:7] is the sub-list for field type_name
}

func init() { file_conflicts_proto_init() }
func file_conflicts_proto_init() {
	if File_conflicts_proto != nil {
		return
	}
	file_lint_proto_init()
	file_shared_proto_init()
	if !protoimpl.UnsafeEnabled {
		file_conflicts_proto_msgTypes[0].Exporter = func(v interface{}, i int) interface{} {
			switch v := v.(*ListConflictFilesRequest); i {
			case 0:
				return &v.state
			case 1:
				return &v.sizeCache
			case 2:
				return &v.unknownFields
			default:
				return nil
			}
		}
		file_conflicts_proto_msgTypes[1].Exporter = func(v interface{}, i int) interface{} {
			switch v := v.(*ConflictFileHeader); i {
			case 0:
				return &v.state
			case 1:
				return &v.sizeCache
			case 2:
				return &v.unknownFields
			default:
				return nil
			}
		}
		file_conflicts_proto_msgTypes[2].Exporter = func(v interface{}, i int) interface{} {
			switch v := v.(*ConflictFile); i {
			case 0:
				return &v.state
			case 1:
				return &v.sizeCache
			case 2:
				return &v.unknownFields
			default:
				return nil
			}
		}
		file_conflicts_proto_msgTypes[3].Exporter = func(v interface{}, i int) interface{} {
			switch v := v.(*ListConflictFilesResponse); i {
			case 0:
				return &v.state
			case 1:
				return &v.sizeCache
			case 2:
				return &v.unknownFields
			default:
				return nil
			}
		}
		file_conflicts_proto_msgTypes[4].Exporter = func(v interface{}, i int) interface{} {
			switch v := v.(*ResolveConflictsRequestHeader); i {
			case 0:
				return &v.state
			case 1:
				return &v.sizeCache
			case 2:
				return &v.unknownFields
			default:
				return nil
			}
		}
		file_conflicts_proto_msgTypes[5].Exporter = func(v interface{}, i int) interface{} {
			switch v := v.(*ResolveConflictsRequest); i {
			case 0:
				return &v.state
			case 1:
				return &v.sizeCache
			case 2:
				return &v.unknownFields
			default:
				return nil
			}
		}
		file_conflicts_proto_msgTypes[6].Exporter = func(v interface{}, i int) interface{} {
			switch v := v.(*ResolveConflictsResponse); i {
			case 0:
				return &v.state
			case 1:
				return &v.sizeCache
			case 2:
				return &v.unknownFields
			default:
				return nil
			}
		}
	}
	file_conflicts_proto_msgTypes[2].OneofWrappers = []interface{}{
		(*ConflictFile_Header)(nil),
		(*ConflictFile_Content)(nil),
	}
	file_conflicts_proto_msgTypes[5].OneofWrappers = []interface{}{
		(*ResolveConflictsRequest_Header)(nil),
		(*ResolveConflictsRequest_FilesJson)(nil),
	}
	type x struct{}
	out := protoimpl.TypeBuilder{
		File: protoimpl.DescBuilder{
			GoPackagePath: reflect.TypeOf(x{}).PkgPath(),
			RawDescriptor: file_conflicts_proto_rawDesc,
			NumEnums:      0,
			NumMessages:   7,
			NumExtensions: 0,
			NumServices:   1,
		},
		GoTypes:           file_conflicts_proto_goTypes,
		DependencyIndexes: file_conflicts_proto_depIdxs,
		MessageInfos:      file_conflicts_proto_msgTypes,
	}.Build()
	File_conflicts_proto = out.File
	file_conflicts_proto_rawDesc = nil
	file_conflicts_proto_goTypes = nil
	file_conflicts_proto_depIdxs = nil
}

// Reference imports to suppress errors if they are not otherwise used.
var _ context.Context
var _ grpc.ClientConnInterface

// This is a compile-time assertion to ensure that this generated file
// is compatible with the grpc package it is being compiled against.
const _ = grpc.SupportPackageIsVersion6

// ConflictsServiceClient is the client API for ConflictsService service.
//
// For semantics around ctx use and closing/ending streaming RPCs, please refer to https://godoc.org/google.golang.org/grpc#ClientConn.NewStream.
type ConflictsServiceClient interface {
	ListConflictFiles(ctx context.Context, in *ListConflictFilesRequest, opts ...grpc.CallOption) (ConflictsService_ListConflictFilesClient, error)
	ResolveConflicts(ctx context.Context, opts ...grpc.CallOption) (ConflictsService_ResolveConflictsClient, error)
}

type conflictsServiceClient struct {
	cc grpc.ClientConnInterface
}

func NewConflictsServiceClient(cc grpc.ClientConnInterface) ConflictsServiceClient {
	return &conflictsServiceClient{cc}
}

func (c *conflictsServiceClient) ListConflictFiles(ctx context.Context, in *ListConflictFilesRequest, opts ...grpc.CallOption) (ConflictsService_ListConflictFilesClient, error) {
	stream, err := c.cc.NewStream(ctx, &_ConflictsService_serviceDesc.Streams[0], "/degitx.ConflictsService/ListConflictFiles", opts...)
	if err != nil {
		return nil, err
	}
	x := &conflictsServiceListConflictFilesClient{stream}
	if err := x.ClientStream.SendMsg(in); err != nil {
		return nil, err
	}
	if err := x.ClientStream.CloseSend(); err != nil {
		return nil, err
	}
	return x, nil
}

type ConflictsService_ListConflictFilesClient interface {
	Recv() (*ListConflictFilesResponse, error)
	grpc.ClientStream
}

type conflictsServiceListConflictFilesClient struct {
	grpc.ClientStream
}

func (x *conflictsServiceListConflictFilesClient) Recv() (*ListConflictFilesResponse, error) {
	m := new(ListConflictFilesResponse)
	if err := x.ClientStream.RecvMsg(m); err != nil {
		return nil, err
	}
	return m, nil
}

func (c *conflictsServiceClient) ResolveConflicts(ctx context.Context, opts ...grpc.CallOption) (ConflictsService_ResolveConflictsClient, error) {
	stream, err := c.cc.NewStream(ctx, &_ConflictsService_serviceDesc.Streams[1], "/degitx.ConflictsService/ResolveConflicts", opts...)
	if err != nil {
		return nil, err
	}
	x := &conflictsServiceResolveConflictsClient{stream}
	return x, nil
}

type ConflictsService_ResolveConflictsClient interface {
	Send(*ResolveConflictsRequest) error
	CloseAndRecv() (*ResolveConflictsResponse, error)
	grpc.ClientStream
}

type conflictsServiceResolveConflictsClient struct {
	grpc.ClientStream
}

func (x *conflictsServiceResolveConflictsClient) Send(m *ResolveConflictsRequest) error {
	return x.ClientStream.SendMsg(m)
}

func (x *conflictsServiceResolveConflictsClient) CloseAndRecv() (*ResolveConflictsResponse, error) {
	if err := x.ClientStream.CloseSend(); err != nil {
		return nil, err
	}
	m := new(ResolveConflictsResponse)
	if err := x.ClientStream.RecvMsg(m); err != nil {
		return nil, err
	}
	return m, nil
}

// ConflictsServiceServer is the server API for ConflictsService service.
type ConflictsServiceServer interface {
	ListConflictFiles(*ListConflictFilesRequest, ConflictsService_ListConflictFilesServer) error
	ResolveConflicts(ConflictsService_ResolveConflictsServer) error
}

// UnimplementedConflictsServiceServer can be embedded to have forward compatible implementations.
type UnimplementedConflictsServiceServer struct {
}

func (*UnimplementedConflictsServiceServer) ListConflictFiles(*ListConflictFilesRequest, ConflictsService_ListConflictFilesServer) error {
	return status.Errorf(codes.Unimplemented, "method ListConflictFiles not implemented")
}
func (*UnimplementedConflictsServiceServer) ResolveConflicts(ConflictsService_ResolveConflictsServer) error {
	return status.Errorf(codes.Unimplemented, "method ResolveConflicts not implemented")
}

func RegisterConflictsServiceServer(s *grpc.Server, srv ConflictsServiceServer) {
	s.RegisterService(&_ConflictsService_serviceDesc, srv)
}

func _ConflictsService_ListConflictFiles_Handler(srv interface{}, stream grpc.ServerStream) error {
	m := new(ListConflictFilesRequest)
	if err := stream.RecvMsg(m); err != nil {
		return err
	}
	return srv.(ConflictsServiceServer).ListConflictFiles(m, &conflictsServiceListConflictFilesServer{stream})
}

type ConflictsService_ListConflictFilesServer interface {
	Send(*ListConflictFilesResponse) error
	grpc.ServerStream
}

type conflictsServiceListConflictFilesServer struct {
	grpc.ServerStream
}

func (x *conflictsServiceListConflictFilesServer) Send(m *ListConflictFilesResponse) error {
	return x.ServerStream.SendMsg(m)
}

func _ConflictsService_ResolveConflicts_Handler(srv interface{}, stream grpc.ServerStream) error {
	return srv.(ConflictsServiceServer).ResolveConflicts(&conflictsServiceResolveConflictsServer{stream})
}

type ConflictsService_ResolveConflictsServer interface {
	SendAndClose(*ResolveConflictsResponse) error
	Recv() (*ResolveConflictsRequest, error)
	grpc.ServerStream
}

type conflictsServiceResolveConflictsServer struct {
	grpc.ServerStream
}

func (x *conflictsServiceResolveConflictsServer) SendAndClose(m *ResolveConflictsResponse) error {
	return x.ServerStream.SendMsg(m)
}

func (x *conflictsServiceResolveConflictsServer) Recv() (*ResolveConflictsRequest, error) {
	m := new(ResolveConflictsRequest)
	if err := x.ServerStream.RecvMsg(m); err != nil {
		return nil, err
	}
	return m, nil
}

var _ConflictsService_serviceDesc = grpc.ServiceDesc{
	ServiceName: "degitx.ConflictsService",
	HandlerType: (*ConflictsServiceServer)(nil),
	Methods:     []grpc.MethodDesc{},
	Streams: []grpc.StreamDesc{
		{
			StreamName:    "ListConflictFiles",
			Handler:       _ConflictsService_ListConflictFiles_Handler,
			ServerStreams: true,
		},
		{
			StreamName:    "ResolveConflicts",
			Handler:       _ConflictsService_ResolveConflicts_Handler,
			ClientStreams: true,
		},
	},
	Metadata: "conflicts.proto",
}
