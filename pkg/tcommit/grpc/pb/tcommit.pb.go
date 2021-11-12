// Code generated by protoc-gen-go. DO NOT EDIT.
// versions:
// 	protoc-gen-go v1.27.1
// 	protoc        v3.17.3
// source: tcommit.proto

package pb

import (
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

// TxID is unique identifier of the transacion
type TxID struct {
	state         protoimpl.MessageState
	sizeCache     protoimpl.SizeCache
	unknownFields protoimpl.UnknownFields

	TxId string `protobuf:"bytes,1,opt,name=tx_id,json=txId,proto3" json:"tx_id,omitempty"`
}

func (x *TxID) Reset() {
	*x = TxID{}
	if protoimpl.UnsafeEnabled {
		mi := &file_tcommit_proto_msgTypes[0]
		ms := protoimpl.X.MessageStateOf(protoimpl.Pointer(x))
		ms.StoreMessageInfo(mi)
	}
}

func (x *TxID) String() string {
	return protoimpl.X.MessageStringOf(x)
}

func (*TxID) ProtoMessage() {}

func (x *TxID) ProtoReflect() protoreflect.Message {
	mi := &file_tcommit_proto_msgTypes[0]
	if protoimpl.UnsafeEnabled && x != nil {
		ms := protoimpl.X.MessageStateOf(protoimpl.Pointer(x))
		if ms.LoadMessageInfo() == nil {
			ms.StoreMessageInfo(mi)
		}
		return ms
	}
	return mi.MessageOf(x)
}

// Deprecated: Use TxID.ProtoReflect.Descriptor instead.
func (*TxID) Descriptor() ([]byte, []int) {
	return file_tcommit_proto_rawDescGZIP(), []int{0}
}

func (x *TxID) GetTxId() string {
	if x != nil {
		return x.TxId
	}
	return ""
}

// Vote of RM
type Vote struct {
	state         protoimpl.MessageState
	sizeCache     protoimpl.SizeCache
	unknownFields protoimpl.UnknownFields

	Vote uint32 `protobuf:"varint,1,opt,name=vote,proto3" json:"vote,omitempty"`
}

func (x *Vote) Reset() {
	*x = Vote{}
	if protoimpl.UnsafeEnabled {
		mi := &file_tcommit_proto_msgTypes[1]
		ms := protoimpl.X.MessageStateOf(protoimpl.Pointer(x))
		ms.StoreMessageInfo(mi)
	}
}

func (x *Vote) String() string {
	return protoimpl.X.MessageStringOf(x)
}

func (*Vote) ProtoMessage() {}

func (x *Vote) ProtoReflect() protoreflect.Message {
	mi := &file_tcommit_proto_msgTypes[1]
	if protoimpl.UnsafeEnabled && x != nil {
		ms := protoimpl.X.MessageStateOf(protoimpl.Pointer(x))
		if ms.LoadMessageInfo() == nil {
			ms.StoreMessageInfo(mi)
		}
		return ms
	}
	return mi.MessageOf(x)
}

// Deprecated: Use Vote.ProtoReflect.Descriptor instead.
func (*Vote) Descriptor() ([]byte, []int) {
	return file_tcommit_proto_rawDescGZIP(), []int{1}
}

func (x *Vote) GetVote() uint32 {
	if x != nil {
		return x.Vote
	}
	return 0
}

// Meta is an optional additional transaction metadata that could be sent by RM
// and used by TM.
type Meta struct {
	state         protoimpl.MessageState
	sizeCache     protoimpl.SizeCache
	unknownFields protoimpl.UnknownFields

	Meta string `protobuf:"bytes,1,opt,name=meta,proto3" json:"meta,omitempty"`
}

func (x *Meta) Reset() {
	*x = Meta{}
	if protoimpl.UnsafeEnabled {
		mi := &file_tcommit_proto_msgTypes[2]
		ms := protoimpl.X.MessageStateOf(protoimpl.Pointer(x))
		ms.StoreMessageInfo(mi)
	}
}

func (x *Meta) String() string {
	return protoimpl.X.MessageStringOf(x)
}

func (*Meta) ProtoMessage() {}

func (x *Meta) ProtoReflect() protoreflect.Message {
	mi := &file_tcommit_proto_msgTypes[2]
	if protoimpl.UnsafeEnabled && x != nil {
		ms := protoimpl.X.MessageStateOf(protoimpl.Pointer(x))
		if ms.LoadMessageInfo() == nil {
			ms.StoreMessageInfo(mi)
		}
		return ms
	}
	return mi.MessageOf(x)
}

// Deprecated: Use Meta.ProtoReflect.Descriptor instead.
func (*Meta) Descriptor() ([]byte, []int) {
	return file_tcommit_proto_rawDescGZIP(), []int{2}
}

func (x *Meta) GetMeta() string {
	if x != nil {
		return x.Meta
	}
	return ""
}

// Votes is a map of votes by node
type Votes struct {
	state         protoimpl.MessageState
	sizeCache     protoimpl.SizeCache
	unknownFields protoimpl.UnknownFields

	Votes map[string]*Vote `protobuf:"bytes,1,rep,name=votes,proto3" json:"votes,omitempty" protobuf_key:"bytes,1,opt,name=key,proto3" protobuf_val:"bytes,2,opt,name=value,proto3"`
}

func (x *Votes) Reset() {
	*x = Votes{}
	if protoimpl.UnsafeEnabled {
		mi := &file_tcommit_proto_msgTypes[3]
		ms := protoimpl.X.MessageStateOf(protoimpl.Pointer(x))
		ms.StoreMessageInfo(mi)
	}
}

func (x *Votes) String() string {
	return protoimpl.X.MessageStringOf(x)
}

func (*Votes) ProtoMessage() {}

func (x *Votes) ProtoReflect() protoreflect.Message {
	mi := &file_tcommit_proto_msgTypes[3]
	if protoimpl.UnsafeEnabled && x != nil {
		ms := protoimpl.X.MessageStateOf(protoimpl.Pointer(x))
		if ms.LoadMessageInfo() == nil {
			ms.StoreMessageInfo(mi)
		}
		return ms
	}
	return mi.MessageOf(x)
}

// Deprecated: Use Votes.ProtoReflect.Descriptor instead.
func (*Votes) Descriptor() ([]byte, []int) {
	return file_tcommit_proto_rawDescGZIP(), []int{3}
}

func (x *Votes) GetVotes() map[string]*Vote {
	if x != nil {
		return x.Votes
	}
	return nil
}

var File_tcommit_proto protoreflect.FileDescriptor

var file_tcommit_proto_rawDesc = []byte{
	0x0a, 0x0d, 0x74, 0x63, 0x6f, 0x6d, 0x6d, 0x69, 0x74, 0x2e, 0x70, 0x72, 0x6f, 0x74, 0x6f, 0x12,
	0x0e, 0x64, 0x65, 0x67, 0x69, 0x74, 0x78, 0x2e, 0x74, 0x63, 0x6f, 0x6d, 0x6d, 0x69, 0x74, 0x22,
	0x1b, 0x0a, 0x04, 0x54, 0x78, 0x49, 0x44, 0x12, 0x13, 0x0a, 0x05, 0x74, 0x78, 0x5f, 0x69, 0x64,
	0x18, 0x01, 0x20, 0x01, 0x28, 0x09, 0x52, 0x04, 0x74, 0x78, 0x49, 0x64, 0x22, 0x1a, 0x0a, 0x04,
	0x56, 0x6f, 0x74, 0x65, 0x12, 0x12, 0x0a, 0x04, 0x76, 0x6f, 0x74, 0x65, 0x18, 0x01, 0x20, 0x01,
	0x28, 0x0d, 0x52, 0x04, 0x76, 0x6f, 0x74, 0x65, 0x22, 0x1a, 0x0a, 0x04, 0x4d, 0x65, 0x74, 0x61,
	0x12, 0x12, 0x0a, 0x04, 0x6d, 0x65, 0x74, 0x61, 0x18, 0x01, 0x20, 0x01, 0x28, 0x09, 0x52, 0x04,
	0x6d, 0x65, 0x74, 0x61, 0x22, 0x8f, 0x01, 0x0a, 0x05, 0x56, 0x6f, 0x74, 0x65, 0x73, 0x12, 0x36,
	0x0a, 0x05, 0x76, 0x6f, 0x74, 0x65, 0x73, 0x18, 0x01, 0x20, 0x03, 0x28, 0x0b, 0x32, 0x20, 0x2e,
	0x64, 0x65, 0x67, 0x69, 0x74, 0x78, 0x2e, 0x74, 0x63, 0x6f, 0x6d, 0x6d, 0x69, 0x74, 0x2e, 0x56,
	0x6f, 0x74, 0x65, 0x73, 0x2e, 0x56, 0x6f, 0x74, 0x65, 0x73, 0x45, 0x6e, 0x74, 0x72, 0x79, 0x52,
	0x05, 0x76, 0x6f, 0x74, 0x65, 0x73, 0x1a, 0x4e, 0x0a, 0x0a, 0x56, 0x6f, 0x74, 0x65, 0x73, 0x45,
	0x6e, 0x74, 0x72, 0x79, 0x12, 0x10, 0x0a, 0x03, 0x6b, 0x65, 0x79, 0x18, 0x01, 0x20, 0x01, 0x28,
	0x09, 0x52, 0x03, 0x6b, 0x65, 0x79, 0x12, 0x2a, 0x0a, 0x05, 0x76, 0x61, 0x6c, 0x75, 0x65, 0x18,
	0x02, 0x20, 0x01, 0x28, 0x0b, 0x32, 0x14, 0x2e, 0x64, 0x65, 0x67, 0x69, 0x74, 0x78, 0x2e, 0x74,
	0x63, 0x6f, 0x6d, 0x6d, 0x69, 0x74, 0x2e, 0x56, 0x6f, 0x74, 0x65, 0x52, 0x05, 0x76, 0x61, 0x6c,
	0x75, 0x65, 0x3a, 0x02, 0x38, 0x01, 0x42, 0x25, 0x5a, 0x23, 0x63, 0x71, 0x66, 0x6e, 0x2e, 0x6f,
	0x72, 0x67, 0x2f, 0x64, 0x65, 0x67, 0x69, 0x74, 0x78, 0x2f, 0x70, 0x6b, 0x67, 0x2f, 0x74, 0x63,
	0x6f, 0x6d, 0x6d, 0x69, 0x74, 0x2f, 0x67, 0x72, 0x70, 0x63, 0x2f, 0x70, 0x62, 0x62, 0x06, 0x70,
	0x72, 0x6f, 0x74, 0x6f, 0x33,
}

var (
	file_tcommit_proto_rawDescOnce sync.Once
	file_tcommit_proto_rawDescData = file_tcommit_proto_rawDesc
)

func file_tcommit_proto_rawDescGZIP() []byte {
	file_tcommit_proto_rawDescOnce.Do(func() {
		file_tcommit_proto_rawDescData = protoimpl.X.CompressGZIP(file_tcommit_proto_rawDescData)
	})
	return file_tcommit_proto_rawDescData
}

var file_tcommit_proto_msgTypes = make([]protoimpl.MessageInfo, 5)
var file_tcommit_proto_goTypes = []interface{}{
	(*TxID)(nil),  // 0: degitx.tcommit.TxID
	(*Vote)(nil),  // 1: degitx.tcommit.Vote
	(*Meta)(nil),  // 2: degitx.tcommit.Meta
	(*Votes)(nil), // 3: degitx.tcommit.Votes
	nil,           // 4: degitx.tcommit.Votes.VotesEntry
}
var file_tcommit_proto_depIdxs = []int32{
	4, // 0: degitx.tcommit.Votes.votes:type_name -> degitx.tcommit.Votes.VotesEntry
	1, // 1: degitx.tcommit.Votes.VotesEntry.value:type_name -> degitx.tcommit.Vote
	2, // [2:2] is the sub-list for method output_type
	2, // [2:2] is the sub-list for method input_type
	2, // [2:2] is the sub-list for extension type_name
	2, // [2:2] is the sub-list for extension extendee
	0, // [0:2] is the sub-list for field type_name
}

func init() { file_tcommit_proto_init() }
func file_tcommit_proto_init() {
	if File_tcommit_proto != nil {
		return
	}
	if !protoimpl.UnsafeEnabled {
		file_tcommit_proto_msgTypes[0].Exporter = func(v interface{}, i int) interface{} {
			switch v := v.(*TxID); i {
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
		file_tcommit_proto_msgTypes[1].Exporter = func(v interface{}, i int) interface{} {
			switch v := v.(*Vote); i {
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
		file_tcommit_proto_msgTypes[2].Exporter = func(v interface{}, i int) interface{} {
			switch v := v.(*Meta); i {
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
		file_tcommit_proto_msgTypes[3].Exporter = func(v interface{}, i int) interface{} {
			switch v := v.(*Votes); i {
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
	type x struct{}
	out := protoimpl.TypeBuilder{
		File: protoimpl.DescBuilder{
			GoPackagePath: reflect.TypeOf(x{}).PkgPath(),
			RawDescriptor: file_tcommit_proto_rawDesc,
			NumEnums:      0,
			NumMessages:   5,
			NumExtensions: 0,
			NumServices:   0,
		},
		GoTypes:           file_tcommit_proto_goTypes,
		DependencyIndexes: file_tcommit_proto_depIdxs,
		MessageInfos:      file_tcommit_proto_msgTypes,
	}.Build()
	File_tcommit_proto = out.File
	file_tcommit_proto_rawDesc = nil
	file_tcommit_proto_goTypes = nil
	file_tcommit_proto_depIdxs = nil
}