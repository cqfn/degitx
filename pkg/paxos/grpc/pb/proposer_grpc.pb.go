// Code generated by protoc-gen-go-grpc. DO NOT EDIT.
// versions:
// - protoc-gen-go-grpc v1.1.0
// - protoc             v3.17.3
// source: proposer.proto

package pb

import (
	context "context"
	grpc "google.golang.org/grpc"
	codes "google.golang.org/grpc/codes"
	status "google.golang.org/grpc/status"
)

// This is a compile-time assertion to ensure that this generated file
// is compatible with the grpc package it is being compiled against.
// Requires gRPC-Go v1.32.0 or later.
const _ = grpc.SupportPackageIsVersion7

// ProposerServiceClient is the client API for ProposerService service.
//
// For semantics around ctx use and closing/ending streaming RPCs, please refer to https://pkg.go.dev/google.golang.org/grpc/?tab=doc#ClientConn.NewStream.
type ProposerServiceClient interface {
	// Promise message
	Promise(ctx context.Context, in *PromiseRequest, opts ...grpc.CallOption) (*PromiseResponse, error)
	// Accepted message
	Accepted(ctx context.Context, in *AcceptedRequest, opts ...grpc.CallOption) (*AcceptedResponse, error)
	// Reject message
	Reject(ctx context.Context, in *RejectRequest, opts ...grpc.CallOption) (*RejectResponse, error)
}

type proposerServiceClient struct {
	cc grpc.ClientConnInterface
}

func NewProposerServiceClient(cc grpc.ClientConnInterface) ProposerServiceClient {
	return &proposerServiceClient{cc}
}

func (c *proposerServiceClient) Promise(ctx context.Context, in *PromiseRequest, opts ...grpc.CallOption) (*PromiseResponse, error) {
	out := new(PromiseResponse)
	err := c.cc.Invoke(ctx, "/degitx.paxos.ProposerService/Promise", in, out, opts...)
	if err != nil {
		return nil, err
	}
	return out, nil
}

func (c *proposerServiceClient) Accepted(ctx context.Context, in *AcceptedRequest, opts ...grpc.CallOption) (*AcceptedResponse, error) {
	out := new(AcceptedResponse)
	err := c.cc.Invoke(ctx, "/degitx.paxos.ProposerService/Accepted", in, out, opts...)
	if err != nil {
		return nil, err
	}
	return out, nil
}

func (c *proposerServiceClient) Reject(ctx context.Context, in *RejectRequest, opts ...grpc.CallOption) (*RejectResponse, error) {
	out := new(RejectResponse)
	err := c.cc.Invoke(ctx, "/degitx.paxos.ProposerService/Reject", in, out, opts...)
	if err != nil {
		return nil, err
	}
	return out, nil
}

// ProposerServiceServer is the server API for ProposerService service.
// All implementations must embed UnimplementedProposerServiceServer
// for forward compatibility
type ProposerServiceServer interface {
	// Promise message
	Promise(context.Context, *PromiseRequest) (*PromiseResponse, error)
	// Accepted message
	Accepted(context.Context, *AcceptedRequest) (*AcceptedResponse, error)
	// Reject message
	Reject(context.Context, *RejectRequest) (*RejectResponse, error)
	mustEmbedUnimplementedProposerServiceServer()
}

// UnimplementedProposerServiceServer must be embedded to have forward compatible implementations.
type UnimplementedProposerServiceServer struct {
}

func (UnimplementedProposerServiceServer) Promise(context.Context, *PromiseRequest) (*PromiseResponse, error) {
	return nil, status.Errorf(codes.Unimplemented, "method Promise not implemented")
}
func (UnimplementedProposerServiceServer) Accepted(context.Context, *AcceptedRequest) (*AcceptedResponse, error) {
	return nil, status.Errorf(codes.Unimplemented, "method Accepted not implemented")
}
func (UnimplementedProposerServiceServer) Reject(context.Context, *RejectRequest) (*RejectResponse, error) {
	return nil, status.Errorf(codes.Unimplemented, "method Reject not implemented")
}
func (UnimplementedProposerServiceServer) mustEmbedUnimplementedProposerServiceServer() {}

// UnsafeProposerServiceServer may be embedded to opt out of forward compatibility for this service.
// Use of this interface is not recommended, as added methods to ProposerServiceServer will
// result in compilation errors.
type UnsafeProposerServiceServer interface {
	mustEmbedUnimplementedProposerServiceServer()
}

func RegisterProposerServiceServer(s grpc.ServiceRegistrar, srv ProposerServiceServer) {
	s.RegisterService(&ProposerService_ServiceDesc, srv)
}

func _ProposerService_Promise_Handler(srv interface{}, ctx context.Context, dec func(interface{}) error, interceptor grpc.UnaryServerInterceptor) (interface{}, error) {
	in := new(PromiseRequest)
	if err := dec(in); err != nil {
		return nil, err
	}
	if interceptor == nil {
		return srv.(ProposerServiceServer).Promise(ctx, in)
	}
	info := &grpc.UnaryServerInfo{
		Server:     srv,
		FullMethod: "/degitx.paxos.ProposerService/Promise",
	}
	handler := func(ctx context.Context, req interface{}) (interface{}, error) {
		return srv.(ProposerServiceServer).Promise(ctx, req.(*PromiseRequest))
	}
	return interceptor(ctx, in, info, handler)
}

func _ProposerService_Accepted_Handler(srv interface{}, ctx context.Context, dec func(interface{}) error, interceptor grpc.UnaryServerInterceptor) (interface{}, error) {
	in := new(AcceptedRequest)
	if err := dec(in); err != nil {
		return nil, err
	}
	if interceptor == nil {
		return srv.(ProposerServiceServer).Accepted(ctx, in)
	}
	info := &grpc.UnaryServerInfo{
		Server:     srv,
		FullMethod: "/degitx.paxos.ProposerService/Accepted",
	}
	handler := func(ctx context.Context, req interface{}) (interface{}, error) {
		return srv.(ProposerServiceServer).Accepted(ctx, req.(*AcceptedRequest))
	}
	return interceptor(ctx, in, info, handler)
}

func _ProposerService_Reject_Handler(srv interface{}, ctx context.Context, dec func(interface{}) error, interceptor grpc.UnaryServerInterceptor) (interface{}, error) {
	in := new(RejectRequest)
	if err := dec(in); err != nil {
		return nil, err
	}
	if interceptor == nil {
		return srv.(ProposerServiceServer).Reject(ctx, in)
	}
	info := &grpc.UnaryServerInfo{
		Server:     srv,
		FullMethod: "/degitx.paxos.ProposerService/Reject",
	}
	handler := func(ctx context.Context, req interface{}) (interface{}, error) {
		return srv.(ProposerServiceServer).Reject(ctx, req.(*RejectRequest))
	}
	return interceptor(ctx, in, info, handler)
}

// ProposerService_ServiceDesc is the grpc.ServiceDesc for ProposerService service.
// It's only intended for direct use with grpc.RegisterService,
// and not to be introspected or modified (even as a copy)
var ProposerService_ServiceDesc = grpc.ServiceDesc{
	ServiceName: "degitx.paxos.ProposerService",
	HandlerType: (*ProposerServiceServer)(nil),
	Methods: []grpc.MethodDesc{
		{
			MethodName: "Promise",
			Handler:    _ProposerService_Promise_Handler,
		},
		{
			MethodName: "Accepted",
			Handler:    _ProposerService_Accepted_Handler,
		},
		{
			MethodName: "Reject",
			Handler:    _ProposerService_Reject_Handler,
		},
	},
	Streams:  []grpc.StreamDesc{},
	Metadata: "proposer.proto",
}
