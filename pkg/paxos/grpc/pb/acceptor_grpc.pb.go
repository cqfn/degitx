// Code generated by protoc-gen-go-grpc. DO NOT EDIT.
// versions:
// - protoc-gen-go-grpc v1.1.0
// - protoc             v3.17.3
// source: acceptor.proto

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

// AcceptorServiceClient is the client API for AcceptorService service.
//
// For semantics around ctx use and closing/ending streaming RPCs, please refer to https://pkg.go.dev/google.golang.org/grpc/?tab=doc#ClientConn.NewStream.
type AcceptorServiceClient interface {
	// Prepare message
	Prepare(ctx context.Context, in *PrepareRequest, opts ...grpc.CallOption) (*PrepareResponse, error)
	// Accept message
	Accept(ctx context.Context, in *AcceptRequest, opts ...grpc.CallOption) (*AcceptResponse, error)
}

type acceptorServiceClient struct {
	cc grpc.ClientConnInterface
}

func NewAcceptorServiceClient(cc grpc.ClientConnInterface) AcceptorServiceClient {
	return &acceptorServiceClient{cc}
}

func (c *acceptorServiceClient) Prepare(ctx context.Context, in *PrepareRequest, opts ...grpc.CallOption) (*PrepareResponse, error) {
	out := new(PrepareResponse)
	err := c.cc.Invoke(ctx, "/degitx.paxos.AcceptorService/Prepare", in, out, opts...)
	if err != nil {
		return nil, err
	}
	return out, nil
}

func (c *acceptorServiceClient) Accept(ctx context.Context, in *AcceptRequest, opts ...grpc.CallOption) (*AcceptResponse, error) {
	out := new(AcceptResponse)
	err := c.cc.Invoke(ctx, "/degitx.paxos.AcceptorService/Accept", in, out, opts...)
	if err != nil {
		return nil, err
	}
	return out, nil
}

// AcceptorServiceServer is the server API for AcceptorService service.
// All implementations must embed UnimplementedAcceptorServiceServer
// for forward compatibility
type AcceptorServiceServer interface {
	// Prepare message
	Prepare(context.Context, *PrepareRequest) (*PrepareResponse, error)
	// Accept message
	Accept(context.Context, *AcceptRequest) (*AcceptResponse, error)
	mustEmbedUnimplementedAcceptorServiceServer()
}

// UnimplementedAcceptorServiceServer must be embedded to have forward compatible implementations.
type UnimplementedAcceptorServiceServer struct {
}

func (UnimplementedAcceptorServiceServer) Prepare(context.Context, *PrepareRequest) (*PrepareResponse, error) {
	return nil, status.Errorf(codes.Unimplemented, "method Prepare not implemented")
}
func (UnimplementedAcceptorServiceServer) Accept(context.Context, *AcceptRequest) (*AcceptResponse, error) {
	return nil, status.Errorf(codes.Unimplemented, "method Accept not implemented")
}
func (UnimplementedAcceptorServiceServer) mustEmbedUnimplementedAcceptorServiceServer() {}

// UnsafeAcceptorServiceServer may be embedded to opt out of forward compatibility for this service.
// Use of this interface is not recommended, as added methods to AcceptorServiceServer will
// result in compilation errors.
type UnsafeAcceptorServiceServer interface {
	mustEmbedUnimplementedAcceptorServiceServer()
}

func RegisterAcceptorServiceServer(s grpc.ServiceRegistrar, srv AcceptorServiceServer) {
	s.RegisterService(&AcceptorService_ServiceDesc, srv)
}

func _AcceptorService_Prepare_Handler(srv interface{}, ctx context.Context, dec func(interface{}) error, interceptor grpc.UnaryServerInterceptor) (interface{}, error) {
	in := new(PrepareRequest)
	if err := dec(in); err != nil {
		return nil, err
	}
	if interceptor == nil {
		return srv.(AcceptorServiceServer).Prepare(ctx, in)
	}
	info := &grpc.UnaryServerInfo{
		Server:     srv,
		FullMethod: "/degitx.paxos.AcceptorService/Prepare",
	}
	handler := func(ctx context.Context, req interface{}) (interface{}, error) {
		return srv.(AcceptorServiceServer).Prepare(ctx, req.(*PrepareRequest))
	}
	return interceptor(ctx, in, info, handler)
}

func _AcceptorService_Accept_Handler(srv interface{}, ctx context.Context, dec func(interface{}) error, interceptor grpc.UnaryServerInterceptor) (interface{}, error) {
	in := new(AcceptRequest)
	if err := dec(in); err != nil {
		return nil, err
	}
	if interceptor == nil {
		return srv.(AcceptorServiceServer).Accept(ctx, in)
	}
	info := &grpc.UnaryServerInfo{
		Server:     srv,
		FullMethod: "/degitx.paxos.AcceptorService/Accept",
	}
	handler := func(ctx context.Context, req interface{}) (interface{}, error) {
		return srv.(AcceptorServiceServer).Accept(ctx, req.(*AcceptRequest))
	}
	return interceptor(ctx, in, info, handler)
}

// AcceptorService_ServiceDesc is the grpc.ServiceDesc for AcceptorService service.
// It's only intended for direct use with grpc.RegisterService,
// and not to be introspected or modified (even as a copy)
var AcceptorService_ServiceDesc = grpc.ServiceDesc{
	ServiceName: "degitx.paxos.AcceptorService",
	HandlerType: (*AcceptorServiceServer)(nil),
	Methods: []grpc.MethodDesc{
		{
			MethodName: "Prepare",
			Handler:    _AcceptorService_Prepare_Handler,
		},
		{
			MethodName: "Accept",
			Handler:    _AcceptorService_Accept_Handler,
		},
	},
	Streams:  []grpc.StreamDesc{},
	Metadata: "acceptor.proto",
}
