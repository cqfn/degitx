// MIT License. Copyright (c) 2020 CQFN
// https://github.com/cqfn/degitx/blob/master/LICENSE

// Package test contains helpers functions for running tests
package test

import (
	"context"
	"log"
	"net"

	"google.golang.org/grpc"
	"google.golang.org/grpc/test/bufconn"
)

// StartServer start gRPC server, prepeare connection for clients and register services
func StartServer(ctx context.Context, register func(*grpc.Server)) (*grpc.Server, *grpc.ClientConn) {
	const bufSize = 1024 * 1024

	lis := bufconn.Listen(bufSize)
	srv := grpc.NewServer()

	register(srv)

	go func() {
		if err := srv.Serve(lis); err != nil {
			log.Fatalf("failed to start gRPC server: %v", err)
		}
	}()

	dialer := grpc.WithContextDialer(func(_ context.Context, _ string) (net.Conn, error) {
		return lis.Dial()
	})
	conn, err := grpc.DialContext(ctx, "", grpc.WithInsecure(), dialer)
	if err != nil {
		log.Fatalf("failed to dial: %v", err)
	}

	return srv, conn
}
