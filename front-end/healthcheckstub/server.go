// MIT License. Copyright (c) 2020 CQFN
// https://github.com/cqfn/degitx/blob/master/LICENSE

// Package healthcheckstub emulates healthcheck
// to allow gitlab to start with degitx that has unimplemented methods.
package healthcheckstub

import (
	"context"

	"cqfn.org/degitx/logging"
	healthpb "google.golang.org/grpc/health/grpc_health_v1"
)

type server struct {
	log *logging.Logger
}

func NewServer(log *logging.Logger) healthpb.HealthServer {
	return &server{
		log: log,
	}
}

func (s server) Check(
	_ context.Context,
	_ *healthpb.HealthCheckRequest,
) (*healthpb.HealthCheckResponse, error) {
	return &healthpb.HealthCheckResponse{
			Status: healthpb.HealthCheckResponse_SERVING,
		},
		nil
}

func (s server) Watch(
	_ *healthpb.HealthCheckRequest,
	_ healthpb.Health_WatchServer,
) error {
	return nil
}
