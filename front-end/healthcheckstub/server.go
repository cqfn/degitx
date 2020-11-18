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

/**
 * @todo #74 Implement health check
 * When all services will be ready, we shall remove this stub type & package
 * and implement real health check correctly: return SERVING only if checks passed.
 */
type serverStub struct {
	log *logging.Logger
}

func NewServer(log *logging.Logger) healthpb.HealthServer {
	return &serverStub{
		log: log,
	}
}

func (s serverStub) Check(
	_ context.Context,
	_ *healthpb.HealthCheckRequest,
) (*healthpb.HealthCheckResponse, error) {
	return &healthpb.HealthCheckResponse{
			Status: healthpb.HealthCheckResponse_SERVING,
		},
		nil
}

func (s serverStub) Watch(
	_ *healthpb.HealthCheckRequest,
	_ healthpb.Health_WatchServer,
) error {
	return nil
}
