// MIT License. Copyright (c) 2020 CQFN
// https://github.com/cqfn/degitx/blob/master/LICENSE

// Package discovery provides discovery protocol interfaces
// and its implementations.
// The main API are:
//   - `Discovery` - provides all API for discovery protocol,
//   such as resolving peer addresses by locator IDs.
//   It keeps local peers table in sync, it checks the local table
//   before query remote providers, and update it on success lookup.
//   It can be created using `NewDiscovery` factory function.
//   - `Provider` - remote discovery provider API,
//   It performs query lookup operation in any remote kind of storage,
//   E.g. it may have implementations for database, etcd, DHT, etc.
//   - `ErrNotFound` - error returned when peer was not found. The error
//   can be checked with `errors.As(err, &notFound)`.
//   - `ErrFailedToResolve` - generic error wrapper, encapsulates
//   more concrete errors, to get caused errors use `errors.Unwrap`
//   or `errors.As()`
package discovery
