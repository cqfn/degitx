// MIT License. Copyright (c) 2020 CQFN
// https://github.com/cqfn/degitx/blob/master/LICENSE

// Package meta provides interfaces and implementations to work
// with metadata protocol of DeGitX, metadata structure is an
// abstract key-value storage.
package meta

import (
	"context"
	"fmt"
	"sync"
	"time"
)

// Data - alias for immutable bytes representation with helper methods
type Data string

var noData = Data("") //nolint:gochecknoglobals //empty constant

// Slice returns metadata slice of immutable byte array
func (md Data) Slice() []byte {
	return []byte(md)
}

// MetaResponse - type of metadata storage response
type MetaResponse struct {
	// Key of metadata response
	Key string
	// Value of metadata
	Value Data
	// Error on failure
	Error error
}

// ErrNotFound returned if a value for key was not found
type ErrNotFound struct {
	Key string
}

func (e *ErrNotFound) Error() string {
	return fmt.Sprintf("Value for key `%s` was not found", e.Key)
}

// Storage - interface of metadata storage with async operations
type Storage interface {
	// Get returns a channel with single response item,
	// channel is closed on context cancellation. Context
	// shold be cancelled with defer.
	Get(ctx context.Context, key string) <-chan MetaResponse
	// Set updates metadata storage, channel with a
	// value is returned on success, a value could differ from
	// provided value, if storage received new value after this request
	// but before response. Channel is closed on context
	// cancellation. Context should be cancelled with defer.
	Set(ctx context.Context, key string, val Data) <-chan MetaResponse
}

// NewInMemStorage creates metadata storage in memory, useful for testing
func NewInMemStorage() Storage {
	return &mapStorage{make(map[string]Data), new(sync.RWMutex)}
}

type mapStorage struct {
	mem map[string]Data
	mux *sync.RWMutex
}

func (s *mapStorage) Get(ctx context.Context, key string) <-chan MetaResponse {
	ch := make(chan MetaResponse)
	go func() {
		var rsp MetaResponse
		s.mux.RLock()
		if val, ok := s.mem[key]; ok {
			rsp = MetaResponse{key, val, nil}
		} else {
			rsp = MetaResponse{key, noData, &ErrNotFound{key}}
		}
		s.mux.RUnlock()
		ch <- rsp
		<-ctx.Done()
		close(ch)
	}()
	return ch
}

func (s *mapStorage) Set(ctx context.Context, key string, val Data) <-chan MetaResponse {
	ch := make(chan MetaResponse)
	go func() {
		s.mux.Lock()
		if val == noData {
			delete(s.mem, key)
		} else {
			s.mem[key] = val
		}
		s.mux.Unlock()
		ch <- MetaResponse{key, val, nil}
		<-ctx.Done()
		close(ch)
	}()
	return ch
}

// StandardTimeout of blocking operations
const StandardTimeout = 30 * time.Second

// GetSync fetches metadata value from remote storage and blocks execution
// with standard timeout to return metadata values
func GetSync(meta Storage, key string) (Data, error) {
	ctx, cancel := context.WithTimeout(context.Background(), StandardTimeout)
	defer cancel()
	resp := <-meta.Get(ctx, key)
	return resp.Value, resp.Error
}

// SetSync updates metadata storage with new value for key and blocks execution
// with standard timeout.
func SetSync(meta Storage, key string, value Data) error {
	ctx, cancel := context.WithTimeout(context.Background(), StandardTimeout)
	defer cancel()
	resp := <-meta.Set(ctx, key, value)
	return resp.Error
}
