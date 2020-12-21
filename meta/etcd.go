// MIT License. Copyright (c) 2020 CQFN
// https://github.com/cqfn/degitx/blob/master/LICENSE

package meta

import (
	"context"
	"time"

	"cqfn.org/degitx/misc"

	"go.etcd.io/etcd/clientv3"
)

const etcdConTimeout = time.Second * 5

type etcd struct {
	client *clientv3.Client
}

// NewEtcd creates new Storage, that encapsulates official etcd client
func NewEtcd(ctx context.Context, endpoints ...string) (Storage, error) {
	client, err := clientv3.New(clientv3.Config{
		Endpoints:   endpoints,
		DialTimeout: etcdConTimeout,
	})
	if err != nil {
		return nil, err
	}

	go func() {
		select { //nolint:gosimple // Done is provided for use in select statements
		case <-ctx.Done():
			misc.CloseWithLog(client)
		}
	}()

	return &etcd{client}, nil
}

// See Storage.Get
func (storage *etcd) Get(ctx context.Context, key string) <-chan *Response {
	return storage.callEtcd(ctx,
		func(ctx context.Context, out chan<- *Response) {
			rsp := new(Response)
			get, err := storage.client.Get(ctx, key)
			if err != nil {
				rsp.Error = err
			} else if len(get.Kvs) > 0 {
				rsp.Key = string(get.Kvs[0].Key)
				rsp.Value = Data(get.Kvs[0].Value)
			}
			select {
			case out <- rsp:
			case <-ctx.Done():
				rsp.Error = ctx.Err()
				rsp.Value = noData
			}
			close(out)
		})
}

// See Storage.Set
func (storage *etcd) Set(ctx context.Context, key string, val Data) <-chan *Response {
	return storage.callEtcd(ctx,
		func(ctx context.Context, out chan<- *Response) {
			rsp := new(Response)
			_, err := storage.client.Put(ctx, key, string(val))
			if err != nil {
				rsp.Error = err
			} else {
				// etcd ensures linearizability for all operations except watch operations
				rsp.Key = key
				rsp.Value = val
			}
			select {
			case out <- rsp:
			case <-ctx.Done():
				rsp.Error = ctx.Err()
				rsp.Value = noData
			}
			close(out)
		})
}

func (storage *etcd) callEtcd(
	ctx context.Context,
	query func(ctx context.Context, out chan<- *Response),
) <-chan *Response {
	ctx, cancel := context.WithTimeout(ctx, etcdConTimeout)
	defer cancel()
	out := make(chan *Response)
	query(ctx, out)
	return out
}
