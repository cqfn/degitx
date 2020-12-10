// MIT License. Copyright (c) 2020 CQFN
// https://github.com/cqfn/degitx/blob/master/LICENSE

package meta

import (
	"context"
	"time"

	"cqfn.org/degitx/discovery"
	"cqfn.org/degitx/misc"

	ma "github.com/multiformats/go-multiaddr"
	"go.etcd.io/etcd/clientv3"
)

type etcd struct {
	Endpoints []string
}

func NewEtcd(endpoints ...string) (Storage, error) {
	var urls []string
	for _, endpoint := range endpoints {
		multiaddr, err := ma.NewMultiaddr(endpoint)
		if err != nil {
			return nil, err
		}
		addr := new(discovery.MaNetworkAddr)
		if err := addr.Parse(multiaddr); err != nil { //nolint:dupl // just parsing an address
			return nil, err
		}
		urls = append(urls, addr.String())
	}

	return &etcd{
			Endpoints: urls,
		},
		nil
}

const conTimeout = time.Second * 5

func (storage *etcd) Get(ctx context.Context, key string) <-chan MetaResponse {
	return storage.callEtcd(ctx,
		func(ctx context.Context, client *clientv3.Client, response *MetaResponse) {
			get, err := client.Get(ctx, key)
			if err != nil {
				response.Error = err
			} else if len(get.Kvs) > 0 {
				response.Key = string(get.Kvs[0].Key)
				response.Value = Data(get.Kvs[0].Value)
			}
		})
}

func (storage *etcd) Set(ctx context.Context, key string, val Data) <-chan MetaResponse {
	return storage.callEtcd(ctx,
		func(ctx context.Context, client *clientv3.Client, response *MetaResponse) {
			_, err := client.Put(ctx, key, string(val))
			if err != nil {
				response.Error = err
			} else {
				//etcd ensures linearizability for all operations except watch operations
				response.Key = key
				response.Value = val
			}
		})
}

func (storage *etcd) callEtcd(
	ctx context.Context,
	query func(ctx context.Context, client *clientv3.Client, response *MetaResponse),
) <-chan MetaResponse {

	client, err := clientv3.New(clientv3.Config{
		Endpoints:   storage.Endpoints,
		DialTimeout: conTimeout,
	})
	if err != nil {
		return nil //todo return an error somehow
	}
	defer misc.CloseWithLog(client)

	ctx, cancel := context.WithTimeout(ctx, conTimeout)
	defer cancel()

	out := make(chan MetaResponse)

	go func() {
		select {
		case <-ctx.Done():
			close(out)
		}
	}()

	response := &MetaResponse{}
	query(ctx, client, response)
	out <- *response
	return out
}
