// MIT License. Copyright (c) 2020 CQFN
// https://github.com/cqfn/degitx/blob/master/LICENSE

package paxos

import (
	"cqfn.org/degitx/pkg/tcommit"
	"github.com/g4s8/go-bundle"
)

var _ binVotes

type binVotes map[tcommit.NodeID]tcommit.Vote

func (bv binVotes) MarshalBinary() (data []byte, err error) {
	out := bundle.NewBEOut()
	src := map[tcommit.NodeID]tcommit.Vote(bv)
	out.PutInt32(int32(len(src)))
	for k, v := range src {
		out.PutString(string(k))
		out.PutUInt8(uint8(v))
	}
	return out.MarshalBinary()
}

func (bv binVotes) UnmarshalBinary(data []byte) error {
	inp := bundle.NewBEInput()
	if err := inp.UnmarshalBinary(data); err != nil {
		return err
	}
	var size int32
	inp.GetInt32(&size)
	src := make(map[string]uint8)
	var i int32
	var key string
	var val uint8
	for i = 0; i < size; i++ {
		inp.GetString(&key)
		inp.GetUInt8(&val)
		src[key] = val
	}
	if err := inp.Error(); err != nil {
		return err
	}
	for k, v := range src {
		bv[tcommit.NodeID(k)] = tcommit.Vote(v)
	}
	return nil
}
