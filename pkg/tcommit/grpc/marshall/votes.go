// MIT License. Copyright (c) 2020 CQFN
// https://github.com/cqfn/degitx/blob/master/LICENSE

// Package marshall converts structs from proto definitions
// to the application one and vise versa
package marshall

import (
	"errors"

	"cqfn.org/degitx/pkg/tcommit"
	"cqfn.org/degitx/pkg/tcommit/grpc/pb"
)

// ErrVoteValueOutOfRange is thrown in case if the proto value is bigger than uint8
var (
	ErrVoteValueOutOfRange = errors.New("vote value out of range")
	ErrEmptyVotes          = errors.New("empty votes")
)

// FromProtoVotes converts the proto definition of Votes to the application one
func FromProtoVotes(votes *pb.Votes) (tcommit.Votes, error) {
	if votes == nil {
		return nil, ErrEmptyVotes
	}

	if len(votes.GetVotes()) == 0 {
		return nil, ErrEmptyVotes
	}

	result := tcommit.Votes{}

	for n, v := range votes.GetVotes() {
		vote := tcommit.Vote(v.GetVote())

		if uint32(vote) != v.GetVote() {
			return nil, ErrVoteValueOutOfRange
		}

		if err := vote.Validate(); err != nil {
			return nil, err
		}

		node := tcommit.NodeID(n)
		result[node] = vote
	}

	return result, nil
}

// ToProtoVotes converts the application's Votes to the proto one
// The opposite of the FromProtoVotes
func ToProtoVotes(votes tcommit.Votes) *pb.Votes {
	result := &pb.Votes{
		Votes: make(map[string]*pb.Vote, len(votes)),
	}

	for n, v := range votes {
		result.Votes[string(n)] = &pb.Vote{Vote: uint32(v)}
	}

	return result
}
