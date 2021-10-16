// MIT License. Copyright (c) 2020 CQFN
// https://github.com/cqfn/degitx/blob/master/LICENSE

package marshall

import (
	"testing"

	"cqfn.org/degitx/pkg/tcommit"
	"cqfn.org/degitx/pkg/tcommit/grpc/pb"
	"github.com/stretchr/testify/assert"
)

func TestFromProtoVotes_empty(t *testing.T) {
	votes := &pb.Votes{}

	result, err := FromProtoVotes(votes)

	assert.EqualError(t, err, "empty votes")
	assert.Nil(t, result)
}

func TestFromProtoVotes_nil(t *testing.T) {
	result, err := FromProtoVotes(nil)

	assert.EqualError(t, err, "empty votes")
	assert.Nil(t, result)
}

func TestFromProtoVotes(t *testing.T) {
	votes := &pb.Votes{
		Votes: map[string]*pb.Vote{
			"1.1": {Vote: 0},
			"1.2": {Vote: 1},
			"1.3": {Vote: 2},
		},
	}

	result, err := FromProtoVotes(votes)

	assert.NoError(t, err)
	assert.Equal(t, tcommit.Votes{
		"1.1": tcommit.VoteUnkown,
		"1.2": tcommit.VotePrepared,
		"1.3": tcommit.VoteAborted,
	}, result)
}

func TestFromProtoVotes_invalidVoteType(t *testing.T) {
	votes := &pb.Votes{
		Votes: map[string]*pb.Vote{
			"1.1": {Vote: 10},
		},
	}

	result, err := FromProtoVotes(votes)

	assert.EqualError(t, err, "invalid Vote")
	assert.Nil(t, result)
}

func TestFromProtoVotes_overflow(t *testing.T) {
	votes := &pb.Votes{
		Votes: map[string]*pb.Vote{
			"1.1": {Vote: 65536},
		},
	}

	result, err := FromProtoVotes(votes)

	assert.EqualError(t, err, "vote value out of range")
	assert.Nil(t, result)
}

func TestToProtoVotes_empty(t *testing.T) {
	votes := tcommit.Votes{}

	result := ToProtoVotes(votes)

	assert.Equal(t, &pb.Votes{
		Votes: make(map[string]*pb.Vote),
	}, result)
}

func TestToProtoVotes(t *testing.T) {
	votes := tcommit.Votes{
		"1.1": tcommit.VoteUnkown,
		"1.2": tcommit.VotePrepared,
		"1.3": tcommit.VoteAborted,
	}

	result := ToProtoVotes(votes)

	assert.Equal(t, &pb.Votes{
		Votes: map[string]*pb.Vote{
			"1.1": {Vote: 0},
			"1.2": {Vote: 1},
			"1.3": {Vote: 2},
		},
	}, result)
}
