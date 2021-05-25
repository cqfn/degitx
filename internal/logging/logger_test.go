// MIT License. Copyright (c) 2020 CQFN
// https://github.com/cqfn/degitx/blob/master/LICENSE

package logging

import (
	"testing"

	"cqfn.org/degitx/internal/locators"
	"github.com/stretchr/testify/assert"
)

func Test_log(t *testing.T) {
	node := locators.Node{
		ID: []byte{42, 42, 42},
	}
	cfg := LogConfig{
		Outputs: []Output{
			{
				Path: []string{
					"stdout",
				},
				Level:  "Debug",
				Format: "plain",
			},
			{
				Path: []string{
					"stdout",
				},
				Level:  "Error",
				Format: "json",
			},
		},
		ErrorsOut: []string{"stderr"},
	}
	Init(&node, &cfg)

	_, err := NewLogger("Discovery")
	assert.Nil(t, err)
}
