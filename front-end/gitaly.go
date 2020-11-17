// MIT License. Copyright (c) 2020 CQFN
// https://github.com/cqfn/degitx/blob/master/LICENSE

// Package frontend provides a gitaly-like front-end server start point
// and contains all all front-end specific code.
package frontend

import (
	"context"
	"log"

	"cqfn.org/degitx/front-end/gitaly/server"
)

// Start DeGitX node or return error
func Start(
	ctx context.Context,
	gitaly server.Server,
) error {
	log.Printf("Starting Gitaly-like front end")

	if err := gitaly.Start(ctx); err != nil {
		return err
	}
	return nil
}
