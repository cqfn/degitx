// MIT License. Copyright (c) 2020 CQFN
// https://github.com/cqfn/degitx/blob/master/LICENSE

// Package degitx provide a degitx server start point.
package degitx

import (
	"context"
	"log"

	"cqfn.org/degitx/discovery"
	"cqfn.org/degitx/gitaly/server"
	"cqfn.org/degitx/locators"
)

// Start DeGitX node or return error
func Start(
	ctx context.Context,
	node *locators.Node,
	disc discovery.Service,
	gitaly server.Server,
) error {
	log.Printf("Starting %s", node)

	if err := disc.Start(ctx); err != nil {
		return err
	}

	if err := gitaly.Start(ctx, node); err != nil {
		return err
	}
	return nil
}
