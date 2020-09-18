// MIT License. Copyright (c) 2020 CQFN
// https://github.com/cqfn/degitx/blob/master/LICENSE

package main

import (
	"github.com/urfave/cli/v2"
	"log"
	"org.cqfn/degitx"
	"os"
)

func main() {
	app := cli.App{
		Name:        "degitx",
		Usage:       "Manage degit node",
		Description: "DeGitX node CLI",
		Commands: []*cli.Command{
			&cli.Command{
				Name:    "run",
				Aliases: []string{"r"},
				Usage:   "run the node",
				Action:  cmdRun,
			},
		},
	}
	if err := app.Run(os.Args); err != nil {
		log.Fatalf("App failed: %s", err)
	}
}

func cmdRun(ctx *cli.Context) error {
	degitx.Stub()
	return nil
}
