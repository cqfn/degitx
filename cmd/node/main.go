// MIT License. Copyright (c) 2020 CQFN
// https://github.com/cqfn/degitx/blob/master/LICENSE

package main

import (
	"log"
	"os"

	"github.com/urfave/cli/v2"

	"org.cqfn/degitx"
)

func main() {
	app := cli.App{
		Name:        "degitx",
		Usage:       "Manage degit node",
		Description: "DeGitX node CLI",
		Commands: []*cli.Command{
			{
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
	degitx.Start()
	return nil
}
