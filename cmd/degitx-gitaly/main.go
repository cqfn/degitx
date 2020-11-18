// MIT License. Copyright (c) 2020 CQFN
// https://github.com/cqfn/degitx/blob/master/LICENSE

package main

import (
	"log"
	"os"

	frontend "cqfn.org/degitx/front-end"
	"cqfn.org/degitx/front-end/gitaly/server"
	"cqfn.org/degitx/internal/config"
	"cqfn.org/degitx/logging"

	ma "github.com/multiformats/go-multiaddr"
	"github.com/urfave/cli/v2"
)

func main() {
	app := cli.App{
		Name:        "Gitaly-like front-end",
		Usage:       "Manage degitx front-end",
		Description: "DeGitX front-end CLI",
		Flags: []cli.Flag{
			&cli.StringFlag{
				Name:     "config",
				Aliases:  []string{"c"},
				Usage:    "configuration file path",
				Required: true,
			},
		},
		Commands: []*cli.Command{
			{
				Name:    "run",
				Aliases: []string{"r"},
				Usage:   "run front-end",
				Action:  cmdRun,
				Flags: []cli.Flag{
					&cli.StringFlag{
						Name:     "host",
						Usage:    "Gitaly gRPC API host and port",
						Required: true,
					},
				},
			},
		},
	}
	if err := app.Run(os.Args); err != nil {
		log.Fatalf("App failed: %s", err)
	}
}

const pConfigUser = "${HOME}/.config/degitx/frontend.yml"

const pConfigSys = "/etc/degitx/frontend.yml"

/**
 * @todo #74 Add channels for errors ans system signals and wait via select (front end)
 * Let's implement channels and handle them here to be able to start servers in goroutines
 */
func cmdRun(ctx *cli.Context) error {
	cfg := new(config.DegitxConfig)
	if err := cfg.FromFiles(pConfigUser, pConfigSys, ctx.String("config")); err != nil {
		return err
	}
	logging.InitNodeless(cfg.LogConfig)

	addr, err := ma.NewMultiaddr(ctx.String("host"))
	if err != nil {
		return err
	}
	gitaly, err := server.NewGrpcServer(addr)
	if err != nil {
		return err
	}

	return frontend.Start(ctx.Context, gitaly)
}
