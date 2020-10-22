// MIT License. Copyright (c) 2020 CQFN
// https://github.com/cqfn/degitx/blob/master/LICENSE

package main

import (
	"encoding/hex"
	"errors"
	"fmt"
	"log"
	"os"

	"cqfn.org/degitx"
	"cqfn.org/degitx/discovery"
	ma "github.com/multiformats/go-multiaddr"
	"github.com/urfave/cli/v2"
)

func main() {
	app := cli.App{
		Name:        "degitx",
		Usage:       "Manage degit node",
		Description: "DeGitX node CLI",
		Flags: []cli.Flag{
			&cli.StringFlag{
				Name:    "config",
				Aliases: []string{"c"},
				Usage:   "configuration file path",
			},
		},
		Commands: []*cli.Command{
			{
				Name:    "run",
				Aliases: []string{"r"},
				Usage:   "run the node",
				Action:  cmdRun,
				Flags: []cli.Flag{
					&cli.StringFlag{
						Name:  "peer-host",
						Usage: "peer discovery host address (multiaddr)",
					},
					&cli.StringFlag{
						Name:  "peer-seed",
						Usage: "initial peer seed host address (multiaddr)",
					},
				},
			},
			{
				Name:   "id",
				Usage:  "print current node id",
				Action: printID,
			},
		},
	}
	if err := app.Run(os.Args); err != nil {
		log.Fatalf("App failed: %s", err)
	}
}

const pConfigUser = "${HOME}/.config/degitx/config.yml"

const pConfigSys = "/etc/degitx/config.yml"

var errConfigNotFound = errors.New("configuration file was not found")

func parseConfig(ctx *cli.Context) (*NodeConfig, error) {
	config := new(NodeConfig)
	paths := []string{
		ctx.String("config"),
		pConfigUser, pConfigSys,
	}
	var path string
	for _, p := range paths {
		if p == "" {
			continue
		}
		p = os.ExpandEnv(p)
		if _, err := os.Stat(p); os.IsNotExist(err) {
			continue
		}
	}
	if path == "" {
		return nil, errConfigNotFound
	}
	err := config.fromFile(path)
	if err != nil {
		return nil, err
	}
	return config, nil
}

func cmdRun(ctx *cli.Context) error {
	cfg, err := parseConfig(ctx)
	if err != nil {
		return err
	}
	loc, err := cfg.Locator()
	if err != nil {
		return err
	}
	var dsc discovery.Service
	peer := ctx.String("peer-host")
	if peer != "" { //nolint:nestif // consider refactoring later
		addr, err := ma.NewMultiaddr(peer)
		if err != nil {
			return err
		}
		dsc, err = discovery.NewServer(addr, loc)
		if err != nil {
			return err
		}
	} else {
		dsc = new(discovery.StubService)
	}
	return degitx.Start(ctx.Context, dsc)
}

func printID(ctx *cli.Context) error {
	cfg, err := parseConfig(ctx)
	if err != nil {
		return err
	}
	l, err := cfg.Locator()
	if err != nil {
		return err
	}
	mh, err := l.Multihash()
	if err != nil {
		return err
	}
	fmt.Println(hex.EncodeToString(mh))
	return nil
}
