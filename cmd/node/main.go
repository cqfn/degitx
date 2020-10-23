// MIT License. Copyright (c) 2020 CQFN
// https://github.com/cqfn/degitx/blob/master/LICENSE

package main

import (
	"fmt"
	"log"
	"os"
	"strings"

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
					&cli.StringFlag{
						Name:     "gitaly-host",
						Usage:    "Gitaly gRPC API host and port",
						Required: true,
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

type errConfigNotFound struct{ paths []string }

func (e *errConfigNotFound) Error() string {
	return fmt.Sprintf("configuration file not found in {%s}",
		strings.Join(e.paths, ":"))
}

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
		path = p
		break
	}
	if path == "" {
		return nil, &errConfigNotFound{paths}
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
	node, err := cfg.Node()
	if err != nil {
		return err
	}
	peers := discovery.NewPeers(ctx.Context)
	var dsc discovery.Service
	peer := ctx.String("peer-host")
	seed := ctx.String("peer-seed")
	if peer != "" { //nolint:nestif,gocritic // consider refactoring later
		addr, err := ma.NewMultiaddr(peer)
		if err != nil {
			return err
		}
		dsc, err = discovery.NewGrpcServer(addr, node, peers)
		if err != nil {
			return err
		}
	} else if seed != "" {
		addr, err := ma.NewMultiaddr(seed)
		if err != nil {
			return err
		}
		dsc = discovery.NewGrpcClient(addr, node, peers)
		if err != nil {
			return err
		}
	} else {
		dsc = new(discovery.StubService)
	}
	node.Addr, err = ma.NewMultiaddr(ctx.String("gitaly-host"))
	if err != nil {
		return err
	}
	return degitx.Start(ctx.Context, node, dsc)
}

func printID(ctx *cli.Context) error {
	cfg, err := parseConfig(ctx)
	if err != nil {
		return err
	}
	l, err := cfg.Node()
	if err != nil {
		return err
	}
	fmt.Println(l)
	return nil
}
