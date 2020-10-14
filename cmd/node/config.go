// MIT License. Copyright (c) 2020 CQFN
// https://github.com/cqfn/degitx/blob/master/LICENSE

package main

import (
	"fmt"
	"io/ioutil"

	"gopkg.in/yaml.v2"
)

type Keys struct {
	Alg     string `yaml:"alg"`
	Private string `yaml:"private"`
	Public  string `yaml:"public"`
}

type NodeConfig struct {
	Version string `yaml:"version"`
	Keys    *Keys  `yaml:"keys"`
}

func (cfg *NodeConfig) fromFile(fileName string) error {
	source, err := ioutil.ReadFile(fileName) //nolint:gosec // no user input for filename
	if err != nil {
		return err
	}
	return cfg.parse(source)
}

func (cfg *NodeConfig) parse(source []byte) error {
	if err := yaml.UnmarshalStrict(source, &cfg); err != nil {
		return err
	}
	return cfg.allFieldsPresent()
}

func (cfg *NodeConfig) allFieldsPresent() error {
	fields := map[string]string{
		cfg.Version:      "config format version",
		cfg.Keys.Alg:     "key algorithm",
		cfg.Keys.Private: "private key location",
		cfg.Keys.Public:  "public key location",
	}
	for field, desc := range fields {
		if len(field) == 0 {
			return fmt.Errorf("%s is omitted", desc) //nolint:goerr113 // No error to wrap here.
		}
	}
	return nil
}
