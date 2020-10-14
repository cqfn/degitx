// MIT License. Copyright (c) 2020 CQFN
// https://github.com/cqfn/degitx/blob/master/LICENSE

// Package config contains yaml node config parser
package config

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

// FromFile parses yaml node config from a file by a given name
func (cfg *NodeConfig) FromFile(fileName string) error {
	source, err := ioutil.ReadFile(fileName) //nolint:gosec // no user input for filename
	if err != nil {
		return err
	}
	return cfg.Parse(source)
}

// Parse parses yaml node config from given bytes
func (cfg *NodeConfig) Parse(source []byte) error {
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
			return fmt.Errorf("%v is omitted", desc) //nolint:goerr113 // No error to wrap here.
		}
	}
	return nil
}
