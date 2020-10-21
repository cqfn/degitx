// MIT License. Copyright (c) 2020 CQFN
// https://github.com/cqfn/degitx/blob/master/LICENSE

package main

import (
	"fmt"
	"io/ioutil"

	"gopkg.in/yaml.v2"
	"cqfn.org/degitx/locators"
)

type Keys struct {
	Alg           string `yaml:"alg"`
	PathToPrivate string `yaml:"private"`
	PathToPublic  string `yaml:"public"`
}

type Locator struct {
	HashFunc string `yaml:"hash"`
}

type NodeConfig struct {
	Version  string   `yaml:"version"`
	Keys     *Keys    `yaml:"keys"`
	Locators *Locator `yaml:"locator"`
}

func (config *NodeConfig) fromFile(fileName string) error {
	source, err := ioutil.ReadFile(fileName) //nolint:gosec // no user input for filename
	if err != nil {
		return err
	}
	return config.parse(source)
}

func (config *NodeConfig) parse(source []byte) error {
	if err := yaml.UnmarshalStrict(source, &config); err != nil {
		return err
	}
	return config.validate()
}

func (config *NodeConfig) validate() error {
	fields := map[string]string{
		config.Version:            "config format version",
		config.Keys.Alg:           "key algorithm",
		config.Keys.PathToPrivate: "private key location",
		config.Keys.PathToPublic:  "public key location",
	}
	for field, desc := range fields {
		if len(field) == 0 {
			return fmt.Errorf("%s is omitted", desc) //nolint:goerr113 // No error to wrap here.
		}
	}
	return nil
}

// Locator of node (nodeID)
func (config *NodeConfig) Locator() (locators.Locator, error) {
	kpub, err := ioutil.ReadFile(config.Keys.PathToPublic) //nolint:gosec // no user input for filename
	if err != nil {
		return nil, err
	}
	var hfunc string
	if config.Locators != nil {
		hfunc = config.Locators.HashFunc
	}
	if hfunc == "" {
		hfunc = "SHA1"
	}
	return locators.NewHash(kpub, hfunc)
}
