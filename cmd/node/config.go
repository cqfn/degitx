// MIT License. Copyright (c) 2020 CQFN
// https://github.com/cqfn/degitx/blob/master/LICENSE

package main

import (
	"crypto/sha1" //nolint:gosec //used only to hash public key
	"encoding/hex"
	"fmt"
	"io/ioutil"

	"github.com/multiformats/go-multihash"
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
	return config.allRequiredFieldsPresent()
}

func (config *NodeConfig) allRequiredFieldsPresent() error {
	fields := map[string]string{
		config.Version:      "config format version",
		config.Keys.Alg:     "key algorithm",
		config.Keys.Private: "private key location",
		config.Keys.Public:  "public key location",
	}
	for field, desc := range fields {
		if len(field) == 0 {
			return fmt.Errorf("%s is omitted", desc) //nolint:goerr113 // No error to wrap here.
		}
	}
	return nil
}

func (config *NodeConfig) generateNodeID() (string, error) {
	data := []byte(config.Keys.Public)
	buf := sha1.Sum(data) //nolint:gosec //public key is not so secured
	mHashBuf, err := multihash.EncodeName(buf[:], "sha1")
	if err != nil {
		return "", err
	}
	return hex.EncodeToString(mHashBuf), nil
}
