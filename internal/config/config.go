// MIT License. Copyright (c) 2020 CQFN
// https://github.com/cqfn/degitx/blob/master/LICENSE

// Package config contains config parser code that is shared between front- and back-end parts.
package config

import (
	"fmt"
	"io/ioutil"
	"os"
	"path/filepath"
	"strings"

	"cqfn.org/degitx/internal/locators"
	"cqfn.org/degitx/internal/logging"

	"gopkg.in/yaml.v2"
)

// Keys is a key's algorithm and paths to private and public keys.
type Keys struct {
	Alg           string `yaml:"alg"`
	PathToPrivate string `yaml:"private"`
	PathToPublic  string `yaml:"public"`
}

// DegitxConfig is a config for both front- and back-end apps.
type DegitxConfig struct {
	Version   string             `yaml:"version"`
	Keys      *Keys              `yaml:"keys"`
	LogConfig *logging.LogConfig `yaml:"logging"`
}

type errConfigNotFound struct{ paths []string }

func (e *errConfigNotFound) Error() string {
	return fmt.Sprintf("configuration file not found in {%s}",
		strings.Join(e.paths, ":"))
}

// FromFiles ensures that at least one file by given paths exist and parses its yaml content.
func (config *DegitxConfig) FromFiles(paths ...string) error {
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
		return &errConfigNotFound{paths}
	}
	err := config.FromFile(path)
	if err != nil {
		return err
	}
	return nil
}

// FromFile parses yaml file.
func (config *DegitxConfig) FromFile(fileName string) error {
	source, err := ioutil.ReadFile(filepath.Clean(fileName))
	if err != nil {
		return err
	}
	return config.parse(source)
}

func (config *DegitxConfig) parse(source []byte) error {
	if err := yaml.UnmarshalStrict(source, &config); err != nil {
		return err
	}
	return config.validate()
}

func (config *DegitxConfig) validate() error {
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

// Node identity properties
func (config *DegitxConfig) Node() (*locators.Node, error) {
	kpub, err := ioutil.ReadFile(filepath.Clean(config.Keys.PathToPublic))
	if err != nil {
		return nil, err
	}
	kpriv, err := ioutil.ReadFile(filepath.Clean(config.Keys.PathToPrivate))
	if err != nil {
		return nil, err
	}
	return locators.FromKeys(kpub, kpriv)
}
