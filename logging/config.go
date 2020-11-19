// MIT License. Copyright (c) 2020 CQFN
// https://github.com/cqfn/degitx/blob/master/LICENSE

package logging

import (
	"io/ioutil"

	"gopkg.in/yaml.v2"
)

type LogConfig struct {
	Outputs   []Output `yaml:"outputs"`
	ErrorsOut []string `yaml:"errors"`
}

type Output struct {
	Path   []string `yaml:"path"`
	Level  string   `yaml:"level"`
	Format string   `yaml:"format"`
}

func (config *LogConfig) FromFile(fileName string) error {
	source, err := ioutil.ReadFile(fileName) //nolint:gosec // no user input for filename
	if err != nil {
		return err
	}
	return config.parse(source)
}

func (config *LogConfig) parse(source []byte) error {
	if err := yaml.UnmarshalStrict(source, &config); err != nil {
		return err
	}
	return nil
}
