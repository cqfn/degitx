// MIT License. Copyright (c) 2020 CQFN
// https://github.com/cqfn/degitx/blob/master/LICENSE

package logging

import (
	"io/ioutil"

	"gopkg.in/yaml.v2"
)

// LogConfig is a log configuration
type LogConfig struct {
	Outputs   []Output `yaml:"outputs"`
	ErrorsOut []string `yaml:"errors"`
}

// Output is a log settings: where to write logs, on which level and how to format them.
type Output struct {
	Path   []string `yaml:"path"`
	Level  string   `yaml:"level"`
	Format string   `yaml:"format"`
}

// FromFile parses yaml file.
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
