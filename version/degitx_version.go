// MIT License. Copyright (c) 2020 CQFN
// https://github.com/cqfn/degitx/blob/master/LICENSE

// Package version provide information about degitx build.
package version

var version = "dev"

// GetVersion returns the version of degitx that is taken from goreleaser.
func GetVersion() string {
	return version
}
