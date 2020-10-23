// MIT License. Copyright (c) 2020 CQFN
// https://github.com/cqfn/degitx/blob/master/LICENSE

// Package misc provides useful common functions that can be moved
// to separated projects later
package misc

import (
	"io"
	"log"
)

// CloseWithLog tries to close the resource and log on error
// it can be used as `defer misc.CloseWithLog(res)`
func CloseWithLog(res io.Closer) {
	if err := res.Close(); err != nil {
		log.Printf("CloseWithLog: %s", err)
	}
}
