// MIT License. Copyright (c) 2020 CQFN
// https://github.com/cqfn/degitx/blob/master/LICENSE

package discovery

import (
	"context"
)

// Seed host for discovery peers resolving
type Seed interface {
	Start(context.Context) error
}
