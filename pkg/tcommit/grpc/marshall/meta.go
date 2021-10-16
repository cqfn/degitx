// MIT License. Copyright (c) 2020 CQFN
// https://github.com/cqfn/degitx/blob/master/LICENSE

package marshall

import (
	"cqfn.org/degitx/pkg/tcommit"
	"cqfn.org/degitx/pkg/tcommit/grpc/pb"
)

// FromProtoMeta converts the proto definition of Meta to the application one
func FromProtoMeta(meta *pb.Meta) (tcommit.Meta, error) {
	return tcommit.Meta(meta.GetMeta()), nil
}
