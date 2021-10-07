// MIT License. Copyright (c) 2020 CQFN
// https://github.com/cqfn/degitx/blob/master/LICENSE

package misc

import (
	"errors"
	"fmt"
	"net"

	ma "github.com/multiformats/go-multiaddr"
)

// maNetworkAddr is a multiaddr to network addr adaptor
type maNetworkAddr struct {
	net  string
	addr string
}

// Network name string, e.g. ipv4 or ipv6
func (n *maNetworkAddr) Network() string {
	return n.net
}

func (n *maNetworkAddr) String() string {
	return n.addr
}

// ErrInvalidAddr returned when multiaddr is invalid
var ErrInvalidAddr = errors.New("invalid address")

// MultiAddrToNet converts multiaddr to net.Addr
func MultiAddrToNet(src ma.Multiaddr) (net.Addr, error) {
	prts := src.Protocols()
	if len(prts) < 2 { //nolint:gomnd // 2 parts is verbose enough here
		return nil, ErrInvalidAddr
	}
	pip := prts[0]
	var prefix string
	switch pip.Code {
	case ma.P_IP4:
		prefix = "ipv4"
	case ma.P_IP6:
		prefix = "ipv6"
	default:
		return nil, ErrInvalidAddr
	}
	ptcp := prts[1]
	if ptcp.Code != ma.P_TCP {
		return nil, ErrInvalidAddr
	}
	ip, err := src.ValueForProtocol(pip.Code)
	if err != nil {
		return nil, fmt.Errorf("failed to find IP component: %w", err)
	}
	tcp, err := src.ValueForProtocol(ptcp.Code)
	if err != nil {
		return nil, fmt.Errorf("failed to find TCP component: %w", err)
	}
	n := new(maNetworkAddr)
	n.addr = fmt.Sprintf("%s:%s", ip, tcp)
	n.net = prefix
	return n, nil
}
