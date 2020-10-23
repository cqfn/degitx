// MIT License. Copyright (c) 2020 CQFN
// https://github.com/cqfn/degitx/blob/master/LICENSE

package discovery

import (
	"fmt"

	ma "github.com/multiformats/go-multiaddr"
)

type MaNetworkAddr struct {
	net  string
	addr string
}

func (n *MaNetworkAddr) Network() string { //nolint:dupl // linter mistake
	return n.net
}

func (n *MaNetworkAddr) String() string { //nolint:dupl // linter mistake
	return n.addr
}

// Parse multiaddr into network addr
func (n *MaNetworkAddr) Parse(addr ma.Multiaddr) error {
	prts := addr.Protocols()
	if len(prts) < 2 { //nolint:gomnd // 2 parts is verbose enough here
		return errInvalidSeedAddr
	}
	pip := prts[0]
	var prefix string
	switch pip.Code {
	case ma.P_IP4:
		prefix = "ipv4"
	case ma.P_IP6:
		prefix = "ipv6"
	default:
		return errInvalidSeedAddr
	}
	ptcp := prts[1]
	if ptcp.Code != ma.P_TCP {
		return errInvalidSeedAddr
	}
	ip, err := addr.ValueForProtocol(pip.Code)
	if err != nil {
		return fmt.Errorf("failed to find IP component: %w", err)
	}
	tcp, err := addr.ValueForProtocol(ptcp.Code)
	if err != nil {
		return fmt.Errorf("failed to find TCP component: %w", err)
	}
	n.addr = fmt.Sprintf("%s:%s", ip, tcp)
	n.net = prefix
	return nil
}
