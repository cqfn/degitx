![CI](https://github.com/cqfn/degitx/workflows/CI/badge.svg?branch=master&event=push)
![Build white paper document](https://github.com/cqfn/degitx/workflows/Build%20white%20paper%20document/badge.svg)
![Lines of code](https://img.shields.io/tokei/lines/github/cqfn/degitx)
[![Telegram chat](https://img.shields.io/badge/Telegram-chat-brightgreen.svg)](https://t.me/cqfn_degit)



DeGitX - distributed git repository manager,
see explanation in the [white paper](https://central.artipie.com/degit/wp/white-paper-latest.pdf)
or job Telegram chat to discuss: [@cqfn_degit](https://t.me/cqfn_degit).

## Install

Download proper binary asset from releases page: https://github.com/cqfn/degitx/releases
(e.g. `degit_(version)_Linux_x86_64.tar.gz` for Linux64 machine).
To verify build signature, download `checksums.txt`, `checksums.txt.sig` and
import GPG by id `84292276B8D114FD450F84C0421ED823A1B750E3` from one of the keyservers, e.g.
```bash
gpg --keyserver pgp.mit.edu --recv-keys 84292276B8D114FD450F84C0421ED823A1B750E3
```
GPG public key from `degit-key.pub` repository root, then import GPG key into your GPG keychain.
After GPG import, verify checksums signature files (downloaded from release assets) using command
```bash
gpg --verify checksums.txt.sig
```
If everithing is OK, verify SHA256 hash of binary asset downloaded (ignore errors for other platform assets):
```bash
sha256sum -c checksums.txt
```
If checksum is OK, extract binary from the archive:
```bash
tar -xvzf degit_(version)_(platform).tar.gz
```

## Node Configuration

`yaml` is the only node configuration format and consist of: 

 - `version` - config format version
 - `keys` - node crypto keys:
   - `alg` - key algorithm
   - `private` - private key location
   - `public` - public key location
   
All fields are required. 

<!--
@todo #25:30min Analyze projects and consensus algorithms above,
 extract summary and refernces, add to white paper. For projects:
 find white paper or other document, and extract summary from it.

Consensus algorithms:
 - http://www.cs.yale.edu/homes/aspnes/pinewiki/Paxos.html
 - https://en.wikipedia.org/wiki/Paxos_algorithm
 - https://raft.github.io/

Projects
 - [etcd](https://etcd.io/)
 - [brig](https://github.com/sahib/brig)

-->

### Contributing

This page will help you with contributing workflow:
https://github.com/cqfb/degitx/blob/master/CONTRIBUTING.md

To build the project use `make` command:
 - `make` - install all dependencies, generate proto files, run tests and build node
 - `make install-deps` - install required dependencies
 - `make proto` - generate protobuf source code
 - `make build` - build core package
 - `make test` - run tests
 - `make degitx` - build `node` binary
 - `make degitx-gitaly` - build front-end binary
 - `make lint` - run linters. [golangci-lint](https://golangci-lint.run/) required to be installed in advance.
 - `make verify` - build, test, lint, degitx and degitx-gitaly
