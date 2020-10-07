![CI](https://github.com/cqfn/degitx/workflows/CI/badge.svg?branch=master&event=push)
![Build white paper document](https://github.com/cqfn/degitx/workflows/Build%20white%20paper%20document/badge.svg)
![Lines of code](https://img.shields.io/tokei/lines/github/cqfn/degitx)


DeGitX - distributed git repository manager, see explanation in the [white paper](https://central.artipie.com/degit/wp/white-paper-latest.pdf).

## Build

Use `make` to build this project:
 - `make` - install all dependencies, generate proto files, run tests and build node
 - `make install-deps` - install required dependencies
 - `make proto` - generate protobuf source code
 - `make build` - build core package
 - `make test` - run tests
 - `make node` - build `node` binary


<!--
@todo #1:30min Process links in the readme.
 Remove already analyzed links. If link is not analyzed, then
 Handle it, extract summary and add research result to white paper document.

Consensus algorithms:
 - http://www.cs.yale.edu/homes/aspnes/pinewiki/Paxos.html
 - https://en.wikipedia.org/wiki/Paxos_algorithm
 - https://raft.github.io/

Researches:
 - https://dl.acm.org/doi/10.1145/98163.98167
 - https://web.archive.org/web/20060508040935/http://www.eecs.harvard.edu/cs262/DSbook.c7.pdf

Implementations:
 - [Spokes](https://github.blog/2016-09-07-building-resilience-in-spokes/) by GitHub
 (previously known as [DGit](https://github.blog/2016-04-05-introducing-dgit/))
 - [etcd](https://etcd.io/)
 - IPFS:
   - [home-page](https://ipfs.io/)
   - [white-paper](https://raw.githubusercontent.com/ipfs-inactive/papers/master/ipfs-cap2pfs/ipfs-p2p-file-system.pdf)
   - [blog-post](https://medium.com/a-weekend-with/a-weekend-with-ipfs-9f2647fc231)
 - [brig](https://github.com/sahib/brig)

-->
