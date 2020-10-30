![CI](https://github.com/cqfn/degitx/workflows/CI/badge.svg?branch=master&event=push)
![Build white paper document](https://github.com/cqfn/degitx/workflows/Build%20white%20paper%20document/badge.svg)
![Lines of code](https://img.shields.io/tokei/lines/github/cqfn/degitx)


DeGitX - distributed git repository manager,
see explanation in the [white paper](https://central.artipie.com/degit/wp/white-paper-latest.pdf)
or job Telegram chat to discuss: [@cqfn_degit](https://t.me/cqfn_degit).

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

To propose new changes:
 1 - create a new branch from `master`
 2 - write the code
 3 - verify with `make verify` to be sure all tests passes
 4 - create new commit using format: `#<ticket> - <message>`, push to fork
 5 - create pull request: specify the problem in PR description, describe the changes
 in PR body
 
Use `make` to build this project:
 - `make` - install all dependencies, generate proto files, run tests and build node
 - `make install-deps` - install required dependencies
 - `make proto` - generate protobuf source code
 - `make build` - build core package
 - `make test` - run tests
 - `make node` - build `node` binary
 - `make lint` - run linters. [golangci-lint](https://golangci-lint.run/) required to be installed in advance.
 - `make verify` - build, test and lint

### GPG public key

Use this public key to verify release checksums (`gpg --verify checksums.txt.sig`):
```
-----BEGIN PGP PUBLIC KEY BLOCK-----

mQENBF+EZIQBCAC9omCAFioYjYIDxhzMz3gykCglQMiOsRNYNG6N+H/2G+A7paU8
9PGapRbOG/wmuE0J76Quh6R/g4MvnSbn3ssbJRWFEYSb1YY/PrABvZPZF6BQ2zsj
zcqSKsrLd7te2LQj4zDtexsoc4s372/qzor+ysGG6aRObgZejgRu2zBhVUkxsBHT
M0AjoHwk38UCmxPB1WF9mJ7fU+wNmvQQxp2BY7ghWFQEBwoknPvIhbLi08o2ZG1m
Wh8d9+fp4KvG0Zm3qnnXo70jvSH3vV1jMalXx7xqKEpyHfxKS4A5ajhDeO9ZY+ZQ
o/tjjfk8WgMJ1cdDENcxn3oNyGmGp1iUj9MFABEBAAG0OEtpcmlsbCBDaGUgKERl
R2l0WCByZWxlYXNlcyBrZXkpIDxnNHM4LnB1YmxpY0BnbWFpbC5jb20+iQFUBBMB
CgA+FiEEhCkidrjRFP1FD4TAQh7YI6G3UOMFAl+EZIQCGwMFCQBpeAAFCwkIBwMF
FQoJCAsFFgIDAQACHgECF4AACgkQQh7YI6G3UOMfEggAhXW3qXdmuVQKnBEeXoOm
g5SvamY0B8sxqZ1EyF9bq0rmijiK5Pl7Vb688vZyzs+RhojVL5VqtA1crSRaKMgL
wXzrb/QZ5EvMK/MNsTbk/oYoXGtp67bdcINXrHMwbuL2SiLxaPxxGlE6mM+Zl7hE
tADR2764LbV6hWFQ2hYm1rER3Xa3gKUffDHbAtF3DvuTijbOC/Uuia/6NzaZnxPL
rlJf0QaYkQA5hc/lQyR/sQpmSwCKyqzNy9XTYOK9HXGLAuitVZ87FMmHitVn5rmJ
93HEQ1vLXv6hClJvz9o9kltYqzKDLABw4Pk9RUlEqiXC6CqRkGZ27KuFeB+tDSxT
uLkBDQRfhGSEAQgA1Ek+XBxtouU3SHpWLDHx1NOKNQHpKCOL3Xp3o1pi3n4eTS2F
/VJnuHF+0QzFDw12OPcQtq+3VPMG3YrguCEG+8PsSAYf5mQCPdbPNHT3f8YkweG8
CqpIh0gO1MHfvgI8dtJmkrcBqOQIrLwMEnUu1fhzINIBySi8SvwOaqiccmHBq7CP
2jNOomGsXvsPrK82ozFRgqqGUppWrRpZ46qIa0fs25kJG8XCcijnv61H4OYyJ4cc
AIB8yeS4CpXVz9KhJ3ExWpllUpGbhqtDbmq//mk+aSNW1SMJjYX0XI/3TM1/bEck
kjw0bfbRhTPoKI4sNv3kIeYW5AFPgjMa1P7WowARAQABiQE8BBgBCgAmFiEEhCki
drjRFP1FD4TAQh7YI6G3UOMFAl+EZIQCGwwFCQBpeAAACgkQQh7YI6G3UOO3VQf/
ZXKfDrYnKXwZEhUDQj8J9Ifw36Rw0Bc4t+yA2UZEs2EKSX+8cbIfT+zDli/X4989
PHl2ewZqx0gnc0eQJ0j046ATPd2Gk0+ARS+eFhxxYxr/SN3qj+yaMzVjduzaYO7V
socx1Rxp7u75m9rHf4a5WB5ZRxsmz3N2vdpqR91LpdQg7XUrJ1uoRy1esNFQ9xtn
ohLFnsZ/FzrYlH7Ta8Iqzj4ld+Jxcyp0CHa0QKXoa9Y87zVTBdK0dEXjQ1zxqNuQ
aYalu/sMPosnG+xMg5L9YECj5VwWhjjYbgrg7qffHMYTG2QP/+10lH1MLn+Zb1jl
6rvy7y8csovT6eMiQVAMNw==
=hiH+
-----END PGP PUBLIC KEY BLOCK-----
```
