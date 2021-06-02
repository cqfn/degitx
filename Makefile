ifeq ($(V),1)
  Q =
else
  Q = @
endif

PROTODIR := proto
WPDIR := white-paper
TEST_OPTS := -count=1
TARGETS := degitx degitx-gitaly
SRC_DIR := $(abspath $(dir $(lastword ${MAKEFILE_LIST})))
BUILD_DIR := ${SRC_DIR}/target
PKG := cqfn.org/degitx
ifeq ($(V),1)
  GOFLAGS :=
else
  GOFLAGS := -v
endif

# find all commands binary names
find_cmd = $(notdir $(shell find ${SRC_DIR}/cmd -mindepth 1 -maxdepth 1 -type d -print))

# run_tests_dir - run all tests in provided directory
define _run_tests_dir
  go test ${FLAGS} ${TEST_OPTS} "./$(1)/..."
endef

unexport GOROOT
export GOBIN=${BUILD_DIR}/bin
export GOCACHE=${BUILD_DIR}/cache
export PATH := ${BUILD_DIR}/bin:${PATH}

.PHONY: all
all: build

debug:
	go env

# build binaries
.PHONY: build
build: proto
	${Q}go install ${GOFLAGS} $(addprefix ${PKG}/cmd/, $(call find_cmd))

# tests
.PHONY: test
test: proto
	$(call _run_tests_dir,internal)
	$(call _run_tests_dir,pkg)

# race detector
.PHONY: test-race
test-race: TEST_OPTS := ${TEST_OPTS} -race
test-race: test

# benchmarks
.PHONY: bench
bench: TEST_OPTS := ${TEST_OPTS} -bench=. -run=^$
bench: test

# generate protobuf sources
.PHONY: proto
proto:
	$(MAKE) -C $(PROTODIR)

# clean all
.PHONY: clean
clean:
	$(MAKE) -C $(PROTODIR) clean
	${Q}mkdir -pv ${BUILD_DIR}
	${Q}chmod -R +w ${BUILD_DIR}
	${Q}rm -fr ${BUILD_DIR}

# install required dependencies
install-deps:
	$(MAKE) -C $(PROTODIR) install-deps

# run golangci-lint
lint:
	${Q}golangci-lint ${FLAGS} run

.PHONY: check-mod-tidy
check-mod-tidy:
	${Q}git diff --exit-code go.mod go.sum || (echo "error: uncommitted changes in go.mod or go.sum" && exit 1)
	${Q}go mod tidy
	${Q}git diff --exit-code go.mod go.sum || (echo "error: uncommitted changes in go.mod or go.sum" && exit 1)

# verify build before commit
.PHONY: verify
verify: build test lint check-mod-tidy

$(WPDIR):
	$(MAKE) -C $(WPDIR)
