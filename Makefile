GIT := git
PROTODIR := proto
WPDIR := white-paper
RMRF := rm -rf
GO := go
FLAGS := -v
TEST_OPTS := -count=1

.PHONY: all build clean install-deps lint verify $(PROTODIR) $(WPDIR)

all: build test degitx degitx-gitaly

# build core package
build: $(PROTODIR)
	go build $(FLAGS)

install: build
	go install $(FLAGS)

# run_tests_dir - run all tests in provided directory
define _run_tests_dir
  go test $(FLAGS) ${TEST_OPTS} "./$(1)/..."
endef

.PHONY: test
test: $(OUTPUT)
	$(call _run_tests_dir,internal)
	# $(call _run_tests_dir,pkg)

.PHONY: test-race
test-race: TEST_OPTS := ${TEST_OPTS} -race
test-race: test

.PHONY: bench
bench: TEST_OPTS := ${TEST_OPTS} -bench=. -run=^$
bench: test

degitx: build proto
	go build $(FLAGS) ./cmd/degitx

degitx-gitaly: build proto
	go build $(FLAGS) ./cmd/degitx-gitaly

# generate protobuf sources
$(PROTODIR):
	$(MAKE) -C $(PROTODIR)

# clean all
.PHONY: clean
clean:
	$(MAKE) -C $(PROTODIR) clean
	$(RMRF) degitx
	$(RMRF) degitx-gitaly

# install required dependencies
install-deps:
	$(MAKE) -C $(PROTODIR) install-deps

# run golangci-lint
lint:
	${Q}golangci-lint --version
	${Q}golangci-lint run

.PHONY: check-mod-tidy
check-mod-tidy:
	${Q}${GIT} diff --quiet --exit-code go.mod go.sum || (echo "error: uncommitted changes in go.mod or go.sum" && exit 1)
	${Q}go mod tidy
	${Q}${GIT} diff --quiet --exit-code go.mod go.sum || (echo "error: uncommitted changes in go.mod or go.sum" && exit 1)

# verify build before commit
.PHONY: verify
verify: build test lint check-mod-tidy degitx degitx-gitaly

$(WPDIR):
	$(MAKE) -C $(WPDIR)
