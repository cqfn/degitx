PROTODIR := proto
WPDIR := white-paper
RMRF := rm -rf
GO := go
FLAGS := -v

.PHONY: all build clean install-deps lint tidy verify $(PROTODIR) $(WPDIR)

all: build test degitx degitx-gitaly

# build core package
build: $(PROTODIR)
	go build $(FLAGS)

install: build
	go install $(FLAGS)

# run tests
test: build
	go test $(FLAGS) ./locators
	go test $(FLAGS) ./discovery
	go test $(FLAGS) ./cmd/degitx
	go test $(FLAGS) ./cmd/degitx-gitaly

degitx: build proto
	go build $(FLAGS) ./cmd/degitx

degitx-gitaly: build proto
	go build $(FLAGS) ./cmd/degitx-gitaly

# generate protobuf sources
$(PROTODIR):
	$(MAKE) -C $(PROTODIR)

# clean all
clean:
	$(MAKE) -C $(PROTODIR) clean
	$(RMRF) degitx
	$(RMRF) degitx-gitaly

# install required dependencies
install-deps:
	$(MAKE) -C $(PROTODIR) install-deps

# run golangci-lint
lint:
	golint .
	golint ./discovery
	golint ./locators
	@golangci-lint --version
	golangci-lint run

# remove unused dependencies
tidy:
	go mod tidy

# verify build before commit
verify: build test lint degitx degitx-gitaly
	@echo "Built is OK"

$(WPDIR):
	$(MAKE) -C $(WPDIR)
