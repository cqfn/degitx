PROTODIR := proto
RMRF := rm -rf
GO := go
FLAGS := -v

.PHONY: all build clean install-deps lint tidy $(PROTODIR)

all: build test node lint

# build core package
build: $(PROTODIR)
	go build $(FLAGS)

install: build
	go install $(FLAGS)

# run tests
test: build
	go test $(FLAGS)
	go test $(FLAGS) ./locators
	go test $(FLAGS) ./cmd/node

node: build proto
	go build $(FLAGS) ./cmd/node

# generate protobuf sources
$(PROTODIR):
	$(MAKE) -C $(PROTODIR)

# clean all
clean:
	$(MAKE) -C $(PROTODIR) clean
	$(RMRF) node

# install required dependencies
install-deps:
	$(MAKE) -C $(PROTODIR) install-deps

# run golangci-lint
lint:
	@golangci-lint --version
	golangci-lint run

tidy:
	go mod tidy
