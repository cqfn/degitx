PROTODIR := proto
RMRF := rm -rf
GO := go
FLAGS := -v

.PHONY: all build clean install-deps lint  $(PROTODIR)

all: build test node

# build core package
build: $(PROTODIR)
	go build $(FLAGS)

# build node CLI
node: build
	go build $(FLAGS) ./cmd/node

# run tests
test: build
	go test $(FLAGS)

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
