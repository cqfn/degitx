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

# install and run golangci-lint. sudo required
lint:
	@echo "install golangci-lint"
	@curl -sSfL https://raw.githubusercontent.com/golangci/golangci-lint/master/install.sh | sh -s -- -b $(go env GOPATH)/bin v1.31.0
	@golangci-lint --version
	@echo "lint degitx"
	@golangci-lint run
	@echo "degitx linted"
