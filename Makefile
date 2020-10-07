PROTODIR := proto
RMRF := rm -rf
GO := go
FLAGS := -v

.PHONY: all build clean install-deps $(PROTODIR)

all: build test node

build: $(PROTODIR)
	go build $(FLAGS)

node: build
	go build $(FLAGS) ./cmd/node

test: build
	go test $(FLAGS)

$(PROTODIR):
	$(MAKE) -C $(PROTODIR)

clean:
	$(MAKE) -C $(PROTODIR) clean
	$(RMRF) node

install-deps:
	$(MAKE) -C $(PROTODIR) install-deps
