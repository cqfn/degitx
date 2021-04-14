OUT := ${CURDIR}/go/degitxpb
GOPATH := $(shell go env GOPATH)
PROTOC_GEN_GO := $(GOPATH)/bin/protoc-gen-go
PROTOC := env PATH="$(GOPATH)/bin:${PATH}" protoc
GOGET := env GO111MODULE=off go get -v

RMFR := rm -fr
MKDIR := mkdir -pv

.PHONY: all clean install-deps

# generate protobuf sources
all: $(PROTOC_GEN_GO) $(OUT)
	$(PROTOC) --go_out=plugins=grpc:$(OUT) --go_opt=paths=source_relative *.proto

# target directory of protobuf go sources
$(OUT):
	$(MKDIR) $(OUT)

# target location of protoc-gen-go tool
$(PROTOC_GEN_GO):
	$(GOGET) github.com/golang/protobuf/protoc-gen-go
	$(GOGET) google.golang.org/grpc/cmd/protoc-gen-go-grpc

# clean target directory
clean:
	$(RMFR) $(OUT)

# install required dependencies
install-deps: $(PROTOC_GEN_GO)

