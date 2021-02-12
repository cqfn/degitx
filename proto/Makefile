OUT := ${CURDIR}/go/degitxpb
GOPATH := $(shell go env GOPATH)
PROTOC_GEN_GO := $(GOPATH)/bin/protoc-gen-go
PROTOC := env PATH="$(GOPATH)/bin:${PATH}" protoc
GOGET := go get -v -u

RMFR := rm -fr
MKDIR := mkdir -pv

.PHONY: all clean install-deps

# generate protobuf sources
all: $(PROTOC_GEN_GO) $(OUT)
	@echo "Done"

# target directory of protobuf go sources
$(OUT):
	@echo "Generating protobuf"
	$(MKDIR) $(OUT)
	$(PROTOC) --go_out=plugins=grpc:$(OUT) --go_opt=paths=source_relative *.proto

# target location of protoc-gen-go tool
$(PROTOC_GEN_GO):
	@echo "Installing protobuf tools"
	$(GOGET) github.com/golang/protobuf/protoc-gen-go
	$(GOGET) google.golang.org/grpc/cmd/protoc-gen-go-grpc@v1.0

# clean target directory
clean:
	$(RMFR) $(OUT)

# install required dependencies
install-deps: $(PROTOC_GEN_GO)

