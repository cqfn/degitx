OUT := ${CURDIR}/..
GOPATH := $(shell go env GOPATH)
PROTOC_GEN_GO := $(GOPATH)/bin/protoc-gen-go
PROTOC := env PATH="$(GOPATH)/bin:${PATH}" protoc
PREFIX := cqfn.org/degitx
GOOPT := module=$(PREFIX)
# directories where the .proto files are located.
PATHS := tcommit/ discovery/ paxos/
# set -I(alias to --proto_path) flag for each path.
PROTO_PATHS_FLAGS := $(foreach pth,$(PATHS),-I=$(pth))
# protoc input files
INPUT_FILES := $(foreach pth,$(PATHS),$(pth)/*.proto)
RMFR := rm -fr
MKDIR := mkdir -pv
GOGET := env GO111MODULE=off go get -v

.PHONY: all clean install-deps

# generate protobuf sources
all: $(PROTOC_GEN_GO) $(OUT)
	$(PROTOC) --go_out=$(OUT) --go_opt=$(GOOPT) $(PROTO_PATHS_FLAGS) \
	--go-grpc_out=$(OUT) --go-grpc_opt=$(GOOPT) $(INPUT_FILES)

# target directory of protobuf go sources
$(OUT):
	$(MKDIR) $(OUT)

# target location of protoc-gen-go tool
$(PROTOC_GEN_GO):
	$(GOGET) google.golang.org/protobuf/cmd/protoc-gen-go
	$(GOGET) google.golang.org/grpc/cmd/protoc-gen-go-grpc
# clean target directory
clean:
	@echo "nothing to clean"

# install required dependencies
install-deps: $(PROTOC_GEN_GO)

