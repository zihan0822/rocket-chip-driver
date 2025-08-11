RUST_PROFILE := release
RUST_TARGET_DIR := $(realpath -f ../target)
RUST_LIB_DIR := $(RUST_TARGET_DIR)/$(RUST_PROFILE)
CXX_DIR := $(shell pwd)/cxx
RISCV_SIM := $(CXX_DIR)/riscv-fesvr
RISCV_DIR:= $(CXX_DIR)/riscv
RISCV_TOOLCHAIN := riscv64-unknown-elf

LDFLAGS += -L$(RUST_LIB_DIR) -L$(RISCV_DIR)/lib
INCLUDES += -I$(RUST_TARGET_DIR) -I$(RISCV_DIR)/include
LINKER_ARGS := -Wl,-rpath,$(RUST_LIB_DIR) -Wl,-rpath,$(RISCV_DIR)/lib
LIBS += -lrocket_chip_driver -lfesvr -lpthread

ifeq ($(RUST_PROFILE),release)
	CARGO_FLAGS := --release
else 
	CARGO_FLAGS :=
endif

PHONY := clean rocket_chip_driver

all: emulator 
	
run: emulator
	@LD_LIBRARY_PATH=$(RUST_LIB_DIR) ./$<

libfesvr.so:
	@mkdir -p $(RISCV_DIR)
	@cd $(RISCV_SIM) && mkdir -p build && cd build && \
		../configure --prefix=$(RISCV_DIR) --target=$(RISCV_TOOLCHAIN) && make install

emulator: $(CXX_DIR)/emulator.cc rocket_chip_driver libfesvr.so
	@$(CXX) -o $@ $< $(LDFLAGS) $(INCLUDES) $(LIBS) $(LINKER_ARGS)

rocket_chip_driver:
	@cargo build $(CARGO_FLAGS) 

clean:
	@rm -f emulator
	@rm -rf $(RISCV_SIM)/build