RUST_PROFILE := release
RUST_TARGET_DIR := $(realpath -f ../target)
RUST_LIB_DIR := $(RUST_TARGET_DIR)/$(RUST_PROFILE)
RISCV_SIM := riscv-fesvr

LDFLAGS += -L$(RUST_LIB_DIR)
INCLUDES += -I$(RUST_TARGET_DIR) -I$(RISCV_SIM)
LINKER_ARGS := -Wl,-rpath,$(RUST_LIB_DIR)
LIBS += -lrocket_chip_driver

ifeq ($(RUST_PROFILE),release)
	CARGO_FLAGS := --release
else 
	CARGO_FLAGS :=
endif

PHONY := clean rocket_chip_driver

all: emulator 
	
run: emulator
	@LD_LIBRARY_PATH=$(RUST_LIB_DIR) ./$<

emulator: emulator.cc rocket_chip_driver
	@$(CXX) -o $@ $< $(LDFLAGS) $(INCLUDES) $(LIBS) $(LINKER_ARGS)

rocket_chip_driver:
	@cargo build $(CARGO_FLAGS) 

clean:
	@rm -f emulator