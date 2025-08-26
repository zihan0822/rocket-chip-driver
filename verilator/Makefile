DESIGN := rocket-latest
VERILATOR := verilator
VERILOG_RESOURCES := ../resources/verilog/*
VERILATOR_SYSTEM_PATH := /usr/share/verilator
TOP_MODULE := TestHarness
RISCV_SIM := ../resources/cxx/riscv


INCLUDES += -Iobj_dir -I$(RISCV_SIM)/include -I$(VERILATOR_SYSTEM_PATH)/include
LDFLAGS += -L$(RISCV_SIM)/lib
LIBS += -lfesvr -lpthread

all: emulator

verilator:
	$(VERILATOR) --sv --cc ../designs/$(DESIGN)/TestHarness.sv $(VERILOG_RESOURCES) \
		--top-module $(TOP_MODULE)

emulator: emulator.o
	$(CXX) -o $@ $< obj_dir/*.o $(LDFLAGS) $(LIBS)

emulator.o: emulator.cc 
	$(CXX) -c $@ $< $(INCLUDES) 