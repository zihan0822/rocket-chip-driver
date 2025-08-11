DESIGNS_DIR := $(wildcard designs/*)
DESIGN_VERILOG:= TestHarness.sv
TOP_MODULE := TestHarness

YOSYS_SCRIPT := verilog2btor.tcl
VERILOG_RESOURCES := resources/verilog/*
BTOR_TARGET := $(patsubst %.sv,%.btor,$(foreach dir,$(DESIGNS_DIR),$(dir)/$(DESIGN_VERILOG)))

.PHONY: clean 

all: btor emulator

btor: $(BTOR_TARGET)

emulator:
	@make -C resources emulator 

%.btor: $(YOSYS_SCRIPT) $(VERILOG_RESOURCES) %.sv
	@VERILOG_FILES="$(VERILOG_RESOURCES) $*.sv" \
	TOP_MODULE=$(TOP_MODULE) \
	BTOR_OUTPUT=$@ \
		yosys $(YOSYS_SCRIPT)

clean:
	@for design in $(DESIGNS_DIR); do \
		rm -f $$design/$(BTOR_OUTPUT); \
	done


