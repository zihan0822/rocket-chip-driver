foreach file [split $::env(VERILOG_FILES)] {
    yosys read_verilog -sv $file
}
yosys hierarchy -top $::env(TOP_MODULE) -check
yosys prep -top $::env(TOP_MODULE) 
yosys memory_dff
yosys memory_collect
yosys flatten
yosys memory_nordff
yosys memory_unpack
yosys splitnets -driver
yosys setundef -undriven -init -zero
yosys opt
yosys async2sync
yosys dffunmap
yosys write_btor -s $::env(BTOR_OUTPUT) 
