foreach file [split $::env(VERILOG_FILES)] {
    yosys read_verilog -sv $file
}
yosys hierarchy -top $::env(TOP_MODULE) -check
yosys proc
yosys flatten
yosys opt_clean
yosys wreduce -keepdc 
yosys memory_dff
yosys memory_collect
yosys opt_clean
yosys memory_nordff
yosys async2sync
yosys dffunmap
yosys write_btor -s $::env(BTOR_OUTPUT) 
