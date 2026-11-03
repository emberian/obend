VERILATOR ?= /opt/homebrew/bin/verilator
TOP_MODULE := silicon_elab_top
SV_SRC := silicon_elab_top.sv
CPP_SRC := sim_main.cpp
BIN := obj_dir/V$(TOP_MODULE)
VCD := silicon_elab_wave.vcd

.PHONY: all run clean

all: $(BIN)

$(BIN): $(SV_SRC) $(CPP_SRC)
	$(VERILATOR) -Wall -Wno-DECLFILENAME --cc --exe --build --trace \
		--top-module $(TOP_MODULE) $(SV_SRC) $(CPP_SRC)

run: $(BIN)
	./$(BIN) $(VCD)

clean:
	rm -rf obj_dir $(VCD)
