# iCEstick (iCE40HX1K) bitstream for the Lean-emitted obend_ice40_mac8 (yosys + nextpnr-ice40 + icestorm).
#   make        -> top_icestick.bin
#   make prog   -> iceprog it
#   make check  -> byte-equality of obend_ice40_mac8.sv with the Lean emitter
REPO_ROOT := $(abspath $(dir $(lastword $(MAKEFILE_LIST)))/../..)
EMIT ?= $(REPO_ROOT)/lean/.lake/build/bin/obend-emit-sv
YOSYS ?= yosys
NEXTPNR ?= nextpnr-ice40
ICEPACK ?= icepack
ICEPROG ?= iceprog

all: top_icestick.bin

check:
	$(EMIT) ice40-mac8 --out /tmp/obend_ice40_mac8.sv >/dev/null
	cmp /tmp/obend_ice40_mac8.sv obend_ice40_mac8.sv

lint:
	verilator --lint-only -Wall -Wno-DECLFILENAME -Wno-UNUSED --top-module top_icestick obend_ice40_mac8.sv top_icestick.sv

top_icestick.json: top_icestick.sv obend_ice40_mac8.sv
	$(YOSYS) -q -l synth.log -p "read_verilog -sv obend_ice40_mac8.sv top_icestick.sv; synth_ice40 -top top_icestick -json $@"

top_icestick.asc: top_icestick.json icestick.pcf
	$(NEXTPNR) --hx1k --package tq144 --pcf icestick.pcf --json $< --asc $@ --freq 12 -l pnr.log -q

top_icestick.bin: top_icestick.asc
	$(ICEPACK) $< $@

prog: top_icestick.bin
	$(ICEPROG) $<

clean:
	rm -f top_icestick.json top_icestick.asc top_icestick.bin synth.log pnr.log

.PHONY: all check lint prog clean
