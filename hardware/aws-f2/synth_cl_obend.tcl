# =============================================================================
# AWS EC2 F2 (`xcvu47p-fsvh2892-2-e`) Non-Project Vivado Synthesis & Place/Route
# Script (`hardware/aws-f2/synth_cl_obend.tcl`)
# =============================================================================
# Usage:
#   vivado -mode batch -source hardware/aws-f2/synth_cl_obend.tcl
#
# Synthesizes `cl_obend_shell_bridge` (including `silicon_elab_top`, the 5
# UltraScale+ macros, and the compiler-emitted `.obend` physical cores),
# applies 250 MHz (`4.000 ns`) timing constraints and SLR0..SLR2 pblock
# floorplanning (`SLR0`: Zone 1 ExprCAM + Zone 3 DiscrTreeLUT, `SLR1`: Zone 2
# NoC Unifier + Zone 4 Kernel FSM + ICAP DPR Tile, `SLR2`: `.obend` physical
# cores & PCIS 512-bit AXI4-Stream DMA bridge), and writes `cl_obend_routed.dcp`
# for AWS EC2 F2 AFI creation (`aws ec2 create-fpga-image`).
# =============================================================================

set PART_NAME "xcvu47p-fsvh2892-2-e"
set TOP_MODULE "cl_obend_shell_bridge"
set BUILD_DIR  [file normalize [file join [file dirname [info script]] "build"]]
file mkdir $BUILD_DIR

puts "\[OBEND-F2\] Reading compiler-emitted SystemVerilog RTL and AWS F2 shell bridge..."
read_verilog -sv [list \
  [file normalize [file join [file dirname [info script]] "../sim/cleanroom_tcad_stack.sv"]] \
  [file normalize [file join [file dirname [info script]] "../sim/lc_drives_userspace_stator.sv"]] \
  [file normalize [file join [file dirname [info script]] "../sim/cnc_5axis_userspace_mill.sv"]] \
  [file normalize [file join [file dirname [info script]] "../sim/obend_retimed_mac2.sv"]] \
  [file normalize [file join [file dirname [info script]] "../sim/silicon_elab_top.sv"]] \
  [file normalize [file join [file dirname [info script]] "cl_obend_shell_bridge.sv"]] \
]

puts "\[OBEND-F2\] Running synth_design for $TOP_MODULE on $PART_NAME..."
synth_design \
  -top $TOP_MODULE \
  -part $PART_NAME \
  -mode out_of_context \
  -flatten_hierarchy rebuilt \
  -directive AlternateRoutability \
  -retiming

# Primary 250 MHz (4.000 ns) AWS F2 `clk_main_a0` constraint
create_clock -period 4.000 -name clk_main_a0 [get_ports clk_main_a0]
set_clock_uncertainty 0.120 [get_clocks clk_main_a0]

# SLR Floorplanning Pblocks across VU47P Super Logic Regions (SLR0, SLR1, SLR2)
create_pblock pblock_slr0_cam_lut
resize_pblock pblock_slr0_cam_lut -add {SLR0}
add_cells_to_pblock pblock_slr0_cam_lut [get_cells -quiet [list \
  u_cl_silicon_elab/u_zone1 \
  u_cl_silicon_elab/u_zone3 \
]]

create_pblock pblock_slr1_noc_kernel_dpr
resize_pblock pblock_slr1_noc_kernel_dpr -add {SLR1}
add_cells_to_pblock pblock_slr1_noc_kernel_dpr [get_cells -quiet [list \
  u_cl_silicon_elab/u_zone2 \
  u_cl_silicon_elab/u_zone4 \
  u_cl_silicon_elab/u_dpr_tile \
]]

create_pblock pblock_slr2_phys_dma
resize_pblock pblock_slr2_phys_dma -add {SLR2}
add_cells_to_pblock pblock_slr2_phys_dma [get_cells -quiet [list \
  u_cl_tcad \
  u_cl_stator \
  u_cl_mill \
  u_pcis_h2c_skid \
]]

puts "\[OBEND-F2\] Running opt_design, place_design, phys_opt_design, route_design..."
opt_design -directive Explore
place_design -directive ExtraPostPlacementOpt
phys_opt_design -directive AggressiveExplore
route_design -directive AggressiveExplore

report_utilization -file [file join $BUILD_DIR "utilization_route.rpt"]
report_timing_summary -max_paths 20 -file [file join $BUILD_DIR "timing_summary_route.rpt"]
report_drc -file [file join $BUILD_DIR "drc_route.rpt"]

write_checkpoint -force [file join $BUILD_DIR "cl_obend_routed.dcp"]
puts "\[OBEND-F2\] Wrote AWS F2 Custom Logic checkpoint: $BUILD_DIR/cl_obend_routed.dcp"
