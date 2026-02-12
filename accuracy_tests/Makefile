SIM              ?= icarus
TOPLEVEL_LANG    ?= verilog
TOPLEVEL         ?= mxint8_sum
MODULE           ?= tests.test_mxint8_adder

HLS_BASE 	  	 ?= ../results/HLS
HLS_SOLN   	 	 ?= 
HLS_OUT_DIR		 := $(abspath $(HLS_BASE)/$(HLS_SOLN)/verilog_out)

# Unique build dir per solution + top (prevents stale .vvp reuse)
SIM_BUILD      ?= $(abspath sim_build/$(TOPLEVEL)_$(notdir $(HLS_SOLN)))

# Require the user to pass the subfolder
ifeq ($(strip $(HLS_SOLN)),)
  $(error Set HLS_SOLN=solution_... (subdir under $(HLS_BASE)))
endif

# Pick up generated RTL under verilog_out, based on selected HDL.
ifeq ($(TOPLEVEL_LANG),vhdl)
  VHDL_SOURCES := $(wildcard $(HLS_OUT_DIR)/*.vhd) $(wildcard $(HLS_OUT_DIR)/*.vhdl)
  ifeq ($(strip $(VHDL_SOURCES)),)
    $(error No VHDL found in $(HLS_OUT_DIR))
  endif
else
  VERILOG_SOURCES := $(wildcard $(HLS_OUT_DIR)/*.v)
  ifeq ($(strip $(VERILOG_SOURCES)),)
    $(error No Verilog found in $(HLS_OUT_DIR))
  endif
endif

include $(shell cocotb-config --makefiles)/Makefile.sim
