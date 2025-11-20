SIM              ?= icarus
TOPLEVEL_LANG    ?= verilog
TOPLEVEL         ?= mxint8_sum
MODULE           ?= tests.test_mxint8_adder

HLS_BASE 	  	 ?= ../results/HLS
HLS_SOLN   	 	 ?= 
HLS_OUT_DIR		 := $(abspath $(HLS_BASE)/$(HLS_SOLN)/verilog_out)

# Require the user to pass the subfolder
ifeq ($(strip $(HLS_SOLN)),)
  $(error Set HLS_SOLN=solution_... (subdir under $(HLS_BASE)))
endif

# Pick up all generated RTL in that verilog_out
VERILOG_SOURCES := $(wildcard $(HLS_OUT_DIR)/*.v)
ifeq ($(strip $(VERILOG_SOURCES)),)
  $(error No Verilog found in $(HLS_OUT_DIR))
endif

include $(shell cocotb-config --makefiles)/Makefile.sim
