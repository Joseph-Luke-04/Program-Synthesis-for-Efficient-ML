# --- Non-project flow: read RTL, synth, implement, report ---

    # Collect RTL
    set v_files  [glob -nocomplain {/home/joe/Desktop/Uni/Year_4/Dissertation/Program-Synthesis-for-Efficient-ML/results/HLS/solution_multiplication_mant/verilog_out/*.v}]
    set sv_files [glob -nocomplain {/home/joe/Desktop/Uni/Year_4/Dissertation/Program-Synthesis-for-Efficient-ML/results/HLS/solution_multiplication_mant/verilog_out/*.sv}]
    if {[llength $v_files] == 0 && [llength $sv_files] == 0} {
      puts "ERROR: No RTL files found in /home/joe/Desktop/Uni/Year_4/Dissertation/Program-Synthesis-for-Efficient-ML/results/HLS/solution_multiplication_mant/verilog_out"
      exit 1
    }
    if {[llength $v_files]  > 0} { read_verilog $v_files }
    foreach f $sv_files { read_verilog -sv $f }

    # Synthesis
    synth_design -top mult_mxint_mant -part xc7z020clg400-1

    # Add a clock ONLY if the port exists (combinational designs won't have ap_clk)
    if {[llength [get_ports -quiet ap_clk]]} {
      create_clock -name ap_clk -period 4.000 [get_ports ap_clk]
    } else {
      puts "INFO: No ap_clk port found; skipping create_clock (design appears combinational)."
    }

    # Implementation
    opt_design
    place_design
    route_design

    # Reports
    report_utilization    -file /home/joe/Desktop/Uni/Year_4/Dissertation/Program-Synthesis-for-Efficient-ML/results/HLS/solution_multiplication_mant/utilization.rpt
    report_timing_summary -file /home/joe/Desktop/Uni/Year_4/Dissertation/Program-Synthesis-for-Efficient-ML/results/HLS/solution_multiplication_mant/timing.rpt

    # Try XML (RPX) timing if supported (avoid nested braces in catch)
    set rpx_path "/home/joe/Desktop/Uni/Year_4/Dissertation/Program-Synthesis-for-Efficient-ML/results/HLS/solution_multiplication_mant/timing.rpx"
    if {[catch {report_timing_summary -rpx $rpx_path} err]} {
      puts "INFO: RPX timing not available: $err"
    }
