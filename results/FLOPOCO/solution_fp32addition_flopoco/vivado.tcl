set rtl_dir "/home/joe/Desktop/Uni/Year_4/Dissertation/Program-Synthesis-for-Efficient-ML/results/FLOPOCO/solution_fp32addition_flopoco/verilog_out"
set vhd_files [glob -nocomplain "$rtl_dir/*.vhd"]
if {[llength $vhd_files] == 0} {
  puts "ERROR: No VHDL files found in $rtl_dir"
  exit 1
}
read_vhdl $vhd_files
synth_design -top fp32_sum_flopoco -part xc7z020clg400-1
create_clock -name ap_clk -period 4.000 [get_ports ap_clk]
opt_design
place_design
route_design
report_utilization -file /home/joe/Desktop/Uni/Year_4/Dissertation/Program-Synthesis-for-Efficient-ML/results/FLOPOCO/solution_fp32addition_flopoco/utilization.rpt
report_timing_summary -file /home/joe/Desktop/Uni/Year_4/Dissertation/Program-Synthesis-for-Efficient-ML/results/FLOPOCO/solution_fp32addition_flopoco/timing.rpt
report_timing -delay_type max -max_paths 1 -nworst 1 -file /home/joe/Desktop/Uni/Year_4/Dissertation/Program-Synthesis-for-Efficient-ML/results/FLOPOCO/solution_fp32addition_flopoco/timing_detail.rpt
exit
