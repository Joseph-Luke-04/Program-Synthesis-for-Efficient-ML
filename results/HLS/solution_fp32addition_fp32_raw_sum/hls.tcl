open_component -reset solution_fp32addition_fp32_raw_sum_component -flow_target vivado
    set_top fp32_raw_summer
    add_files /home/joe/Desktop/Uni/Year_4/Dissertation/Program-Synthesis-for-Efficient-ML/results/cpp/solution_fp32addition_fp32_raw_sum.cpp
    set_part {xc7z020clg400-1}
    create_clock -period 50ns
    csynth_design
    export_design -rtl verilog
