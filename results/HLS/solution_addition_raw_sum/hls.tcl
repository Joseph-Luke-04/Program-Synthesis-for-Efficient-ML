open_component -reset solution_addition_raw_sum_component -flow_target vivado
    set_top add_raw
    add_files /home/joe/Desktop/Uni/Year_4/Dissertation/Program-Synthesis-for-Efficient-ML/results/cpp/solution_addition_raw_sum.cpp
    set_part {xc7z020clg400-1}
    create_clock -period 1000000000ns
    csynth_design
    export_design -rtl verilog
