open_component -reset solution_addition_overflow_component -flow_target vivado
    set_top detect_overflow
    add_files /home/joe/Desktop/Uni/Year_4/Dissertation/Program-Synthesis-for-Efficient-ML/results/cpp/solution_addition_overflow.cpp
    set_part {xc7z020clg400-1}
    create_clock -period 1000000000ns
    csynth_design
    export_design -rtl verilog
