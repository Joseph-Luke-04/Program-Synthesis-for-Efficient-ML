open_component -reset solution_addition_alignment_component -flow_target vivado
    set_top select_exponent
    add_files /home/joe/Desktop/Uni/Year_4/Dissertation/Program-Synthesis-for-Efficient-ML/results/cpp/solution_addition_alignment.cpp
    set_part {xc7z020clg400-1}
    create_clock -period 4ns
    csynth_design
    export_design -rtl verilog
