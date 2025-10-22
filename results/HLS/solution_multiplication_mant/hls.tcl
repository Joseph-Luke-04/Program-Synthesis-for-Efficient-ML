open_component -reset solution_multiplication_mant_component -flow_target vivado
    set_top mult_mxint_mant
    add_files /home/joe/Desktop/Uni/Year_4/Dissertation/Program-Synthesis-for-Efficient-ML/results/cpp/solution_multiplication_mant.cpp
    set_part {xc7z020clg400-1}
    create_clock -period 4ns
    csynth_design
    export_design -rtl verilog
