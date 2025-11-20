open_component -reset solution_fp32addition_fp32_alignment_component -flow_target vivado
    set_top fp32_aligner
    add_files /home/joe/Desktop/Uni/Year_4/Dissertation/Program-Synthesis-for-Efficient-ML/results/cpp/solution_fp32addition_fp32_alignment.cpp
    set_part {xc7z020clg400-1}
    create_clock -period 50ns
    csynth_design
    export_design -rtl verilog
