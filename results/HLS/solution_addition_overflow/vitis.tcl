open_component -reset solution_addition_overflow_component -flow_target vivado
    set_top detect_overflow

    # Design sources
    add_files /home/joe/Desktop/Uni/Year_4/Dissertation/Program-Synthesis-for-Efficient-ML/results/cpp/solution_addition_overflow.cpp

    # Target device & clock
    set_part {xc7z020clg400-1}
    create_clock -period 4

    # Synthesize to RTL (no csim/cosim since there is no main())
    csynth_design

    # Export RTL + reports
    export_design -format ip_catalog -rtl verilog -output /home/joe/Desktop/Uni/Year_4/Dissertation/Program-Synthesis-for-Efficient-ML/results/HLS/solution_addition_overflow/solution_addition_overflow_export
