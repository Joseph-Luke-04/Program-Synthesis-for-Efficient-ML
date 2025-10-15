open_component -reset solution_multiplication_mant_component -flow_target vivado
    set_top mult_mxint_mant

    # Design sources
    add_files /home/joe/Desktop/Uni/Year_4/Dissertation/Program-Synthesis-for-Efficient-ML/results/cpp/solution_multiplication_mant.cpp

    # Target device & clock
    set_part {xc7z020clg400-1}
    create_clock -period 4

    # Synthesize to RTL (no csim/cosim since there is no main())
    csynth_design

    # Export RTL + reports
    export_design -format ip_catalog -rtl verilog -output /home/joe/Desktop/Uni/Year_4/Dissertation/Program-Synthesis-for-Efficient-ML/results/HLS/solution_multiplication_mant/solution_multiplication_mant_export
