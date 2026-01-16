set clock_constraint { \
    name clk \
    module fp32_sum \
    port ap_clk \
    period 1e+06 \
    uncertainty 270000 \
}

set all_path {}

set false_path {}

