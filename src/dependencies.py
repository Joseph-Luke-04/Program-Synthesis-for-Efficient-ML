# Maps component keys (targets) to lists of dependency component keys (the building blocks).

DEPENDENCY_MAP = {
    # MXINT8 
    "addition_alignment": [],
    "addition_normalisation": [],
    "addition_raw_sum": ["addition_alignment"],
    "addition_full_sum": [
        "addition_alignment",
        "addition_raw_sum",
        "addition_normalisation",
    ],

    # FP32 
    "fp32addition_fp32_alignment": [],
    "fp32addition_fp32_normalisation": [],
    "fp32addition_fp32_full_sum": [
        "fp32addition_fp32_alignment",
        "fp32addition_fp32_raw_sum",
        "fp32addition_fp32_normalisation",
    ],
}