# Maps component keys (targets) to lists of dependency component keys (the building blocks).

DEPENDENCY_MAP = {
    # MXINT8 Addition
    "addition_alignment": [],
    "addition_overflow": [],
    "addition_normalisation": ["addition_overflow"],
    "addition_raw_sum": ["addition_alignment"],
    "addition_full_sum": [
        "addition_alignment",
        "addition_raw_sum",
        "addition_overflow",
        "addition_normalisation",
    ],
    # MXINT8 Addition (class-name-prefixed outputs)
    "mxint8addition_alignment": [],
    "mxint8addition_overflow": [],
    "mxint8addition_normalisation": ["mxint8addition_overflow"],
    "mxint8addition_raw_sum": ["mxint8addition_alignment"],
    "mxint8addition_full_sum": [
        "mxint8addition_alignment",
        "mxint8addition_raw_sum",
        "mxint8addition_overflow",
        "mxint8addition_normalisation",
    ],

    # MXINT8 Multiplication
    "multiplication_renorm_flag": [],
    "multiplication_exp": ["multiplication_renorm_flag"],
    "multiplication_mant": [],
    "multiplication_full_product": [
        "multiplication_renorm_flag",
        "multiplication_exp",
        "multiplication_mant",
    ],
    # MXINT8 Multiplication (class-name-prefixed outputs)
    "mxint8multiplication_renorm_flag": [],
    "mxint8multiplication_exp": ["mxint8multiplication_renorm_flag"],
    "mxint8multiplication_mant": [],
    "mxint8multiplication_full_product": [
        "mxint8multiplication_renorm_flag",
        "mxint8multiplication_exp",
        "mxint8multiplication_mant",
    ],

    # FP32 Addition
    "fp32addition_fp32_alignment": [],
    "fp32addition_fp32_normalisation": [],
    "fp32addition_fp32_full_sum": [
        "fp32addition_fp32_alignment",
        "fp32addition_fp32_raw_sum",
        "fp32addition_fp32_normalisation",
    ],

    # FP32 Multiplication
    "fp32multiplication_renorm": [],
    "fp32multiplication_exp": ["fp32multiplication_renorm"],
    "fp32multiplication_mant": [],
    "fp32multiplication_full_product": [
        "fp32multiplication_renorm",
        "fp32multiplication_exp",
        "fp32multiplication_mant",
    ],
}
