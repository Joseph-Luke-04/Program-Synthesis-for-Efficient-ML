import re

# =====================================================================
# Canonicalisation functions for MXINT8 addition
# =====================================================================

import re

def _canonicalise_mxint8_alignment(code: str) -> str:
    """
    Overwrite align_mantissas with a rounded, sign-aware right-shift for the
    smaller-exponent operand. Rounds to nearest (sign-biased), saturates to [-8, 7].
    Uses widened temps to avoid ?: width ambiguity in HLS.
    """
    func_re = re.compile(
        r'^\s*ap_uint<\s*8\s*>\s+align_mantissas\s*'
        r'\(\s*ap_uint<\s*4\s*>\s*\w+\s*,\s*ap_uint<\s*4\s*>\s*\w+\s*,\s*'
        r'ap_uint<\s*4\s*>\s*\w+\s*,\s*ap_uint<\s*4\s*>\s*\w+\s*\)\s*\{.*?\}\s*',
        re.DOTALL | re.MULTILINE
    )

    replacement = (
        "ap_uint<8> align_mantissas(ap_uint<4> m1, ap_uint<4> e1, ap_uint<4> m2, ap_uint<4> e2) {\n"
        "  ap_int<4> s1 = (ap_int<4>)m1;\n"
        "  ap_int<4> s2 = (ap_int<4>)m2;\n"
        "  ap_int<4> de = (ap_int<4>)e1 - (ap_int<4>)e2;\n"
        "  ap_int<4> a1, a2;\n"
        "  if (de >= 0) {\n"
        "    a1 = s1;\n"
        "    if (de == 0) {\n"
        "      a2 = s2;\n"
        "    } else {\n"
        "      ap_uint<4> d = (ap_uint<4>)de;          // d >= 1 here\n"
        "      ap_int<16> t  = (ap_int<16>)s2;         // widen for safe rounding\n"
        "      ap_int<16> mag = ((ap_int<16>)1) << (d - 1);\n"
        "      ap_int<16> sgn = (t >= 0) ? (ap_int<16>)1 : (ap_int<16>)-1;\n"
        "      t = (t + sgn * mag) >> d;               // round-to-nearest, sign-aware\n"
        "      if (t > 7) t = 7; if (t < -8) t = -8;\n"
        "      a2 = (ap_int<4>)t;\n"
        "    }\n"
        "  } else {\n"
        "    ap_uint<4> d = (ap_uint<4>)(-de);\n"
        "    a2 = s2;\n"
        "    if (d == 0) {\n"
        "      a1 = s1;\n"
        "    } else {\n"
        "      ap_int<16> t  = (ap_int<16>)s1;         // widen for safe rounding\n"
        "      ap_int<16> mag = ((ap_int<16>)1) << (d - 1);\n"
        "      ap_int<16> sgn = (t >= 0) ? (ap_int<16>)1 : (ap_int<16>)-1;\n"
        "      t = (t + sgn * mag) >> d;               // round-to-nearest, sign-aware\n"
        "      if (t > 7) t = 7; if (t < -8) t = -8;\n"
        "      a1 = (ap_int<4>)t;\n"
        "    }\n"
        "  }\n"
        "  return (ap_uint<8>)((((ap_uint<8>)(ap_uint<4>)a1) << 4) | (ap_uint<4>)a2);\n"
        "}\n"
    )
    return func_re.sub(replacement, code)


def _canonicalise_mxint8_raw_adder(code: str) -> str:
    """
    Overwrite add_raw with a width-safe version that:
      - aligns once,
      - slices nibbles with .range(7,4)/(3,0),
      - applies sign after slicing,
      - sums in 5 bits,
      - packs {sum, exp} into 9 bits.
    """
    func_re = re.compile(
        r'^\s*ap_uint<\s*9\s*>\s+add_raw\s*'
        r'\(\s*ap_uint<\s*4\s*>\s*\w+\s*,\s*ap_uint<\s*4\s*>\s*\w+\s*,\s*'
        r'ap_uint<\s*4\s*>\s*\w+\s*,\s*ap_uint<\s*4\s*>\s*\w+\s*\)\s*\{.*?\}\s*',
        re.DOTALL | re.MULTILINE
    )

    replacement = (
        "ap_uint<9> add_raw(ap_uint<4> m1, ap_uint<4> e1, ap_uint<4> m2, ap_uint<4> e2) {\n"
        "  ap_uint<8> aligned = align_mantissas(m1, e1, m2, e2);\n"
        "  ap_int<4> a = (ap_int<4>)((ap_uint<4>)aligned.range(7, 4));\n"
        "  ap_int<4> b = (ap_int<4>)((ap_uint<4>)aligned.range(3, 0));\n"
        "  ap_uint<5> sum = (ap_uint<5>)((ap_int<5>)a + (ap_int<5>)b);\n"
        "  ap_uint<4> texp = select_exponent(e1, e2);\n"
        "  return (ap_uint<9>)((((ap_uint<9>)sum) << 4) | texp);\n"
        "}\n"
    )
    return func_re.sub(replacement, code)


def _canonicalise_mxint8_normaliser_rounded(code: str) -> str:
    """
    Overwrite normalise_addition to use round-to-nearest (sign-aware) on overflow.
    Uses same-width ?: arms to avoid Vitis HLS conditional ambiguity.
    """
    func_re = re.compile(
        r'^\s*ap_uint<\s*8\s*>\s+normalise_addition\s*'
        r'\(\s*ap_uint<\s*5\s*>\s*\w+\s*,\s*ap_uint<\s*4\s*>\s*\w+\s*\)\s*\{.*?\}\s*',
        re.DOTALL | re.MULTILINE
    )

    replacement = (
        "ap_uint<8> normalise_addition(ap_uint<5> raw_sum, ap_uint<4> target_exp) {\n"
        "  ap_int<5> s5 = (ap_int<5>)raw_sum;\n"
        "  ap_uint<4> exp = target_exp;\n"
        "  ap_int<4> mant;\n"
        "  if (s5 > 7 || s5 < -8) {\n"
        "    ap_int<6> t = (ap_int<6>)s5;\n"
        "    ap_int<6> sgn = (t >= 0) ? (ap_int<6>)1 : (ap_int<6>)-1; // same type both arms\n"
        "    t = t + sgn;                                            // +0.5 ulp before >>1\n"
        "    t >>= 1;\n"
        "    if (t > 7) t = 7; if (t < -8) t = -8;\n"
        "    mant = (ap_int<4>)t;\n"
        "    exp  = exp + 1;\n"
        "  } else {\n"
        "    mant = (ap_int<4>)s5;\n"
        "  }\n"
        "  return (ap_uint<8>)((((ap_uint<8>)((ap_uint<4>)mant)) << 4) | exp);\n"
        "}\n"
    )
    return func_re.sub(replacement, code)

def _canonicalise_add_full_sum(code: str) -> str:
    if "add_full_sum(" not in code:
        return code
    m = re.search(r'\b(ap_uint<\d+>|unsigned\s+char)\s+add_full_sum\s*\([^)]*\)\s*\{', code)
    if not m:
        return code

    start = m.start()
    # find matching closing brace
    i = m.end() - 1
    depth = 0; end = None
    while i < len(code):
        if code[i] == '{': depth += 1
        elif code[i] == '}':
            depth -= 1
            if depth == 0:
                end = i + 1; break
        i += 1
    if end is None:
        return code

    new_body = r"""
ap_uint<8> add_full_sum(ap_uint<4> m1, ap_uint<4> e1, ap_uint<4> m2, ap_uint<4> e2) {
  ap_uint<9> raw = add_raw(m1, e1, m2, e2);
  ap_uint<5> raw_m = (ap_uint<5>) raw.range(8, 4);
  ap_uint<4> texp  = (ap_uint<4>) raw.range(3, 0);
  return normalise_addition(raw_m, texp);
}
""".strip("\n")

    return code[:start] + new_body + "\n" + code[end:]

# =====================================================================
# Canonicalisation functions for FP32 addition
# =====================================================================

# =====================================================================
# Canonicalisation functions for MXINT8 multiplication
# =====================================================================

def _canonicalise_mxint8_mult_renorm_flag(code: str) -> str:
    """
    Replace mult_renorm_flag with a clear, width-stable implementation.
    """
    func_re = re.compile(
        r'^\s*ap_uint<\s*1\s*>\s+mult_renorm_flag\s*'
        r'\(\s*ap_uint<\s*4\s*>\s*\w+\s*,\s*ap_uint<\s*4\s*>\s*\w+\s*\)\s*\{.*?\}\s*',
        re.DOTALL | re.MULTILINE
    )

    replacement = (
        "ap_uint<1> mult_renorm_flag(ap_uint<4> m1, ap_uint<4> m2) {\n"
        "  ap_int<4> s1 = (ap_int<4>)m1;\n"
        "  ap_int<4> s2 = (ap_int<4>)m2;\n"
        "  ap_int<8> prod = (ap_int<8>)(s1 * s2);\n"
        "  ap_int<8> abs_p = (prod < 0) ? (ap_int<8>)-prod : prod;\n"
        "  return (abs_p <= (ap_int<8>)32) ? (ap_uint<1>)1 : (ap_uint<1>)0;\n"
        "}\n"
    )
    return func_re.sub(replacement, code)


def _canonicalise_mxint8_mult_mant(code: str) -> str:
    """
    Replace mult_mxint_mant with a direct, width-stable implementation.
    """
    func_re = re.compile(
        r'^\s*ap_uint<\s*4\s*>\s+mult_mxint_mant\s*'
        r'\(\s*ap_uint<\s*4\s*>\s*\w+\s*,\s*ap_uint<\s*4\s*>\s*\w+\s*\)\s*\{.*?\}\s*',
        re.DOTALL | re.MULTILINE
    )

    replacement = (
        "ap_uint<4> mult_mxint_mant(ap_uint<4> m1, ap_uint<4> m2) {\n"
        "  ap_int<4> s1 = (ap_int<4>)m1;\n"
        "  ap_int<4> s2 = (ap_int<4>)m2;\n"
        "  ap_int<8> prod = (ap_int<8>)(s1 * s2);\n"
        "  ap_int<8> abs_p = (prod < 0) ? (ap_int<8>)-prod : prod;\n"
        "  ap_int<8> inter = (abs_p <= (ap_int<8>)32)\n"
        "                  ? (ap_int<8>)((prod << 1) >> 3)\n"
        "                  : (ap_int<8>)(prod >> 3);\n"
        "  return (ap_uint<4>)inter;\n"
        "}\n"
    )
    return func_re.sub(replacement, code)

def _canonicalise_fp32_aligner(code: str) -> str:
    """
    Replace the entire fp32_aligner(...) with a width-safe version that:
      - builds 24-bit significands as {hidden1, mantissa} (hidden1=1 if exp!=0),
      - right-shifts only the smaller-exponent operand by |e1-e2|,
      - packs [55:32]=aligned m1, [31:8]=aligned m2, [7:0]=target exponent,
      - uses <<32 and <<8 (not 52!) and ORs to avoid comma-operator bugs.
    """
    if "fp32_aligner(" not in code:
        return code

    m = re.search(
        r'\b(?:ap_uint<\s*56\s*>|unsigned\s+long\s+long)\s+fp32_aligner\s*\([^)]*\)\s*\{',
        code
    )
    if not m:
        return code

    func_start = m.start()
    brace_pos  = m.end() - 1

    depth = 0
    i = brace_pos
    n = len(code)
    while i < n:
        if code[i] == '{':
            depth += 1
        elif code[i] == '}':
            depth -= 1
            if depth == 0:
                func_end = i + 1
                break
        i += 1
    else:
        return code

    canonical = r"""
ap_uint<56> fp32_aligner(ap_uint<8> e1, ap_uint<23> m1, ap_uint<8> e2, ap_uint<23> m2) {
  // Build 24-bit significands with hidden 1 for normal numbers
  ap_uint<24> sm1 = (e1 == 0) ? (ap_uint<24>)m1 : (ap_uint<24>)(((ap_uint<24>)1 << 23) | m1);
  ap_uint<24> sm2 = (e2 == 0) ? (ap_uint<24>)m2 : (ap_uint<24>)(((ap_uint<24>)1 << 23) | m2);

  // Align the smaller exponent
  ap_uint<8>  texp = (e1 >= e2) ? e1 : e2;
  ap_uint<8>  de   = (e1 >= e2) ? (ap_uint<8>)(e1 - e2) : (ap_uint<8>)(e2 - e1);
  ap_uint<24> am1  = (e1 >= e2) ? sm1 : (ap_uint<24>)(sm1 >> de);
  ap_uint<24> am2  = (e1 >= e2) ? (ap_uint<24>)(sm2 >> de) : sm2;

  // Pack: [55:32]=am1, [31:8]=am2, [7:0]=texp
  ap_uint<56> pack = ((ap_uint<56>)am1 << 32) | ((ap_uint<56>)am2 << 8) | (ap_uint<56>)texp;
  return pack;
}
""".strip("\n")

    return code[:func_start] + canonical + "\n" + code[func_end:]


def _canonicalise_fp32_raw_summer(code: str) -> str:
    """
    Replace fp32_raw_summer(...) with a clean version that:
      - performs add/sub on zero-extended 25-bit magnitudes,
      - chooses sign per IEEE magnitude compare,
      - returns {sign, sum25} as ap_uint<26>.
    """
    if "fp32_raw_summer(" not in code:
        return code

    m = re.search(
        r'\b(?:ap_uint<\s*26\s*>|unsigned\s+int)\s+fp32_raw_summer\s*\([^)]*\)\s*\{',
        code
    )
    if not m:
        return code

    func_start = m.start()
    brace_pos  = m.end() - 1

    depth = 0
    i = brace_pos
    n = len(code)
    while i < n:
        if code[i] == '{':
            depth += 1
        elif code[i] == '}':
            depth -= 1
            if depth == 0:
                func_end = i + 1
                break
        i += 1
    else:
        return code

    canonical = r"""
ap_uint<26> fp32_raw_summer(ap_uint<1> s1, ap_uint<24> aligned_m1,
                            ap_uint<1> s2, ap_uint<24> aligned_m2) {
  ap_uint<25> A = (ap_uint<25>)aligned_m1; // zero-extended
  ap_uint<25> B = (ap_uint<25>)aligned_m2; // zero-extended

  ap_uint<25> sum25;
  ap_uint<1>  out_sign;

  if (s1 == s2) {
    sum25   = A + B;
    out_sign = s1;
  } else {
    if (A == B) {
      sum25   = 0;
      out_sign = 0;       // +0 by convention
    } else if (A > B) {
      sum25   = A - B;
      out_sign = s1;
    } else {
      sum25   = B - A;
      out_sign = s2;
    }
  }

  return ((ap_uint<26>)out_sign << 25) | (ap_uint<26>)sum25;
}
""".strip("\n")

    return code[:func_start] + canonical + "\n" + code[func_end:]

def _canonicalise_fp32_normaliser(code: str) -> str:
    """
    Replace the entire fp32_normaliser(...) function with a clean, canonical version.
    Uses brace matching to avoid truncation.
    """
    if "fp32_normaliser(" not in code:
        return code

    # Find the function header (return type may be ap_uint<...> or unsigned int from smt2c)
    m = re.search(r'\b(?:ap_uint<\d+>|unsigned\s+int)\s+fp32_normaliser\s*\([^)]*\)\s*\{', code)
    if not m:
        return code

    func_start = m.start()
    brace_pos  = m.end() - 1  # position of the '{'

    # Match braces to find the end of this function
    depth = 0
    i = brace_pos
    n = len(code)
    while i < n:
        if code[i] == '{':
            depth += 1
        elif code[i] == '}':
            depth -= 1
            if depth == 0:
                func_end = i + 1
                break
        i += 1
    else:
        # unmatched braces; leave code unchanged
        return code

    canonical = r"""
ap_uint<32> fp32_normaliser(ap_uint<25> raw_sum_mantissa, ap_uint<1> raw_sign, ap_uint<8> target_exponent) {
  if (raw_sum_mantissa == 0) {
    return (ap_uint<32>)((ap_uint<1>)0, (ap_uint<8>)0, (ap_uint<23>)0);
  }
  ap_uint<8> exp = target_exponent;
  ap_uint<24> norm24;
  if (raw_sum_mantissa[24]) { norm24 = raw_sum_mantissa.range(24,1); exp += 1; }
  else if (raw_sum_mantissa[23]) { norm24 = raw_sum_mantissa.range(23,0); }
  else if (raw_sum_mantissa[22]) { norm24 = (ap_uint<24>)raw_sum_mantissa.range(22,0) << 1; exp -= 1; }
  else if (raw_sum_mantissa[21]) { norm24 = (ap_uint<24>)raw_sum_mantissa.range(21,0) << 2; exp -= 2; }
  else if (raw_sum_mantissa[20]) { norm24 = (ap_uint<24>)raw_sum_mantissa.range(20,0) << 3; exp -= 3; }
  else if (raw_sum_mantissa[19]) { norm24 = (ap_uint<24>)raw_sum_mantissa.range(19,0) << 4; exp -= 4; }
  else if (raw_sum_mantissa[18]) { norm24 = (ap_uint<24>)raw_sum_mantissa.range(18,0) << 5; exp -= 5; }
  else if (raw_sum_mantissa[17]) { norm24 = (ap_uint<24>)raw_sum_mantissa.range(17,0) << 6; exp -= 6; }
  else if (raw_sum_mantissa[16]) { norm24 = (ap_uint<24>)raw_sum_mantissa.range(16,0) << 7; exp -= 7; }
  else if (raw_sum_mantissa[15]) { norm24 = (ap_uint<24>)raw_sum_mantissa.range(15,0) << 8; exp -= 8; }
  else if (raw_sum_mantissa[14]) { norm24 = (ap_uint<24>)raw_sum_mantissa.range(14,0) << 9; exp -= 9; }
  else if (raw_sum_mantissa[13]) { norm24 = (ap_uint<24>)raw_sum_mantissa.range(13,0) << 10; exp -= 10; }
  else if (raw_sum_mantissa[12]) { norm24 = (ap_uint<24>)raw_sum_mantissa.range(12,0) << 11; exp -= 11; }
  else if (raw_sum_mantissa[11]) { norm24 = (ap_uint<24>)raw_sum_mantissa.range(11,0) << 12; exp -= 12; }
  else if (raw_sum_mantissa[10]) { norm24 = (ap_uint<24>)raw_sum_mantissa.range(10,0) << 13; exp -= 13; }
  else if (raw_sum_mantissa[9])  { norm24 = (ap_uint<24>)raw_sum_mantissa.range(9,0)  << 14; exp -= 14; }
  else if (raw_sum_mantissa[8])  { norm24 = (ap_uint<24>)raw_sum_mantissa.range(8,0)  << 15; exp -= 15; }
  else if (raw_sum_mantissa[7])  { norm24 = (ap_uint<24>)raw_sum_mantissa.range(7,0)  << 16; exp -= 16; }
  else if (raw_sum_mantissa[6])  { norm24 = (ap_uint<24>)raw_sum_mantissa.range(6,0)  << 17; exp -= 17; }
  else if (raw_sum_mantissa[5])  { norm24 = (ap_uint<24>)raw_sum_mantissa.range(5,0)  << 18; exp -= 18; }
  else if (raw_sum_mantissa[4])  { norm24 = (ap_uint<24>)raw_sum_mantissa.range(4,0)  << 19; exp -= 19; }
  else if (raw_sum_mantissa[3])  { norm24 = (ap_uint<24>)raw_sum_mantissa.range(3,0)  << 20; exp -= 20; }
  else if (raw_sum_mantissa[2])  { norm24 = (ap_uint<24>)raw_sum_mantissa.range(2,0)  << 21; exp -= 21; }
  else if (raw_sum_mantissa[1])  { norm24 = (ap_uint<24>)raw_sum_mantissa.range(1,0)  << 22; exp -= 22; }
  else /* raw_sum_mantissa[0] */  { norm24 = (ap_uint<24>)raw_sum_mantissa.range(0,0)  << 23; exp -= 23; }
  ap_uint<1> sign = raw_sign; // zero already handled
  return (ap_uint<32>)((ap_uint<1>)sign, (ap_uint<8>)exp, (ap_uint<23>)norm24.range(22,0));
}
""".strip("\n")

    return code[:func_start] + canonical + "\n" + code[func_end:]

def _canonicalise_fp32_sum(code: str) -> str:
    """
    Replace the whole fp32_sum(...) body with a simple, HLS-safe version that
    uses temporaries for the aligned pack and slices. Works whether the return
    type was 'unsigned int' (from smt2c) or 'ap_uint<32>'.
    """
    if "fp32_sum(" not in code:
        return code

    # find the start of the function body
    m = re.search(r'\b(?:ap_uint<\d+>|unsigned\s+int)\s+fp32_sum\s*\([^)]*\)\s*\{', code)
    if not m:
        return code

    func_start = m.start()
    brace_pos  = m.end() - 1  # at '{'

    # match balanced braces to find the end of this function
    depth = 0
    i = brace_pos
    n = len(code)
    while i < n:
        if code[i] == '{':
            depth += 1
        elif code[i] == '}':
            depth -= 1
            if depth == 0:
                func_end = i + 1
                break
        i += 1
    else:
        return code  # unmatched braces; bail

    canonical = r"""
ap_uint<32> fp32_sum(ap_uint<1> s1, ap_uint<8> e1, ap_uint<23> m1,
                     ap_uint<1> s2, ap_uint<8> e2, ap_uint<23> m2) {
  // 56-bit pack: [55:32]=aligned m1, [31:8]=aligned m2, [7:0]=target exponent
  ap_uint<56> pack = fp32_aligner(e1, m1, e2, m2);
  ap_uint<24> am1  = (ap_uint<24>) pack.range(55, 32);
  ap_uint<24> am2  = (ap_uint<24>) pack.range(31,  8);
  ap_uint<8>  exp  = (ap_uint<8>)  pack.range( 7,  0);

  ap_uint<26> raw  = fp32_raw_summer(s1, am1, s2, am2);
  ap_uint<25> raw_m = (ap_uint<25>) raw.range(24, 0);
  ap_uint<1>  raw_s = (ap_uint<1>)  raw.range(25, 25);

  return fp32_normaliser(raw_m, raw_s, exp);
}
""".strip("\n")

    return code[:func_start] + canonical + "\n" + code[func_end:]
