#include <ap_int.h>

ap_uint<4> select_exponent(ap_uint<4> e1, ap_uint<4> e2) {
  return (ap_int<4>)e1 >= (ap_int<4>)e2 ? ap_uint<4>(((ap_uint<4>)  e1)) : ap_uint<4>(((ap_uint<4>)  e2));
}
ap_uint<8> align_mantissas(ap_uint<4> m1, ap_uint<4> e1, ap_uint<4> m2, ap_uint<4> e2) {
  ap_int<4> s1 = (ap_int<4>)m1;
  ap_int<4> s2 = (ap_int<4>)m2;
  ap_int<4> de = (ap_int<4>)e1 - (ap_int<4>)e2;
  ap_int<4> a1, a2;
  if (de >= 0) {
    a1 = s1;
    if (de == 0) {
      a2 = s2;
    } else {
      ap_uint<4> d = (ap_uint<4>)de;          // d >= 1 here
      ap_int<16> t  = (ap_int<16>)s2;         // widen for safe rounding
      ap_int<16> mag = ((ap_int<16>)1) << (d - 1);
      ap_int<16> sgn = (t >= 0) ? (ap_int<16>)1 : (ap_int<16>)-1;
      t = (t + sgn * mag) >> d;               // round-to-nearest, sign-aware
      if (t > 7) t = 7; if (t < -8) t = -8;
      a2 = (ap_int<4>)t;
    }
  } else {
    ap_uint<4> d = (ap_uint<4>)(-de);
    a2 = s2;
    if (d == 0) {
      a1 = s1;
    } else {
      ap_int<16> t  = (ap_int<16>)s1;         // widen for safe rounding
      ap_int<16> mag = ((ap_int<16>)1) << (d - 1);
      ap_int<16> sgn = (t >= 0) ? (ap_int<16>)1 : (ap_int<16>)-1;
      t = (t + sgn * mag) >> d;               // round-to-nearest, sign-aware
      if (t > 7) t = 7; if (t < -8) t = -8;
      a1 = (ap_int<4>)t;
    }
  }
  return (ap_uint<8>)((((ap_uint<8>)(ap_uint<4>)a1) << 4) | (ap_uint<4>)a2);
}
ap_uint<9> add_raw(ap_uint<4> m1, ap_uint<4> e1, ap_uint<4> m2, ap_uint<4> e2) {
  ap_uint<8> aligned = align_mantissas(m1, e1, m2, e2);
  ap_int<4> a = (ap_int<4>)((ap_uint<4>)aligned.range(7, 4));
  ap_int<4> b = (ap_int<4>)((ap_uint<4>)aligned.range(3, 0));
  ap_uint<5> sum = (ap_uint<5>)((ap_int<5>)a + (ap_int<5>)b);
  ap_uint<4> texp = select_exponent(e1, e2);
  return (ap_uint<9>)((((ap_uint<9>)sum) << 4) | texp);
}
ap_uint<8> normalise_addition(ap_uint<5> raw_sum, ap_uint<4> target_exp) {
  ap_int<5> s5 = (ap_int<5>)raw_sum;
  ap_uint<4> exp = target_exp;
  ap_int<4> mant;
  if (s5 > 7 || s5 < -8) {
    ap_int<6> t = (ap_int<6>)s5;
    ap_int<6> sgn = (t >= 0) ? (ap_int<6>)1 : (ap_int<6>)-1; // same type both arms
    t = t + sgn;                                            // +0.5 ulp before >>1
    t >>= 1;
    if (t > 7) t = 7; if (t < -8) t = -8;
    mant = (ap_int<4>)t;
    exp  = exp + 1;
  } else {
    mant = (ap_int<4>)s5;
  }
  return (ap_uint<8>)((((ap_uint<8>)((ap_uint<4>)mant)) << 4) | exp);
}
ap_uint<8> add_full_sum(ap_uint<4> m1, ap_uint<4> e1, ap_uint<4> m2, ap_uint<4> e2) {
  ap_uint<9> raw = add_raw(m1, e1, m2, e2);
  ap_uint<5> raw_m = (ap_uint<5>) raw.range(8, 4);
  ap_uint<4> texp  = (ap_uint<4>) raw.range(3, 0);
  return normalise_addition(raw_m, texp);
}
