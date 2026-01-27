#include <ap_int.h>

ap_uint<4> select_exponent(ap_uint<4> e1, ap_uint<4> e2) {
  return (ap_int<4>) (e1 >= (ap_int<4>)e2 ? ap_uint<4>(((ap_uint<4>)  e1)) : ap_uint<4>(((ap_uint<4>)  e2)));
}
ap_uint<8> align_mantissas(ap_uint<4> m1, ap_uint<4> e1, ap_uint<4> m2, ap_uint<4> e2) {
  ap_int<4> s1 = (ap_int<4>)m1;
  ap_int<4> s2 = (ap_int<4>)m2;
  ap_int<4> se1 = (ap_int<4>)e1;
  ap_int<4> se2 = (ap_int<4>)e2;
  bool cond = (se1 >= se2);
  ap_uint<4> d = cond ? (ap_uint<4>)(e1 - e2) : (ap_uint<4>)(e2 - e1);
  ap_int<4> a1, a2;
  if (cond) {
    a1 = s1;
    if (d == 0) {
      a2 = s2;
    } else if (d >= 4) {
      a2 = (ap_int<4>)0;
    } else {
      ap_uint<3> ush = (ap_uint<3>)d;
      a2 = (ap_int<4>)(s2 >> ush);
    }
  } else {
    a2 = s2;
    if (d == 0) {
      a1 = s1;
    } else if (d >= 4) {
      a1 = (ap_int<4>)0;
    } else {
      ap_uint<3> ush = (ap_uint<3>)d;
      a1 = (ap_int<4>)(s1 >> ush);
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
ap_uint<1> detect_overflow(ap_uint<5> raw_sum) {
  ap_int<5> s5 = (ap_int<5>)raw_sum;
  return (s5 > 7 || s5 < -8) ? (ap_uint<1>)1 : (ap_uint<1>)0;
}
ap_uint<8> normalise_addition(ap_uint<5> raw_sum, ap_uint<4> target_exp) {
  ap_int<5> s5 = (ap_int<5>)raw_sum;
  ap_uint<5> abs5 = (s5 < 0) ? (ap_uint<5>)(-s5) : (ap_uint<5>)s5;
  ap_int<5> shifted = s5;
  ap_int<5> exp5 = (ap_int<5>)(ap_int<4>)target_exp;
  if (s5 == 0) {
    shifted = 0;
    exp5 = 0;
  } else {
    ap_uint<3> msb = abs5[4] ? 4 : abs5[3] ? 3 : abs5[2] ? 2 : abs5[1] ? 1 : 0;
    if (msb > 2) {
      ap_uint<2> rsh = (ap_uint<2>)(msb - 2); // 1 or 2
      ap_int<5> bias = (rsh == 1) ? (ap_int<5>)1 : (ap_int<5>)2;
      ap_int<5> adj = (s5 < 0) ? (ap_int<5>)(-bias) : bias;
      shifted = (ap_int<5>)((s5 + adj) >> rsh);
      exp5 = exp5 + (ap_int<5>)rsh;
    } else if (msb < 2) {
      ap_uint<2> lsh = (ap_uint<2>)(2 - msb);
      ap_uint<5> u = (ap_uint<5>)s5;
      shifted = (ap_int<5>)(u << lsh);
      exp5 = exp5 - (ap_int<5>)lsh;
    }
  }
  if (exp5 > 7) exp5 = 7;
  if (exp5 < -8) exp5 = -8;
  ap_int<5> sat = shifted;
  if (sat > 7) sat = 7;
  if (sat < -8) sat = -8;
  ap_uint<4> mant_u = ((ap_uint<5>)sat).range(3, 0);
  ap_uint<4> exp_u = (ap_uint<4>)exp5;
  return (ap_uint<8>)((((ap_uint<8>)mant_u) << 4) | exp_u);
}
ap_uint<8> add_full_sum(ap_uint<4> m1, ap_uint<4> e1, ap_uint<4> m2, ap_uint<4> e2) {
  return normalise_addition((ap_uint<9>((add_raw(m1, e1, m2, e2)))).range(8, 4), (ap_uint<4>((add_raw(m1, e1, m2, e2)))).range(3, 0));
}
