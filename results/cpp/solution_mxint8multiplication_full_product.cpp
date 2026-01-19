#include <ap_int.h>
ap_uint<1> mult_renorm_flag(ap_uint<4> m1, ap_uint<4> m2) {
  ap_int<4> s1 = (ap_int<4>)m1;
  ap_int<4> s2 = (ap_int<4>)m2;
  ap_int<8> prod = (ap_int<8>)(s1 * s2);
  ap_int<8> abs_p = (prod < 0) ? (ap_int<8>)-prod : prod;
  return (abs_p <= (ap_int<8>)32) ? (ap_uint<1>)1 : (ap_uint<1>)0;
}
ap_uint<4> mult_mxint_exp(ap_uint<4> e1, ap_uint<4> e2, ap_uint<1> renorm_flag) {
  return renorm_flag == 1 ? ap_uint<4>((ap_uint<4>(((e1 + e2) - 1)))) : ap_uint<4>((ap_uint<4>((e1 + e2))));
}
ap_uint<4> mult_mxint_mant(ap_uint<4> m1, ap_uint<4> m2) {
  ap_int<4> s1 = (ap_int<4>)m1;
  ap_int<4> s2 = (ap_int<4>)m2;
  ap_int<8> prod = (ap_int<8>)(s1 * s2);
  ap_int<8> abs_p = (prod < 0) ? (ap_int<8>)-prod : prod;
  ap_int<8> inter = (abs_p <= (ap_int<8>)32)
                  ? (ap_int<8>)((prod << 1) >> 3)
                  : (ap_int<8>)(prod >> 3);
  return (ap_uint<4>)inter;
}
ap_uint<8> mult_mxint_full_product(ap_uint<4> m1, ap_uint<4> e1, ap_uint<4> m2, ap_uint<4> e2, ap_uint<1> renorm_flag) {
  return ap_uint<8>(((ap_uint<8>)((ap_uint<8>)((mult_mxint_mant(m1, m2))) << 4)) | (ap_uint<4>)((mult_mxint_exp(e1, e2, mult_renorm_flag(m1, m2)))));
}
