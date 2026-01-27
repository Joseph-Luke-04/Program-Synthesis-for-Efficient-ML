#include <ap_int.h>
ap_uint<1> mult_renorm_flag(ap_uint<4> m1, ap_uint<4> m2) {
  ap_int<4> s1 = (ap_int<4>)m1;
  ap_int<4> s2 = (ap_int<4>)m2;
  ap_int<8> prod = (ap_int<8>)(s1 * s2);
  ap_int<8> abs_p = (prod < 0) ? (ap_int<8>)-prod : prod;
  return (abs_p <= (ap_int<8>)32) ? (ap_uint<1>)1 : (ap_uint<1>)0;
}
ap_uint<4> mult_mxint_exp(ap_uint<4> e1, ap_uint<4> e2, ap_uint<1> renorm_flag) {
return renorm_flag == 1 ? ap_uint<4>(((e1 + e2) - 1)) : ap_uint<4>((e1 + e2));
}
