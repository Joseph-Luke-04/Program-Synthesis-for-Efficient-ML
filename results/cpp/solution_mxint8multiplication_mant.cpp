#include <ap_int.h>
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
