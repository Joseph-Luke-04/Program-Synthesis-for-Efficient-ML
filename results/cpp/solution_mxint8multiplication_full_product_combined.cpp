#include <ap_int.h>

ap_uint<8> mult_mxint_full_product(ap_uint<4> m1, ap_uint<4> e1, ap_uint<4> m2, ap_uint<4> e2, ap_uint<1> renorm_flag) {
  ap_int<8> prod = (ap_int<8>)((ap_int<4>)m1) * (ap_int<8>)((ap_int<4>)m2);
  ap_int<8> mant_shift = (ap_int<8>)(prod >> 2);
  ap_uint<4> mant = (ap_uint<4>)mant_shift.range(3, 0);

  ap_int<5> esum = (ap_int<5>)((ap_int<4>)e1) + (ap_int<5>)((ap_int<4>)e2);
  ap_int<5> eadj = (renorm_flag == (ap_uint<1>)1) ? (ap_int<5>)(esum - (ap_int<5>)1) : esum;
  ap_uint<4> exp = (ap_uint<4>)eadj.range(3, 0);

  return (ap_uint<8>)((((ap_uint<8>)mant) << 4) | (ap_uint<8>)exp);
}
