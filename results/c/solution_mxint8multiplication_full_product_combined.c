unsigned char mult_mxint_full_product(ap_uint<4> m1, ap_uint<4> e1, ap_uint<4> m2, ap_uint<4> e2, ap_uint<1> renorm_flag) {
  return ((unsigned char)((signed char)((unsigned char)(signed char)(ap_int<4>)m1 * (unsigned char)(signed char)(ap_int<4>)m2) >> (signed char)2)[0 + 3, 0],renorm_flag == 1 ? (ap_uint<5>)  ((ap_uint<5>)(ap_int<5>)(ap_int<4>)e1 + (ap_uint<5>)(ap_int<5>)(ap_int<4>)e2) - (ap_uint<5>)(ap_int<5>)(ap_int<4>)1 : (ap_uint<5>)  (ap_uint<5>)(ap_int<5>)(ap_int<4>)e1 + (ap_uint<5>)(ap_int<5>)(ap_int<4>)e2[0 + 3, 0]);
}
