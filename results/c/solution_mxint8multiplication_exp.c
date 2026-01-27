ap_uint<1> mult_renorm_flag(ap_uint<4> m1, ap_uint<4> m2) {
  return (signed char)((signed char)((unsigned char)(signed char)(ap_int<4>)m1 * (unsigned char)(signed char)(ap_int<4>)m2) < (signed char)0 ? (unsigned char)  -((unsigned char)(signed char)(ap_int<4>)m1 * (unsigned char)(signed char)(ap_int<4>)m2) : (unsigned char)  (unsigned char)(signed char)(ap_int<4>)m1 * (unsigned char)(signed char)(ap_int<4>)m2) <= (signed char)31 ? (ap_uint<1>)  1 : (ap_uint<1>)  0;
}

ap_uint<4> mult_mxint_exp(ap_uint<4> e1, ap_uint<4> e2, ap_uint<1> renorm_flag) {
  return renorm_flag == 1 ? (ap_uint<4>)  (e1 + e2) - 1 : (ap_uint<4>)  e1 + e2;
}
