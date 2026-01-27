ap_uint<1> mult_renorm_flag(ap_uint<4> m1, ap_uint<4> m2) {
  return (signed char)((signed char)((unsigned char)(signed char)(ap_int<4>)m1 * (unsigned char)(signed char)(ap_int<4>)m2) < (signed char)0 ? (unsigned char)  -((unsigned char)(signed char)(ap_int<4>)m1 * (unsigned char)(signed char)(ap_int<4>)m2) : (unsigned char)  (unsigned char)(signed char)(ap_int<4>)m1 * (unsigned char)(signed char)(ap_int<4>)m2) <= (signed char)31 ? (ap_uint<1>)  1 : (ap_uint<1>)  0;
}

ap_uint<4> mult_mxint_exp(ap_uint<4> e1, ap_uint<4> e2, ap_uint<1> renorm_flag) {
  return renorm_flag == 1 ? (ap_uint<4>)  (e1 + e2) - 1 : (ap_uint<4>)  e1 + e2;
}

ap_uint<4> mult_mxint_mant(ap_uint<4> m1, ap_uint<4> m2) {
  return (signed char)((signed char)((unsigned char)(signed char)(ap_int<4>)m1 * (unsigned char)(signed char)(ap_int<4>)m2) < (signed char)0 ? (unsigned char)  -((unsigned char)(signed char)(ap_int<4>)m1 * (unsigned char)(signed char)(ap_int<4>)m2) : (unsigned char)  (unsigned char)(signed char)(ap_int<4>)m1 * (unsigned char)(signed char)(ap_int<4>)m2) <= (signed char)32 ? (unsigned char)  (unsigned char)((signed char)((unsigned char)(signed char)(ap_int<4>)m1 * (unsigned char)(signed char)(ap_int<4>)m2 << 1) >> (signed char)3) : (unsigned char)  (unsigned char)((signed char)((unsigned char)(signed char)(ap_int<4>)m1 * (unsigned char)(signed char)(ap_int<4>)m2) >> (signed char)3)[0 + 3, 0];
}

unsigned char mult_mxint_full_product(ap_uint<4> m1, ap_uint<4> e1, ap_uint<4> m2, ap_uint<4> e2, ap_uint<1> renorm_flag) {
  return (mult_mxint_mant(m1, m2),mult_mxint_exp(e1, e2, mult_renorm_flag(m1, m2)));
}
