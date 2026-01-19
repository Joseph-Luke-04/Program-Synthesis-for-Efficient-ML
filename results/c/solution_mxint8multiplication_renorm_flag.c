ap_uint<1> mult_renorm_flag(ap_uint<4> m1, ap_uint<4> m2) {
  return (signed char)((signed char)((unsigned char)(signed char)(ap_int<4>)m1 * (unsigned char)(signed char)(ap_int<4>)m2) < (signed char)0 ? (unsigned char)  -((unsigned char)(signed char)(ap_int<4>)m1 * (unsigned char)(signed char)(ap_int<4>)m2) : (unsigned char)  (unsigned char)(signed char)(ap_int<4>)m1 * (unsigned char)(signed char)(ap_int<4>)m2) <= (signed char)32 ? (ap_uint<1>)  1 : (ap_uint<1>)  0;
}
