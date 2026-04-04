unsigned char mult_mxint_full_product(ap_uint<4> m1, ap_uint<4> e1, ap_uint<4> m2, ap_uint<4> e2, ap_uint<1> renorm_flag) {
  unsigned char _let_1 = (unsigned char)(signed char)(ap_int<4>)m1 * (unsigned char)(signed char)(ap_int<4>)m2;
  ap_uint<4> __smt2c_ext_0 = ((ap_uint<8>)_let_1).range(3, 0);
  ap_uint<4> _let_2 = __smt2c_ext_0;
  ap_uint<5> __smt2c_src_1 = (ap_uint<5>)(ap_int<5>)(ap_int<4>)e1 + (ap_uint<5>)(ap_int<5>)(ap_int<4>)e2;
  ap_uint<4> __smt2c_ext_2 = ((ap_uint<5>)__smt2c_src_1).range(3, 0);
  return (unsigned char)__smt2c_ext_2 << 4 | (unsigned char)(true ? (ap_uint<4>)  ((signed char)_let_1 > (signed char)7 ? (ap_uint<4>)  7 : (ap_uint<4>)  ((signed char)_let_1 < (signed char)248 ? (ap_uint<4>)  8 : (ap_uint<4>)  _let_2)) : (ap_uint<4>)  _let_2);
}
