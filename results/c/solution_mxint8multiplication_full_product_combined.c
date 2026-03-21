unsigned char mult_mxint_full_product(ap_uint<4> m1, ap_uint<4> e1, ap_uint<4> m2, ap_uint<4> e2, ap_uint<1> renorm_flag) {
  ap_uint<5> _let_1 = (ap_uint<5>)(ap_int<5>)(ap_int<4>)e1 + (ap_uint<5>)(ap_int<5>)(ap_int<4>)e2;
  __CPROVER_bool _let_2 = 0 == 1;
  unsigned char __smt2c_src_0 = (unsigned char)((signed char)((unsigned char)(signed char)(ap_int<4>)m1 * (unsigned char)(signed char)(ap_int<4>)m2) >> (signed char)(_let_2 ? (unsigned char)  3 : (unsigned char)  2));
  ap_uint<4> __smt2c_ext_1 = ((ap_uint<8>)__smt2c_src_0).range(3, 0);
  ap_uint<5> __smt2c_src_2 = _let_2 ? (ap_uint<5>)  _let_1 : (ap_uint<5>)  _let_1 - (ap_uint<5>)(ap_int<5>)(ap_int<4>)1;
  ap_uint<4> __smt2c_ext_3 = ((ap_uint<5>)__smt2c_src_2).range(3, 0);
  return (unsigned char)__smt2c_ext_1 << 4 | (unsigned char)__smt2c_ext_3;
}
