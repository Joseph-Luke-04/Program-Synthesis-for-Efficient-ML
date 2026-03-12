ap_uint<1> mult_renorm_flag(ap_uint<4> m1, ap_uint<4> m2) {
  unsigned char _let_1 = (unsigned char)(signed char)(ap_int<4>)m1 * (unsigned char)(signed char)(ap_int<4>)m2;
  return (signed char)(_let_1 + (_let_1 & _let_1 + _let_1)) <= (signed char)0 ? (ap_uint<1>)  1 : (ap_uint<1>)  0;
}

ap_uint<4> mult_mxint_exp(ap_uint<4> e1, ap_uint<4> e2, ap_uint<1> renorm_flag) {
  ap_uint<4> _let_1 = e1 + e1;
  __CPROVER_bool _let_2 = renorm_flag == 1;
  ap_uint<4> _let_3 = _let_2 ? (ap_uint<4>)  e2 : (ap_uint<4>)  0;
  ap_uint<4> _let_4 = e2 + e2;
  ap_uint<4> _let_5 = e1 + e2;
  ap_uint<4> _let_6 = e1 - e2;
  ap_uint<4> __smt2c_result;
  if((ap_int<4>)0 >= (ap_int<4>)(e1 & _let_3)) {
    __smt2c_result = (ap_int<4>)e2 >= (ap_int<4>)(_let_2 ? (ap_uint<4>)  e1 : (ap_uint<4>)  e2) ? (ap_uint<4>)  ((ap_int<4>)0 < (ap_int<4>)(e2 & _let_6) ? (ap_uint<4>)  ((ap_int<4>)e2 >= (ap_int<4>)(e1 | e2) ? (ap_uint<4>)  ((ap_int<4>)_let_1 >= (ap_int<4>)0 ? (ap_uint<4>)  ((ap_int<4>)0 < (ap_int<4>)(e1 & _let_6) ? (ap_uint<4>)  _let_5 : (ap_uint<4>)  ((ap_int<4>)e1 < (ap_int<4>)(_let_2 ? (ap_uint<4>)  0 : (ap_uint<4>)  e2) ? (ap_uint<4>)  _let_5 : (ap_uint<4>)  ((ap_int<4>)e2 >= (ap_int<4>)e1 ? (ap_uint<4>)  e2 & _let_4 : (ap_uint<4>)  _let_5))) : (ap_uint<4>)  _let_5) : (ap_uint<4>)  _let_5) : (ap_uint<4>)  _let_5) : (ap_uint<4>)  ((ap_int<4>)e2 >= (ap_int<4>)_let_6 ? (ap_uint<4>)  ((ap_int<4>)_let_6 >= (ap_int<4>)e2 ? (ap_uint<4>)  _let_5 : (ap_uint<4>)  _let_4) : (ap_uint<4>)  e1);
  }
  else if((ap_int<4>)e1 >= (ap_int<4>)_let_3) {
    __smt2c_result = (ap_int<4>)(e2 - e1) < (ap_int<4>)0 ? (ap_uint<4>)  e1 : (ap_uint<4>)  e1 + (e1 & _let_1);
  }
  else {
    __smt2c_result = _let_1;
  }
  return __smt2c_result;
}

ap_uint<4> mult_mxint_mant(ap_uint<4> m1, ap_uint<4> m2) {
  unsigned char _let_1 = (unsigned char)(signed char)(ap_int<4>)m1 * (unsigned char)(signed char)(ap_int<4>)m2;
  unsigned char __smt2c_src_0 = _let_1 + _let_1;
  ap_uint<4> __smt2c_ext_1 = ((ap_uint<8>)__smt2c_src_0).range(7, 4);
  unsigned char __smt2c_src_2 = (unsigned char)(signed char)(ap_int<4>)__smt2c_ext_1;
  ap_uint<4> __smt2c_ext_3 = ((ap_uint<8>)__smt2c_src_2).range(3, 0);
  return __smt2c_ext_3;
}

unsigned char mult_mxint_full_product(ap_uint<4> m1, ap_uint<4> e1, ap_uint<4> m2, ap_uint<4> e2, ap_uint<1> renorm_flag) {
  return (unsigned char)mult_mxint_mant(m1, m2) << 4 | (unsigned char)mult_mxint_exp(e1, e2, mult_renorm_flag(m1, m2));
}
