#include <ap_int.h>

ap_uint<1> mult_renorm_flag(ap_uint<4> m1, ap_uint<4> m2) {
  ap_uint<8> _let_1 = (ap_uint<8>)(ap_int<8>)(ap_int<4>)m1 * (ap_uint<8>)(ap_int<8>)(ap_int<4>)m2;
  return (ap_int<8>)0 <= (ap_int<8>)(_let_1 + ((ap_int<8>)_let_1 < (ap_int<8>)0 ? (ap_uint<8>)  -_let_1 : ap_uint<8>((_let_1 + _let_1)))) ? (ap_uint<1>)  1 : (ap_uint<1>)  0;
}

ap_uint<4> mult_mxint_exp(ap_uint<4> e1, ap_uint<4> e2, ap_uint<1> renorm_flag) {
  bool _let_1 = renorm_flag == 1;
  ap_uint<4> _let_2 = e1 + e2;
  ap_uint<4> _let_3 = e1 | e2;
  ap_uint<4> __smt2c_result;
  if((ap_int<4>)0 >= (ap_int<4>)(e2 - (e1 - e2))) {
    __smt2c_result = (ap_int<4>)0 < (ap_int<4>)_let_3 ? ap_uint<4>((e1 + (_let_1 ? (ap_uint<4>)  0 : (ap_uint<4>)  e2))) : (ap_uint<4>)  ((ap_int<4>)0 < (ap_int<4>)(e1 & e2) ? ap_uint<4>((e1 - (e1 & 0 - e2))) : (ap_uint<4>)  _let_2);
  }
  else if((ap_int<4>)0 < (ap_int<4>)(e1 + _let_3)) {
    __smt2c_result = (ap_int<4>)0 >= (ap_int<4>)(e1 + e2 + e2) ? (ap_uint<4>)  ((ap_int<4>)e1 < (ap_int<4>)e2 ? (ap_uint<4>)  _let_2 : ap_uint<4>((e1 + (e1 & e1 + e1)))) : (ap_uint<4>)  _let_2;
  }
  else {
    __smt2c_result = e1 + (_let_1 ? (ap_uint<4>)  e1 : (ap_uint<4>)  e2);
  }
  return __smt2c_result;
}

ap_uint<4> mult_mxint_mant(ap_uint<4> m1, ap_uint<4> m2) {
  ap_uint<8> __smt2c_src_0 = (ap_uint<8>)((ap_int<8>)((ap_uint<8>)(ap_int<8>)(ap_int<4>)m1 * (ap_uint<8>)(ap_int<8>)(ap_int<4>)m2) >> (ap_int<8>)2);
  ap_uint<4> __smt2c_ext_1 = ((ap_uint<8>)__smt2c_src_0).range(3, 0);
  return __smt2c_ext_1;
}

ap_uint<8> mult_mxint_full_product(ap_uint<4> m1, ap_uint<4> e1, ap_uint<4> m2, ap_uint<4> e2, ap_uint<1> renorm_flag) {
  return (ap_uint<8>)mult_mxint_mant(m1, m2) << 4 | (ap_uint<8>)mult_mxint_exp(e1, e2, mult_renorm_flag(m1, m2));
}
