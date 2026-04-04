#include <ap_int.h>

ap_uint<1> mult_renorm_flag(ap_uint<4> m1, ap_uint<4> m2) {
  ap_uint<8> _let_1 = (ap_uint<8>)(ap_int<8>)(ap_int<4>)m1 * (ap_uint<8>)(ap_int<8>)(ap_int<4>)m2;
  return (ap_int<8>)((ap_int<8>)_let_1 < (ap_int<8>)0 ? (ap_uint<8>)  -_let_1 : (ap_uint<8>)  _let_1) <= (ap_int<8>)32 ? (ap_uint<1>)  1 : (ap_uint<1>)  0;
}

ap_uint<4> mult_mxint_exp(ap_uint<4> e1, ap_uint<4> e2, ap_uint<1> renorm_flag) {
  bool _let_1 = renorm_flag == 1;
  ap_uint<4> _let_2 = e2 + (_let_1 ? (ap_uint<4>)  e2 : (ap_uint<4>)  e1);
  ap_uint<4> _let_3 = _let_1 ? (ap_uint<4>)  e1 : (ap_uint<4>)  e2;
  ap_uint<4> _let_4 = e1 + _let_3;
  ap_uint<4> _let_5 = e1 + e1;
  return (ap_int<4>)e2 >= (ap_int<4>)_let_3 ? (ap_uint<4>)  ((ap_int<4>)e1 >= (ap_int<4>)0 ? (ap_uint<4>)  ((ap_int<4>)_let_5 >= (ap_int<4>)0 ? (ap_uint<4>)  ((ap_int<4>)0 < (ap_int<4>)_let_2 ? (ap_uint<4>)  ((ap_int<4>)0 < (ap_int<4>)(e1 + e1 + e2) ? (ap_uint<4>)  _let_4 : (ap_uint<4>)  ((ap_int<4>)(_let_1 ? (ap_uint<4>)  0 : (ap_uint<4>)  e2) < (ap_int<4>)e1 ? ap_uint<4>((e1 + (e1 & _let_5))) : (ap_uint<4>)  _let_4)) : (ap_uint<4>)  _let_4) : (ap_uint<4>)  _let_4) : (ap_uint<4>)  _let_4) : (ap_uint<4>)  _let_2;
}

ap_uint<4> mult_mxint_mant(ap_uint<4> m1, ap_uint<4> m2) {
  ap_uint<8> _let_1 = (ap_uint<8>)(ap_int<8>)(ap_int<4>)m1 * (ap_uint<8>)(ap_int<8>)(ap_int<4>)m2;
  ap_uint<8> __smt2c_src_0 = (ap_uint<8>)((ap_int<8>)_let_1 >> (ap_int<8>)((ap_int<8>)((ap_int<8>)_let_1 < (ap_int<8>)0 ? (ap_uint<8>)  -_let_1 : (ap_uint<8>)  _let_1) >= (ap_int<8>)32 ? (ap_uint<8>)  3 : (ap_uint<8>)  2));
  ap_uint<4> __smt2c_ext_1 = ((ap_uint<8>)__smt2c_src_0).range(3, 0);
  return __smt2c_ext_1;
}

ap_uint<8> mult_mxint_full_product(ap_uint<4> m1, ap_uint<4> e1, ap_uint<4> m2, ap_uint<4> e2, ap_uint<1> renorm_flag) {
  return (ap_uint<8>)mult_mxint_exp(e1, e2, mult_renorm_flag(m1, m2)) << 4 | (ap_uint<8>)mult_mxint_mant(m1, m2);
}
