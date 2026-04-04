#include <ap_int.h>

ap_uint<8> mult_mxint_full_product(ap_uint<4> m1, ap_uint<4> e1, ap_uint<4> m2, ap_uint<4> e2, ap_uint<1> renorm_flag) {
  ap_uint<8> _let_1 = (ap_uint<8>)(ap_int<8>)(ap_int<4>)m1 * (ap_uint<8>)(ap_int<8>)(ap_int<4>)m2;
  bool _let_2 = (ap_int<8>)_let_1 < (ap_int<8>)0;
  ap_uint<5> _let_3 = (ap_uint<5>)(ap_int<5>)(ap_int<4>)e1 + (ap_uint<5>)(ap_int<5>)(ap_int<4>)e2;
  ap_uint<5> __smt2c_src_0 = ((ap_int<8>)(_let_2 ? (ap_uint<8>)  -_let_1 : (ap_uint<8>)  _let_1) >= (ap_int<8>)31 ? (ap_uint<1>)  1 : (ap_uint<1>)  0) == 1 ? (ap_uint<5>)  _let_3 : (ap_uint<5>)((ap_uint<5>)  _let_3 - (ap_uint<5>)(ap_int<5>)(ap_int<4>)1);
  ap_uint<4> __smt2c_ext_1 = ((ap_uint<5>)__smt2c_src_0).range(3, 0);
  ap_uint<8> __smt2c_src_2 = (ap_uint<8>)((ap_int<8>)(_let_1 + (_let_2 ? (ap_uint<8>)  -4 : (ap_uint<8>)  0)) >> (ap_int<8>)2);
  ap_uint<4> __smt2c_ext_3 = ((ap_uint<8>)__smt2c_src_2).range(3, 0);
  ap_uint<4> __smt2c_ext_4 = ((ap_uint<8>)_let_1).range(3, 0);
  return (ap_uint<8>)__smt2c_ext_1 << 4 | (ap_uint<8>)(true ? (ap_uint<4>)  ((ap_int<8>)_let_1 > (ap_int<8>)7 ? (ap_uint<4>)  7 : (ap_uint<4>)  ((ap_int<8>)(ap_uint<8>)((ap_int<8>)(_let_1 + (_let_2 ? (ap_uint<8>)  -3 : (ap_uint<8>)  0)) >> (ap_int<8>)2) < (ap_int<8>)248 ? (ap_uint<4>)  8 : (ap_uint<4>)  __smt2c_ext_3)) : (ap_uint<4>)  __smt2c_ext_4);
}
