#include <ap_int.h>

ap_uint<4> select_exponent(ap_uint<4> e1, ap_uint<4> e2) {
  return (ap_int<4>)e1 >= (ap_int<4>)e2 ? (ap_uint<4>)  e1 : (ap_uint<4>)  e2;
}

ap_uint<8> align_mantissas(ap_uint<4> m1, ap_uint<4> e1, ap_uint<4> m2, ap_uint<4> e2) {
  bool _let_1 = (ap_int<4>)e1 >= (ap_int<4>)e2;
  ap_uint<4> _let_2 = _let_1 ? (ap_uint<4>)  m1 : (ap_uint<4>)  m2;
  ap_uint<5> _let_3 = (ap_uint<5>)(ap_int<5>)(ap_int<4>)((ap_int<4>)e1 > (ap_int<4>)e2 ? (ap_uint<4>)  e1 : (ap_uint<4>)  e2) - (ap_uint<5>)(ap_int<5>)(ap_int<4>)(_let_1 ? (ap_uint<4>)  e2 : (ap_uint<4>)  e1);
  ap_uint<4> __smt2c_ext_0 = ((ap_uint<5>)_let_3).range(3, 0);
  ap_uint<4> _let_4 = __smt2c_ext_0;
  ap_uint<4> _let_5 = _let_1 ? (ap_uint<4>)  m2 : (ap_uint<4>)  m1;
  ap_uint<5> _let_6 = (ap_uint<5>)(ap_int<5>)(ap_int<4>)_let_5;
  ap_uint<5> __smt2c_src_1 = (ap_uint<5>)((ap_int<5>)_let_6 >> (ap_int<5>)_let_3);
  ap_uint<4> __smt2c_ext_2 = ((ap_uint<5>)__smt2c_src_1).range(3, 0);
  ap_uint<5> __smt2c_src_3 = (ap_uint<5>)((ap_int<5>)(_let_6 + (ap_uint<5>)(ap_int<5>)(ap_int<4>)((ap_int<4>)_let_5 < (ap_int<4>)0 ? (ap_uint<4>)  -(_let_4 == 1 ? (ap_uint<4>)  1 : (ap_uint<4>)  (_let_4 == 2 ? (ap_uint<4>)  2 : (ap_uint<4>)  (_let_4 == 3 ? (ap_uint<4>)  4 : (ap_uint<4>)  0))) : (ap_uint<4>)  _let_4)) >> (ap_int<5>)_let_3);
  ap_uint<4> __smt2c_ext_4 = ((ap_uint<5>)__smt2c_src_3).range(3, 0);
  return (ap_uint<8>)(_let_1 ? (ap_uint<4>)  _let_2 : (ap_uint<4>)  __smt2c_ext_2) << 4 | (ap_uint<8>)(_let_1 ? (ap_uint<4>)  ((ap_int<5>)_let_3 >= (ap_int<5>)4 ? (ap_uint<4>)  0 : (ap_uint<4>)  __smt2c_ext_4) : (ap_uint<4>)  _let_2);
}

ap_uint<9> add_raw(ap_uint<4> m1, ap_uint<4> e1, ap_uint<4> m2, ap_uint<4> e2) {
  ap_uint<8> _let_1 = align_mantissas(m1, e1, m2, e2);
  ap_uint<4> __smt2c_ext_0 = ((ap_uint<8>)_let_1).range(7, 4);
  ap_uint<4> __smt2c_ext_1 = ((ap_uint<8>)_let_1).range(3, 0);
  return (ap_uint<9>)((ap_uint<5>)(ap_int<5>)(ap_int<4>)__smt2c_ext_0 + (ap_uint<5>)(ap_int<5>)(ap_int<4>)__smt2c_ext_1) << 4 | (ap_uint<9>)select_exponent(e1, e2);
}

ap_uint<1> detect_overflow(ap_uint<5> raw_sum) {
  ap_uint<1> __smt2c_ext_0 = ((ap_uint<5>)raw_sum).range(4, 4);
  ap_uint<1> __smt2c_ext_1 = ((ap_uint<5>)raw_sum).range(3, 3);
  return !(__smt2c_ext_0 == __smt2c_ext_1) ? (ap_uint<1>)  1 : (ap_uint<1>)  0;
}

ap_uint<8> normalise_addition(ap_uint<5> raw_sum, ap_uint<4> target_exp) {
  ap_uint<5> _let_1 = (ap_int<5>)raw_sum < (ap_int<5>)0 ? (ap_uint<5>)  -raw_sum : (ap_uint<5>)  raw_sum;
  bool _let_2 = raw_sum == 0;
  ap_uint<1> __smt2c_ext_0 = ((ap_uint<5>)_let_1).range(4, 4);
  ap_uint<1> __smt2c_ext_1 = ((ap_uint<5>)_let_1).range(3, 3);
  ap_uint<1> __smt2c_ext_2 = ((ap_uint<5>)_let_1).range(2, 2);
  ap_uint<1> __smt2c_ext_3 = ((ap_uint<5>)_let_1).range(1, 1);
  ap_uint<5> _let_3 = _let_2 ? (ap_uint<5>)  0 : (ap_uint<5>)  (__smt2c_ext_0 == 1 ? (ap_uint<5>)  2 : (ap_uint<5>)  (__smt2c_ext_1 == 1 ? (ap_uint<5>)  1 : (ap_uint<5>)  (__smt2c_ext_2 == 1 ? (ap_uint<5>)  0 : (ap_uint<5>)  (__smt2c_ext_3 == 1 ? (ap_uint<5>)  31 : (ap_uint<5>)  30))));
  ap_uint<5> _let_4 = (ap_uint<5>)ap_int<5>((ap_int<4>((target_exp + _let_3))));
  ap_uint<5> __smt2c_src_4 = (ap_int<5>)_let_3 >= (ap_int<5>)0 ? (ap_uint<5>)  (ap_uint<5>)((ap_int<5>)raw_sum >> (ap_int<5>)_let_3) : (ap_uint<5>)  raw_sum << -_let_3;
  ap_uint<4> __smt2c_ext_5 = ((ap_uint<5>)__smt2c_src_4).range(3, 0);
  ap_uint<5> __smt2c_src_6 = (ap_int<5>)_let_4 > (ap_int<5>)7 ? (ap_uint<5>)  7 : (ap_uint<5>)  ((ap_int<5>)_let_4 < (ap_int<5>)24 ? (ap_uint<5>)  24 : (ap_uint<5>)  _let_4);
  ap_uint<4> __smt2c_ext_7 = ((ap_uint<5>)__smt2c_src_6).range(3, 0);
  return (ap_uint<8>)(_let_2 ? (ap_uint<4>)  0 : (ap_uint<4>)  __smt2c_ext_5) << 4 | (ap_uint<8>)(_let_2 ? (ap_uint<4>)  0 : (ap_uint<4>)  __smt2c_ext_7);
}

ap_uint<8> add_full_sum(ap_uint<4> m1, ap_uint<4> e1, ap_uint<4> m2, ap_uint<4> e2) {
  ap_uint<9> _let_1 = add_raw(m1, e1, m2, e2);
  ap_uint<5> __smt2c_ext_0 = ((ap_uint<9>)_let_1).range(8, 4);
  ap_uint<4> __smt2c_ext_1 = ((ap_uint<9>)_let_1).range(3, 0);
  return normalise_addition(__smt2c_ext_0, __smt2c_ext_1);
}
