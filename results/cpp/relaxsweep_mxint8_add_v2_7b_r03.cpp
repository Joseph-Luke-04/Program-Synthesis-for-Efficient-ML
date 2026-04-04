#include <ap_int.h>

ap_uint<5> norm_shifted5(ap_uint<5> raw) {
  ap_uint<5> abs5 = (ap_int<5>)raw < (ap_int<5>)0 ? (ap_uint<5>)((ap_uint<5>)  -raw) : (ap_uint<5>)  raw;
  ap_uint<1> __smt2c_ext_0 = ((ap_uint<5>)abs5).range(4, 4);
  ap_uint<1> __smt2c_ext_1 = ((ap_uint<5>)abs5).range(3, 3);
  ap_uint<1> __smt2c_ext_2 = ((ap_uint<5>)abs5).range(2, 2);
  ap_uint<1> __smt2c_ext_3 = ((ap_uint<5>)abs5).range(1, 1);
  ap_uint<5> __smt2c_result;
  if(raw == 0) {
    __smt2c_result = raw;
  }
  else if(__smt2c_ext_0 == 1) {
    __smt2c_result = (ap_uint<5>)((ap_int<5>)raw >> (ap_int<5>)2);
  }
  else if(__smt2c_ext_1 == 1) {
    __smt2c_result = (ap_uint<5>)((ap_int<5>)raw >> (ap_int<5>)1);
  }
  else if(__smt2c_ext_2 == 1) {
    __smt2c_result = raw;
  }
  else if(__smt2c_ext_3 == 1) {
    __smt2c_result = raw << 1;
  }
  else {
    __smt2c_result = raw << 2;
  }
  return __smt2c_result;
}

ap_uint<5> exp_delta5_from_raw(ap_uint<5> raw) {
  ap_uint<5> abs5 = (ap_int<5>)raw < (ap_int<5>)0 ? (ap_uint<5>)((ap_uint<5>)  -raw) : (ap_uint<5>)  raw;
  ap_uint<1> __smt2c_ext_0 = ((ap_uint<5>)abs5).range(4, 4);
  ap_uint<1> __smt2c_ext_1 = ((ap_uint<5>)abs5).range(3, 3);
  ap_uint<1> __smt2c_ext_2 = ((ap_uint<5>)abs5).range(2, 2);
  ap_uint<1> __smt2c_ext_3 = ((ap_uint<5>)abs5).range(1, 1);
  ap_uint<5> __smt2c_result;
  if(raw == 0) {
    __smt2c_result = 0;
  }
  else if(__smt2c_ext_0 == 1) {
    __smt2c_result = 2;
  }
  else if(__smt2c_ext_1 == 1) {
    __smt2c_result = 1;
  }
  else if(__smt2c_ext_2 == 1) {
    __smt2c_result = 0;
  }
  else if(__smt2c_ext_3 == 1) {
    __smt2c_result = 31;
  }
  else {
    __smt2c_result = 30;
  }
  return __smt2c_result;
}

ap_uint<4> sat_mant4(ap_uint<5> shifted) {
  ap_uint<4> __smt2c_ext_0 = ((ap_uint<5>)shifted).range(3, 0);
  ap_uint<4> __smt2c_result;
  if((ap_int<5>)shifted > (ap_int<5>)7) {
    __smt2c_result = 7;
  }
  else if((ap_int<5>)shifted < (ap_int<5>)24) {
    __smt2c_result = 8;
  }
  else {
    __smt2c_result = __smt2c_ext_0;
  }
  return __smt2c_result;
}

ap_uint<4> clamp_exp4(ap_uint<5> exp_adj) {
  ap_uint<5> __smt2c_src_0 = (ap_int<5>)exp_adj > (ap_int<5>)7 ? (ap_uint<5>)((ap_uint<5>)  7) : (ap_uint<5>)  ((ap_int<5>)exp_adj < (ap_int<5>)24 ? (ap_uint<5>)  24 : (ap_uint<5>)  exp_adj);
  ap_uint<4> __smt2c_ext_1 = ((ap_uint<5>)__smt2c_src_0).range(3, 0);
  return __smt2c_ext_1;
}

ap_uint<8> add_full_sum(ap_uint<4> m1, ap_uint<4> e1, ap_uint<4> m2, ap_uint<4> e2) {
  bool _let_1 = (ap_int<4>)e1 >= (ap_int<4>)e2;
  ap_uint<5> _let_2 = (ap_uint<5>)(ap_int<5>)(ap_int<4>)(_let_1 ? (ap_uint<4>)  e1 : (ap_uint<4>)  e2);
  ap_uint<5> _let_3 = _let_2 - (ap_uint<5>)(ap_int<5>)(ap_int<4>)(_let_1 ? (ap_uint<4>)  e2 : (ap_uint<4>)  e1);
  ap_uint<4> __smt2c_ext_0 = ((ap_uint<5>)_let_3).range(3, 0);
  ap_uint<4> _let_4 = __smt2c_ext_0;
  ap_uint<4> _let_5 = _let_1 ? (ap_uint<4>)  m2 : (ap_uint<4>)  m1;
  ap_uint<5> _let_6 = (ap_uint<5>)(ap_int<5>)(ap_int<4>)_let_5;
  ap_uint<5> _let_7 = (ap_uint<5>)(ap_int<5>)(ap_int<4>)(_let_1 ? (ap_uint<4>)  m1 : (ap_uint<4>)  m2);
  ap_uint<5> __smt2c_src_1 = (ap_uint<5>)((ap_int<5>)(_let_6 + (ap_uint<5>)(ap_int<5>)(ap_int<4>)_let_4) >> (ap_int<5>)_let_3);
  ap_uint<4> __smt2c_ext_2 = ((ap_uint<5>)__smt2c_src_1).range(3, 0);
  ap_uint<5> __smt2c_src_3 = _let_2 + exp_delta5_from_raw(_let_7 + (ap_uint<5>)(ap_int<5>)(ap_int<4>)__smt2c_ext_2);
  ap_uint<4> __smt2c_ext_4 = ((ap_uint<5>)__smt2c_src_3).range(3, 0);
  ap_uint<5> __smt2c_src_5 = (ap_uint<5>)((ap_int<5>)(_let_6 + (ap_uint<5>)(ap_int<5>)(ap_int<4>)((ap_int<4>)_let_5 < (ap_int<4>)0 ? (ap_uint<4>)  -0 : (ap_uint<4>)  _let_4)) >> (ap_int<5>)_let_3);
  ap_uint<4> __smt2c_ext_6 = ((ap_uint<5>)__smt2c_src_5).range(3, 0);
  return (ap_uint<8>)__smt2c_ext_4 << 4 | (ap_uint<8>)(_let_7 + _let_7 == 0 ? (ap_uint<4>)  0 : (ap_uint<4>)  sat_mant4(norm_shifted5(_let_7 + (ap_uint<5>)(ap_int<5>)(ap_int<4>)__smt2c_ext_6)));
}
