#include <ap_int.h>

ap_uint<48> fp32_mult_raw48_renorm(ap_uint<24> Ma, ap_uint<24> Mb) {
  return (ap_uint<48>)Ma * (ap_uint<48>)Mb;
}

ap_uint<1> fp32_mult_renorm(ap_uint<24> Ma, ap_uint<24> Mb) {
  ap_uint<48> __smt2c_src_0 = fp32_mult_raw48_renorm(Ma, Mb);
  ap_uint<1> __smt2c_ext_1 = ((ap_uint<48>)__smt2c_src_0).range(47, 47);
  return __smt2c_ext_1;
}

ap_uint<48> fp32_mult_raw48_carry(ap_uint<24> Ma, ap_uint<24> Mb) {
  return (ap_uint<48>)Ma * (ap_uint<48>)Mb;
}

ap_uint<1> fp32_mult_round_carry(ap_uint<24> Ma, ap_uint<24> Mb, ap_uint<1> renorm) {
  ap_uint<48> _let_1 = fp32_mult_raw48_carry(Ma, Mb);
  ap_uint<1> __smt2c_ext_0 = ((ap_uint<48>)_let_1).range(22, 22);
  ap_uint<24> __smt2c_ext_1 = ((ap_uint<48>)_let_1).range(46, 23);
  return __smt2c_ext_0 == 1 && __smt2c_ext_1 == 16777215 ? (ap_uint<1>)  1 : (ap_uint<1>)  0;
}

ap_uint<8> fp32_mult_exp(ap_uint<8> ea, ap_uint<8> eb, ap_uint<1> renorm, ap_uint<1> carry) {
  ap_uint<10> __smt2c_src_0 = (((ap_uint<10>)(ap_int<10>)(ap_int<8>)ea + (ap_uint<10>)(ap_int<10>)(ap_int<8>)eb) - 127) + (ap_uint<10>)renorm;
  ap_uint<8> __smt2c_ext_1 = ((ap_uint<10>)__smt2c_src_0).range(7, 0);
  return __smt2c_ext_1;
}

ap_uint<48> fp32_mult_raw48(ap_uint<24> Ma, ap_uint<24> Mb) {
  return (ap_uint<48>)Ma * (ap_uint<48>)Mb;
}

ap_uint<23> fp32_mult_mant(ap_uint<24> Ma, ap_uint<24> Mb, ap_uint<1> renorm) {
  ap_uint<48> _let_1 = fp32_mult_raw48(Ma, Mb) >> (ap_uint<48>)renorm;
  ap_uint<24> __smt2c_ext_0 = ((ap_uint<48>)_let_1).range(46, 23);
  ap_uint<1> __smt2c_ext_1 = ((ap_uint<48>)_let_1).range(22, 22);
  ap_uint<24> __smt2c_src_2 = __smt2c_ext_0 + (ap_uint<24>)__smt2c_ext_1;
  ap_uint<23> __smt2c_ext_3 = ((ap_uint<24>)__smt2c_src_2).range(22, 0);
  return __smt2c_ext_3;
}

ap_uint<32> fp32_full_mul(ap_uint<32> a, ap_uint<32> b) {
  ap_uint<23> __smt2c_ext_0 = ((ap_uint<32>)b).range(22, 0);
  ap_uint<24> _let_1 = (ap_uint<24>)1 << 23 | (ap_uint<24>)__smt2c_ext_0;
  ap_uint<23> __smt2c_ext_1 = ((ap_uint<32>)a).range(22, 0);
  ap_uint<24> _let_2 = (ap_uint<24>)1 << 23 | (ap_uint<24>)__smt2c_ext_1;
  ap_uint<1> _let_3 = fp32_mult_renorm(_let_2, _let_1);
  ap_uint<1> __smt2c_ext_2 = ((ap_uint<32>)a).range(31, 31);
  ap_uint<1> __smt2c_ext_3 = ((ap_uint<32>)b).range(31, 31);
  ap_uint<8> __smt2c_ext_4 = ((ap_uint<32>)a).range(30, 23);
  ap_uint<8> __smt2c_ext_5 = ((ap_uint<32>)b).range(30, 23);
  return (ap_uint<32>)(__smt2c_ext_2 ^ __smt2c_ext_3) << 31 | (ap_uint<32>)((ap_uint<31>)fp32_mult_exp(__smt2c_ext_4, __smt2c_ext_5, _let_3, fp32_mult_round_carry(_let_2, _let_1, _let_3)) << 23 | (ap_uint<31>)fp32_mult_mant(_let_2, _let_1, _let_3));
}
