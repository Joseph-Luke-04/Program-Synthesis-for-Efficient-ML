ap_uint<1> fp32_mult_renorm(ap_uint<24> Ma, ap_uint<24> Mb) {
  ap_uint<48> __smt2c_src_0 = (ap_uint<48>)Ma * (ap_uint<48>)Mb;
  ap_uint<1> __smt2c_ext_1 = ((ap_uint<48>)__smt2c_src_0).range(47, 47);
  return __smt2c_ext_1;
}

unsigned char fp32_mult_exp(unsigned char ea, unsigned char eb, ap_uint<1> renorm, ap_uint<1> carry) {
  ap_uint<10> __smt2c_src_0 = (((ap_uint<10>)ea + (ap_uint<10>)eb) - 127) + (ap_uint<10>)renorm;
  unsigned char __smt2c_ext_1 = ((ap_uint<10>)__smt2c_src_0).range(7, 0);
  return __smt2c_ext_1;
}

ap_uint<23> fp32_mult_mant(ap_uint<24> Ma, ap_uint<24> Mb, ap_uint<1> renorm) {
  ap_uint<48> _let_1 = (ap_uint<48>)Ma * (ap_uint<48>)Mb;
  ap_uint<48> _let_2 = renorm == 1 ? (ap_uint<48>)  _let_1 >> 1 : (ap_uint<48>)  _let_1;
  ap_uint<24> __smt2c_ext_0 = ((ap_uint<48>)_let_2).range(46, 23);
  ap_uint<23> __smt2c_ext_1 = ((ap_uint<24>)__smt2c_ext_0).range(22, 0);
  ap_uint<1> __smt2c_ext_2 = ((ap_uint<48>)_let_2).range(22, 22);
  return __smt2c_ext_1 + (ap_uint<23>)__smt2c_ext_2;
}

unsigned int fp32_full_mul(unsigned int a, unsigned int b) {
  ap_uint<23> __smt2c_ext_0 = ((ap_uint<32>)b).range(22, 0);
  ap_uint<24> _let_1 = (ap_uint<24>)1 << 23 | (ap_uint<24>)__smt2c_ext_0;
  ap_uint<23> __smt2c_ext_1 = ((ap_uint<32>)a).range(22, 0);
  ap_uint<24> _let_2 = (ap_uint<24>)1 << 23 | (ap_uint<24>)__smt2c_ext_1;
  ap_uint<1> _let_3 = fp32_mult_renorm(_let_2, _let_1);
  ap_uint<1> __smt2c_ext_2 = ((ap_uint<32>)a).range(31, 31);
  ap_uint<1> __smt2c_ext_3 = ((ap_uint<32>)b).range(31, 31);
  unsigned char __smt2c_ext_4 = ((ap_uint<32>)a).range(30, 23);
  unsigned char __smt2c_ext_5 = ((ap_uint<32>)b).range(30, 23);
  return (unsigned int)(__smt2c_ext_2 ^ __smt2c_ext_3) << 31 | (unsigned int)((ap_uint<31>)fp32_mult_exp(__smt2c_ext_4, __smt2c_ext_5, _let_3, 0) << 23 | (ap_uint<31>)fp32_mult_mant(_let_2, _let_1, _let_3));
}
