unsigned int fp32_full_mul(unsigned int a, unsigned int b) {
  ap_uint<23> __smt2c_ext_0 = ((ap_uint<32>)b).range(22, 0);
  ap_uint<23> _let_1 = __smt2c_ext_0;
  ap_uint<23> __smt2c_ext_1 = ((ap_uint<32>)a).range(22, 0);
  ap_uint<23> _let_2 = __smt2c_ext_1;
  ap_uint<1> __smt2c_ext_2 = ((ap_uint<32>)a).range(31, 31);
  ap_uint<1> __smt2c_ext_3 = ((ap_uint<32>)b).range(31, 31);
  unsigned char __smt2c_ext_4 = ((ap_uint<32>)a).range(30, 23);
  unsigned char __smt2c_ext_5 = ((ap_uint<32>)b).range(30, 23);
  ap_uint<48> __smt2c_src_6 = (ap_uint<48>)((ap_uint<24>)1 << 23 | (ap_uint<24>)_let_2) * (ap_uint<48>)((ap_uint<24>)1 << 23 | (ap_uint<24>)_let_1);
  ap_uint<1> __smt2c_ext_7 = ((ap_uint<48>)__smt2c_src_6).range(47, 47);
  ap_uint<48> __smt2c_src_8 = (ap_uint<48>)(ap_uint<24>)_let_2 * (ap_uint<48>)(ap_uint<24>)_let_1;
  ap_uint<23> __smt2c_ext_9 = ((ap_uint<48>)__smt2c_src_8).range(22, 0);
  return (unsigned int)(__smt2c_ext_2 ^ __smt2c_ext_3) << 31 | (unsigned int)((ap_uint<31>)(((__smt2c_ext_4 + __smt2c_ext_5) - 127) + (unsigned char)__smt2c_ext_7) << 23 | (ap_uint<31>)__smt2c_ext_9);
}
