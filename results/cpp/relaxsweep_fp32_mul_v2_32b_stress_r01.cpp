#include <ap_int.h>

ap_uint<32> fp32_full_mul(ap_uint<32> a, ap_uint<32> b) {
  ap_uint<23> __smt2c_ext_0 = ((ap_uint<32>)a).range(22, 0);
  ap_uint<23> __smt2c_ext_1 = ((ap_uint<32>)b).range(22, 0);
  ap_uint<48> _let_1 = (ap_uint<48>)((ap_uint<24>)1 << 23 | (ap_uint<24>)__smt2c_ext_0) * (ap_uint<48>)((ap_uint<24>)1 << 23 | (ap_uint<24>)__smt2c_ext_1);
  ap_uint<1> __smt2c_ext_2 = ((ap_uint<48>)_let_1).range(47, 47);
  ap_uint<1> _let_2 = __smt2c_ext_2;
  ap_uint<48> _let_3 = _let_2 == 1 ? (ap_uint<48>)((ap_uint<48>)  _let_1 >> 1) : (ap_uint<48>)  _let_1;
  ap_uint<1> __smt2c_ext_3 = ((ap_uint<32>)a).range(31, 31);
  ap_uint<1> __smt2c_ext_4 = ((ap_uint<32>)b).range(31, 31);
  ap_uint<8> __smt2c_ext_5 = ((ap_uint<32>)a).range(30, 23);
  ap_uint<8> __smt2c_ext_6 = ((ap_uint<32>)b).range(30, 23);
  ap_uint<24> __smt2c_ext_7 = ((ap_uint<48>)_let_3).range(46, 23);
  ap_uint<1> __smt2c_ext_8 = ((ap_uint<48>)_let_3).range(22, 22);
  ap_uint<25> __smt2c_src_9 = ap_uint<25>((__smt2c_ext_7 + (ap_uint<25>)__smt2c_ext_8));
  ap_uint<24> __smt2c_ext_10 = ((ap_uint<25>)__smt2c_src_9).range(23, 0);
  ap_uint<23> __smt2c_ext_11 = ((ap_uint<24>)__smt2c_ext_10).range(22, 0);
  return (ap_uint<32>)(__smt2c_ext_3 ^ __smt2c_ext_4) << 31 | (ap_uint<32>)((ap_uint<31>)(((__smt2c_ext_5 + __smt2c_ext_6) - 127) + (ap_uint<8>)_let_2) << 23 | (ap_uint<31>)__smt2c_ext_11);
}
