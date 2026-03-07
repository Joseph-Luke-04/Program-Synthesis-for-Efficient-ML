#include <ap_int.h>

ap_uint<56> fp32_aligner(ap_uint<8> e1, ap_uint<23> m1, ap_uint<8> e2, ap_uint<23> m2) {
  __CPROVER_bool _let_1 = e1 >= e2;
  ap_uint<24> _let_2 = (ap_uint<24>)(e2 == 0 ? (ap_uint<1>)  0 : (ap_uint<1>)  1) << 23 | (ap_uint<24>)m2;
  ap_uint<24> _let_3 = (ap_uint<24>)0 << 8 | (ap_uint<24>)(_let_1 ? (ap_uint<8>)  e1 - e2 : (ap_uint<8>)  e2 - e1);
  ap_uint<24> _let_4 = (ap_uint<24>)(e1 == 0 ? (ap_uint<1>)  0 : (ap_uint<1>)  1) << 23 | (ap_uint<24>)m1;
  return (ap_uint<56>)(_let_1 ? (ap_uint<24>)  _let_4 : (ap_uint<24>)  _let_4 >> _let_3) << 32 | (ap_uint<56>)((ap_uint<32>)(_let_1 ? (ap_uint<24>)  _let_2 >> _let_3 : (ap_uint<24>)  _let_2) << 8 | (ap_uint<32>)(_let_1 ? (ap_uint<8>)  e1 : (ap_uint<8>)  e2));
}

ap_uint<26> fp32_raw_summer(ap_uint<1> s1, ap_uint<24> aligned_m1, ap_uint<1> s2, ap_uint<24> aligned_m2) {
  ap_uint<25> _let_1 = (ap_uint<25>)0 << 24 | (ap_uint<25>)aligned_m1;
  ap_uint<25> _let_2 = (ap_uint<25>)0 << 24 | (ap_uint<25>)aligned_m2;
  __CPROVER_bool _let_3 = aligned_m1 >= aligned_m2;
  __CPROVER_bool _let_4 = s1 == s2;
  return (ap_uint<26>)(!_let_4 && aligned_m1 == aligned_m2 ? (ap_uint<1>)  0 : (ap_uint<1>)  (_let_4 ? (ap_uint<1>)  s1 : (ap_uint<1>)  (_let_3 ? (ap_uint<1>)  s1 : (ap_uint<1>)  s2))) << 25 | (ap_uint<26>)(_let_4 ? (ap_uint<25>)  _let_1 + _let_2 : (ap_uint<25>)  (_let_3 ? (ap_uint<25>)  _let_1 - _let_2 : (ap_uint<25>)  _let_2 - _let_1));
}

ap_uint<32> fp32_normaliser(ap_uint<25> raw_sum_mantissa, ap_uint<1> raw_sign, ap_uint<8> target_exponent) {
  ap_uint<1> __smt2c_ext_0 = ((ap_uint<25>)raw_sum_mantissa).range(0, 0);
  ap_uint<1> _let_1 = __smt2c_ext_0;
  __CPROVER_bool _let_2 = _let_1 == 1;
  ap_uint<1> __smt2c_ext_1 = ((ap_uint<25>)raw_sum_mantissa).range(1, 1);
  __CPROVER_bool _let_3 = __smt2c_ext_1 == 1;
  ap_uint<1> __smt2c_ext_2 = ((ap_uint<25>)raw_sum_mantissa).range(2, 2);
  __CPROVER_bool _let_4 = __smt2c_ext_2 == 1;
  ap_uint<1> __smt2c_ext_3 = ((ap_uint<25>)raw_sum_mantissa).range(3, 3);
  __CPROVER_bool _let_5 = __smt2c_ext_3 == 1;
  ap_uint<1> __smt2c_ext_4 = ((ap_uint<25>)raw_sum_mantissa).range(4, 4);
  __CPROVER_bool _let_6 = __smt2c_ext_4 == 1;
  ap_uint<1> __smt2c_ext_5 = ((ap_uint<25>)raw_sum_mantissa).range(5, 5);
  __CPROVER_bool _let_7 = __smt2c_ext_5 == 1;
  ap_uint<1> __smt2c_ext_6 = ((ap_uint<25>)raw_sum_mantissa).range(6, 6);
  __CPROVER_bool _let_8 = __smt2c_ext_6 == 1;
  ap_uint<1> __smt2c_ext_7 = ((ap_uint<25>)raw_sum_mantissa).range(7, 7);
  __CPROVER_bool _let_9 = __smt2c_ext_7 == 1;
  ap_uint<1> __smt2c_ext_8 = ((ap_uint<25>)raw_sum_mantissa).range(8, 8);
  __CPROVER_bool _let_10 = __smt2c_ext_8 == 1;
  ap_uint<1> __smt2c_ext_9 = ((ap_uint<25>)raw_sum_mantissa).range(9, 9);
  __CPROVER_bool _let_11 = __smt2c_ext_9 == 1;
  ap_uint<1> __smt2c_ext_10 = ((ap_uint<25>)raw_sum_mantissa).range(10, 10);
  __CPROVER_bool _let_12 = __smt2c_ext_10 == 1;
  ap_uint<1> __smt2c_ext_11 = ((ap_uint<25>)raw_sum_mantissa).range(11, 11);
  __CPROVER_bool _let_13 = __smt2c_ext_11 == 1;
  ap_uint<1> __smt2c_ext_12 = ((ap_uint<25>)raw_sum_mantissa).range(12, 12);
  __CPROVER_bool _let_14 = __smt2c_ext_12 == 1;
  ap_uint<1> __smt2c_ext_13 = ((ap_uint<25>)raw_sum_mantissa).range(13, 13);
  __CPROVER_bool _let_15 = __smt2c_ext_13 == 1;
  ap_uint<1> __smt2c_ext_14 = ((ap_uint<25>)raw_sum_mantissa).range(14, 14);
  __CPROVER_bool _let_16 = __smt2c_ext_14 == 1;
  ap_uint<1> __smt2c_ext_15 = ((ap_uint<25>)raw_sum_mantissa).range(15, 15);
  __CPROVER_bool _let_17 = __smt2c_ext_15 == 1;
  ap_uint<1> __smt2c_ext_16 = ((ap_uint<25>)raw_sum_mantissa).range(16, 16);
  __CPROVER_bool _let_18 = __smt2c_ext_16 == 1;
  ap_uint<1> __smt2c_ext_17 = ((ap_uint<25>)raw_sum_mantissa).range(17, 17);
  __CPROVER_bool _let_19 = __smt2c_ext_17 == 1;
  ap_uint<1> __smt2c_ext_18 = ((ap_uint<25>)raw_sum_mantissa).range(18, 18);
  __CPROVER_bool _let_20 = __smt2c_ext_18 == 1;
  ap_uint<1> __smt2c_ext_19 = ((ap_uint<25>)raw_sum_mantissa).range(19, 19);
  __CPROVER_bool _let_21 = __smt2c_ext_19 == 1;
  ap_uint<1> __smt2c_ext_20 = ((ap_uint<25>)raw_sum_mantissa).range(20, 20);
  __CPROVER_bool _let_22 = __smt2c_ext_20 == 1;
  ap_uint<1> __smt2c_ext_21 = ((ap_uint<25>)raw_sum_mantissa).range(21, 21);
  __CPROVER_bool _let_23 = __smt2c_ext_21 == 1;
  ap_uint<1> __smt2c_ext_22 = ((ap_uint<25>)raw_sum_mantissa).range(22, 22);
  __CPROVER_bool _let_24 = __smt2c_ext_22 == 1;
  ap_uint<1> __smt2c_ext_23 = ((ap_uint<25>)raw_sum_mantissa).range(23, 23);
  __CPROVER_bool _let_25 = __smt2c_ext_23 == 1;
  ap_uint<1> __smt2c_ext_24 = ((ap_uint<25>)raw_sum_mantissa).range(24, 24);
  __CPROVER_bool _let_26 = __smt2c_ext_24 == 1;
  __CPROVER_bool _let_27 = raw_sum_mantissa == 0;
  ap_uint<24> __smt2c_ext_25 = ((ap_uint<25>)raw_sum_mantissa).range(24, 1);
  ap_uint<24> __smt2c_ext_26 = ((ap_uint<25>)raw_sum_mantissa).range(23, 0);
  ap_uint<23> __smt2c_ext_27 = ((ap_uint<25>)raw_sum_mantissa).range(22, 0);
  ap_uint<22> __smt2c_ext_28 = ((ap_uint<25>)raw_sum_mantissa).range(21, 0);
  ap_uint<21> __smt2c_ext_29 = ((ap_uint<25>)raw_sum_mantissa).range(20, 0);
  ap_uint<20> __smt2c_ext_30 = ((ap_uint<25>)raw_sum_mantissa).range(19, 0);
  ap_uint<19> __smt2c_ext_31 = ((ap_uint<25>)raw_sum_mantissa).range(18, 0);
  ap_uint<18> __smt2c_ext_32 = ((ap_uint<25>)raw_sum_mantissa).range(17, 0);
  ap_uint<17> __smt2c_ext_33 = ((ap_uint<25>)raw_sum_mantissa).range(16, 0);
  unsigned short ap_int<32> __smt2c_ext_34 = ((ap_uint<25>)raw_sum_mantissa).range(15, 0);
  ap_uint<15> __smt2c_ext_35 = ((ap_uint<25>)raw_sum_mantissa).range(14, 0);
  ap_uint<14> __smt2c_ext_36 = ((ap_uint<25>)raw_sum_mantissa).range(13, 0);
  ap_uint<13> __smt2c_ext_37 = ((ap_uint<25>)raw_sum_mantissa).range(12, 0);
  ap_uint<12> __smt2c_ext_38 = ((ap_uint<25>)raw_sum_mantissa).range(11, 0);
  ap_uint<11> __smt2c_ext_39 = ((ap_uint<25>)raw_sum_mantissa).range(10, 0);
  ap_uint<10> __smt2c_ext_40 = ((ap_uint<25>)raw_sum_mantissa).range(9, 0);
  ap_uint<9> __smt2c_ext_41 = ((ap_uint<25>)raw_sum_mantissa).range(8, 0);
  ap_uint<8> __smt2c_ext_42 = ((ap_uint<25>)raw_sum_mantissa).range(7, 0);
  ap_uint<7> __smt2c_ext_43 = ((ap_uint<25>)raw_sum_mantissa).range(6, 0);
  ap_uint<6> __smt2c_ext_44 = ((ap_uint<25>)raw_sum_mantissa).range(5, 0);
  ap_uint<5> __smt2c_ext_45 = ((ap_uint<25>)raw_sum_mantissa).range(4, 0);
  ap_uint<4> __smt2c_ext_46 = ((ap_uint<25>)raw_sum_mantissa).range(3, 0);
  ap_uint<3> __smt2c_ext_47 = ((ap_uint<25>)raw_sum_mantissa).range(2, 0);
  ap_uint<2> __smt2c_ext_48 = ((ap_uint<25>)raw_sum_mantissa).range(1, 0);
  ap_uint<24> __smt2c_src_49 = _let_26 ? (ap_uint<24>)  __smt2c_ext_25 : (ap_uint<24>)  (_let_25 ? (ap_uint<24>)  __smt2c_ext_26 : (ap_uint<24>)  (_let_24 ? (ap_uint<24>)  (ap_uint<24>)__smt2c_ext_27 << 1 | (ap_uint<24>)0 : (ap_uint<24>)  (_let_23 ? (ap_uint<24>)  (ap_uint<24>)__smt2c_ext_28 << 2 | (ap_uint<24>)0 : (ap_uint<24>)  (_let_22 ? (ap_uint<24>)  (ap_uint<24>)__smt2c_ext_29 << 3 | (ap_uint<24>)0 : (ap_uint<24>)  (_let_21 ? (ap_uint<24>)  (ap_uint<24>)__smt2c_ext_30 << 4 | (ap_uint<24>)0 : (ap_uint<24>)  (_let_20 ? (ap_uint<24>)  (ap_uint<24>)__smt2c_ext_31 << 5 | (ap_uint<24>)0 : (ap_uint<24>)  (_let_19 ? (ap_uint<24>)  (ap_uint<24>)__smt2c_ext_32 << 6 | (ap_uint<24>)0 : (ap_uint<24>)  (_let_18 ? (ap_uint<24>)  (ap_uint<24>)__smt2c_ext_33 << 7 | (ap_uint<24>)0 : (ap_uint<24>)  (_let_17 ? (ap_uint<24>)  (ap_uint<24>)__smt2c_ext_34 << 8 | (ap_uint<24>)0 : (ap_uint<24>)  (_let_16 ? (ap_uint<24>)  (ap_uint<24>)__smt2c_ext_35 << 9 | (ap_uint<24>)0 : (ap_uint<24>)  (_let_15 ? (ap_uint<24>)  (ap_uint<24>)__smt2c_ext_36 << 10 | (ap_uint<24>)0 : (ap_uint<24>)  (_let_14 ? (ap_uint<24>)  (ap_uint<24>)__smt2c_ext_37 << 11 | (ap_uint<24>)0 : (ap_uint<24>)  (_let_13 ? (ap_uint<24>)  (ap_uint<24>)__smt2c_ext_38 << 12 | (ap_uint<24>)0 : (ap_uint<24>)  (_let_12 ? (ap_uint<24>)  (ap_uint<24>)__smt2c_ext_39 << 13 | (ap_uint<24>)0 : (ap_uint<24>)  (_let_11 ? (ap_uint<24>)  (ap_uint<24>)__smt2c_ext_40 << 14 | (ap_uint<24>)0 : (ap_uint<24>)  (_let_10 ? (ap_uint<24>)  (ap_uint<24>)__smt2c_ext_41 << 15 | (ap_uint<24>)0 : (ap_uint<24>)  (_let_9 ? (ap_uint<24>)  (ap_uint<24>)__smt2c_ext_42 << 16 | (ap_uint<24>)0 : (ap_uint<24>)  (_let_8 ? (ap_uint<24>)  (ap_uint<24>)__smt2c_ext_43 << 17 | (ap_uint<24>)0 : (ap_uint<24>)  (_let_7 ? (ap_uint<24>)  (ap_uint<24>)__smt2c_ext_44 << 18 | (ap_uint<24>)0 : (ap_uint<24>)  (_let_6 ? (ap_uint<24>)  (ap_uint<24>)__smt2c_ext_45 << 19 | (ap_uint<24>)0 : (ap_uint<24>)  (_let_5 ? (ap_uint<24>)  (ap_uint<24>)__smt2c_ext_46 << 20 | (ap_uint<24>)0 : (ap_uint<24>)  (_let_4 ? (ap_uint<24>)  (ap_uint<24>)__smt2c_ext_47 << 21 | (ap_uint<24>)0 : (ap_uint<24>)  (_let_3 ? (ap_uint<24>)  (ap_uint<24>)__smt2c_ext_48 << 22 | (ap_uint<24>)0 : (ap_uint<24>)  (_let_2 ? (ap_uint<24>)  (ap_uint<24>)_let_1 << 23 | (ap_uint<24>)0 : (ap_uint<24>)  0))))))))))))))))))))))));
  ap_uint<23> __smt2c_ext_50 = ((ap_uint<24>)__smt2c_src_49).range(22, 0);
  return (ap_uint<32>)(_let_27 ? (ap_uint<1>)  0 : (ap_uint<1>)  raw_sign) << 31 | (ap_uint<32>)((ap_uint<31>)(_let_27 ? (ap_uint<8>)  0 : (ap_uint<8>)  target_exponent + (_let_26 ? (ap_uint<8>)  1 : (ap_uint<8>)  (_let_25 ? (ap_uint<8>)  0 : (ap_uint<8>)  (_let_24 ? (ap_uint<8>)  -1 : (ap_uint<8>)  (_let_23 ? (ap_uint<8>)  -2 : (ap_uint<8>)  (_let_22 ? (ap_uint<8>)  -3 : (ap_uint<8>)  (_let_21 ? (ap_uint<8>)  -4 : (ap_uint<8>)  (_let_20 ? (ap_uint<8>)  -5 : (ap_uint<8>)  (_let_19 ? (ap_uint<8>)  -6 : (ap_uint<8>)  (_let_18 ? (ap_uint<8>)  -7 : (ap_uint<8>)  (_let_17 ? (ap_uint<8>)  -8 : (ap_uint<8>)  (_let_16 ? (ap_uint<8>)  -9 : (ap_uint<8>)  (_let_15 ? (ap_uint<8>)  -10 : (ap_uint<8>)  (_let_14 ? (ap_uint<8>)  -11 : (ap_uint<8>)  (_let_13 ? (ap_uint<8>)  -12 : (ap_uint<8>)  (_let_12 ? (ap_uint<8>)  -13 : (ap_uint<8>)  (_let_11 ? (ap_uint<8>)  -14 : (ap_uint<8>)  (_let_10 ? (ap_uint<8>)  -15 : (ap_uint<8>)  (_let_9 ? (ap_uint<8>)  -16 : (ap_uint<8>)  (_let_8 ? (ap_uint<8>)  -17 : (ap_uint<8>)  (_let_7 ? (ap_uint<8>)  -18 : (ap_uint<8>)  (_let_6 ? (ap_uint<8>)  -19 : (ap_uint<8>)  (_let_5 ? (ap_uint<8>)  -20 : (ap_uint<8>)  (_let_4 ? (ap_uint<8>)  -21 : (ap_uint<8>)  (_let_3 ? (ap_uint<8>)  -22 : (ap_uint<8>)  (_let_2 ? (ap_uint<8>)  -23 : (ap_uint<8>)  0)))))))))))))))))))))))))) << 23 | (ap_uint<31>)__smt2c_ext_50);
}

ap_uint<32> fp32_sum(ap_uint<1> s1, ap_uint<8> e1, ap_uint<23> m1, ap_uint<1> s2, ap_uint<8> e2, ap_uint<23> m2) {
  ap_uint<56> _let_1 = fp32_aligner(e1, m1, e2, m2);
  ap_uint<24> __smt2c_ext_0 = ((ap_uint<56>)_let_1).range(55, 32);
  ap_uint<24> __smt2c_ext_1 = ((ap_uint<56>)_let_1).range(31, 8);
  ap_uint<26> _let_2 = fp32_raw_summer(s1, __smt2c_ext_0, s2, __smt2c_ext_1);
  ap_uint<25> __smt2c_ext_2 = ((ap_uint<26>)_let_2).range(24, 0);
  ap_uint<1> __smt2c_ext_3 = ((ap_uint<26>)_let_2).range(25, 25);
  ap_uint<8> __smt2c_ext_4 = ((ap_uint<56>)_let_1).range(7, 0);
  return fp32_normaliser(__smt2c_ext_2, __smt2c_ext_3, __smt2c_ext_4);
}
