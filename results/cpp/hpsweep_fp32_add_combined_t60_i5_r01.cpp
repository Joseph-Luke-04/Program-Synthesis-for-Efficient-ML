#include <ap_int.h>

ap_uint<24> shr24_sat(ap_uint<24> x, ap_uint<8> d) {
  return d >= 24 ? (ap_uint<24>)  0 : (ap_uint<24>)  x >> (ap_uint<24>)d;
}

ap_uint<24> norm24_from_raw(ap_uint<25> raw) {
  ap_uint<1> __smt2c_ext_0 = ((ap_uint<25>)raw).range(24, 24);
  ap_uint<24> __smt2c_ext_1 = ((ap_uint<25>)raw).range(24, 1);
  ap_uint<1> __smt2c_ext_2 = ((ap_uint<25>)raw).range(23, 23);
  ap_uint<24> __smt2c_ext_3 = ((ap_uint<25>)raw).range(23, 0);
  ap_uint<1> __smt2c_ext_4 = ((ap_uint<25>)raw).range(22, 22);
  ap_uint<23> __smt2c_ext_5 = ((ap_uint<25>)raw).range(22, 0);
  ap_uint<1> __smt2c_ext_6 = ((ap_uint<25>)raw).range(21, 21);
  ap_uint<22> __smt2c_ext_7 = ((ap_uint<25>)raw).range(21, 0);
  ap_uint<1> __smt2c_ext_8 = ((ap_uint<25>)raw).range(20, 20);
  ap_uint<21> __smt2c_ext_9 = ((ap_uint<25>)raw).range(20, 0);
  ap_uint<1> __smt2c_ext_10 = ((ap_uint<25>)raw).range(19, 19);
  ap_uint<20> __smt2c_ext_11 = ((ap_uint<25>)raw).range(19, 0);
  ap_uint<1> __smt2c_ext_12 = ((ap_uint<25>)raw).range(18, 18);
  ap_uint<19> __smt2c_ext_13 = ((ap_uint<25>)raw).range(18, 0);
  ap_uint<1> __smt2c_ext_14 = ((ap_uint<25>)raw).range(17, 17);
  ap_uint<18> __smt2c_ext_15 = ((ap_uint<25>)raw).range(17, 0);
  ap_uint<1> __smt2c_ext_16 = ((ap_uint<25>)raw).range(16, 16);
  ap_uint<17> __smt2c_ext_17 = ((ap_uint<25>)raw).range(16, 0);
  ap_uint<1> __smt2c_ext_18 = ((ap_uint<25>)raw).range(15, 15);
  ap_uint<16> __smt2c_ext_19 = ((ap_uint<25>)raw).range(15, 0);
  ap_uint<1> __smt2c_ext_20 = ((ap_uint<25>)raw).range(14, 14);
  ap_uint<15> __smt2c_ext_21 = ((ap_uint<25>)raw).range(14, 0);
  ap_uint<1> __smt2c_ext_22 = ((ap_uint<25>)raw).range(13, 13);
  ap_uint<14> __smt2c_ext_23 = ((ap_uint<25>)raw).range(13, 0);
  ap_uint<1> __smt2c_ext_24 = ((ap_uint<25>)raw).range(12, 12);
  ap_uint<13> __smt2c_ext_25 = ((ap_uint<25>)raw).range(12, 0);
  ap_uint<1> __smt2c_ext_26 = ((ap_uint<25>)raw).range(11, 11);
  ap_uint<12> __smt2c_ext_27 = ((ap_uint<25>)raw).range(11, 0);
  ap_uint<1> __smt2c_ext_28 = ((ap_uint<25>)raw).range(10, 10);
  ap_uint<11> __smt2c_ext_29 = ((ap_uint<25>)raw).range(10, 0);
  ap_uint<1> __smt2c_ext_30 = ((ap_uint<25>)raw).range(9, 9);
  ap_uint<10> __smt2c_ext_31 = ((ap_uint<25>)raw).range(9, 0);
  ap_uint<1> __smt2c_ext_32 = ((ap_uint<25>)raw).range(8, 8);
  ap_uint<9> __smt2c_ext_33 = ((ap_uint<25>)raw).range(8, 0);
  ap_uint<1> __smt2c_ext_34 = ((ap_uint<25>)raw).range(7, 7);
  ap_uint<8> __smt2c_ext_35 = ((ap_uint<25>)raw).range(7, 0);
  ap_uint<1> __smt2c_ext_36 = ((ap_uint<25>)raw).range(6, 6);
  ap_uint<7> __smt2c_ext_37 = ((ap_uint<25>)raw).range(6, 0);
  ap_uint<1> __smt2c_ext_38 = ((ap_uint<25>)raw).range(5, 5);
  ap_uint<6> __smt2c_ext_39 = ((ap_uint<25>)raw).range(5, 0);
  ap_uint<1> __smt2c_ext_40 = ((ap_uint<25>)raw).range(4, 4);
  ap_uint<5> __smt2c_ext_41 = ((ap_uint<25>)raw).range(4, 0);
  ap_uint<1> __smt2c_ext_42 = ((ap_uint<25>)raw).range(3, 3);
  ap_uint<4> __smt2c_ext_43 = ((ap_uint<25>)raw).range(3, 0);
  ap_uint<1> __smt2c_ext_44 = ((ap_uint<25>)raw).range(2, 2);
  ap_uint<3> __smt2c_ext_45 = ((ap_uint<25>)raw).range(2, 0);
  ap_uint<1> __smt2c_ext_46 = ((ap_uint<25>)raw).range(1, 1);
  ap_uint<2> __smt2c_ext_47 = ((ap_uint<25>)raw).range(1, 0);
  ap_uint<1> __smt2c_ext_48 = ((ap_uint<25>)raw).range(0, 0);
  ap_uint<24> __smt2c_result;
  if(raw == 0) {
    __smt2c_result = 0;
  }
  else if(__smt2c_ext_0 == 1) {
    __smt2c_result = __smt2c_ext_1;
  }
  else if(__smt2c_ext_2 == 1) {
    __smt2c_result = __smt2c_ext_3;
  }
  else if(__smt2c_ext_4 == 1) {
    __smt2c_result = (ap_uint<24>)__smt2c_ext_5 << 1 | (ap_uint<24>)0;
  }
  else if(__smt2c_ext_6 == 1) {
    __smt2c_result = (ap_uint<24>)__smt2c_ext_7 << 2 | (ap_uint<24>)0;
  }
  else if(__smt2c_ext_8 == 1) {
    __smt2c_result = (ap_uint<24>)__smt2c_ext_9 << 3 | (ap_uint<24>)0;
  }
  else if(__smt2c_ext_10 == 1) {
    __smt2c_result = (ap_uint<24>)__smt2c_ext_11 << 4 | (ap_uint<24>)0;
  }
  else if(__smt2c_ext_12 == 1) {
    __smt2c_result = (ap_uint<24>)__smt2c_ext_13 << 5 | (ap_uint<24>)0;
  }
  else if(__smt2c_ext_14 == 1) {
    __smt2c_result = (ap_uint<24>)__smt2c_ext_15 << 6 | (ap_uint<24>)0;
  }
  else if(__smt2c_ext_16 == 1) {
    __smt2c_result = (ap_uint<24>)__smt2c_ext_17 << 7 | (ap_uint<24>)0;
  }
  else if(__smt2c_ext_18 == 1) {
    __smt2c_result = (ap_uint<24>)__smt2c_ext_19 << 8 | (ap_uint<24>)0;
  }
  else if(__smt2c_ext_20 == 1) {
    __smt2c_result = (ap_uint<24>)__smt2c_ext_21 << 9 | (ap_uint<24>)0;
  }
  else if(__smt2c_ext_22 == 1) {
    __smt2c_result = (ap_uint<24>)__smt2c_ext_23 << 10 | (ap_uint<24>)0;
  }
  else if(__smt2c_ext_24 == 1) {
    __smt2c_result = (ap_uint<24>)__smt2c_ext_25 << 11 | (ap_uint<24>)0;
  }
  else if(__smt2c_ext_26 == 1) {
    __smt2c_result = (ap_uint<24>)__smt2c_ext_27 << 12 | (ap_uint<24>)0;
  }
  else if(__smt2c_ext_28 == 1) {
    __smt2c_result = (ap_uint<24>)__smt2c_ext_29 << 13 | (ap_uint<24>)0;
  }
  else if(__smt2c_ext_30 == 1) {
    __smt2c_result = (ap_uint<24>)__smt2c_ext_31 << 14 | (ap_uint<24>)0;
  }
  else if(__smt2c_ext_32 == 1) {
    __smt2c_result = (ap_uint<24>)__smt2c_ext_33 << 15 | (ap_uint<24>)0;
  }
  else if(__smt2c_ext_34 == 1) {
    __smt2c_result = (ap_uint<24>)__smt2c_ext_35 << 16 | (ap_uint<24>)0;
  }
  else if(__smt2c_ext_36 == 1) {
    __smt2c_result = (ap_uint<24>)__smt2c_ext_37 << 17 | (ap_uint<24>)0;
  }
  else if(__smt2c_ext_38 == 1) {
    __smt2c_result = (ap_uint<24>)__smt2c_ext_39 << 18 | (ap_uint<24>)0;
  }
  else if(__smt2c_ext_40 == 1) {
    __smt2c_result = (ap_uint<24>)__smt2c_ext_41 << 19 | (ap_uint<24>)0;
  }
  else if(__smt2c_ext_42 == 1) {
    __smt2c_result = (ap_uint<24>)__smt2c_ext_43 << 20 | (ap_uint<24>)0;
  }
  else if(__smt2c_ext_44 == 1) {
    __smt2c_result = (ap_uint<24>)__smt2c_ext_45 << 21 | (ap_uint<24>)0;
  }
  else if(__smt2c_ext_46 == 1) {
    __smt2c_result = (ap_uint<24>)__smt2c_ext_47 << 22 | (ap_uint<24>)0;
  }
  else {
    __smt2c_result = (ap_uint<24>)__smt2c_ext_48 << 23 | (ap_uint<24>)0;
  }
  return __smt2c_result;
}

ap_uint<8> exp_delta_from_raw(ap_uint<25> raw) {
  ap_uint<1> __smt2c_ext_0 = ((ap_uint<25>)raw).range(24, 24);
  ap_uint<1> __smt2c_ext_1 = ((ap_uint<25>)raw).range(23, 23);
  ap_uint<1> __smt2c_ext_2 = ((ap_uint<25>)raw).range(22, 22);
  ap_uint<1> __smt2c_ext_3 = ((ap_uint<25>)raw).range(21, 21);
  ap_uint<1> __smt2c_ext_4 = ((ap_uint<25>)raw).range(20, 20);
  ap_uint<1> __smt2c_ext_5 = ((ap_uint<25>)raw).range(19, 19);
  ap_uint<1> __smt2c_ext_6 = ((ap_uint<25>)raw).range(18, 18);
  ap_uint<1> __smt2c_ext_7 = ((ap_uint<25>)raw).range(17, 17);
  ap_uint<1> __smt2c_ext_8 = ((ap_uint<25>)raw).range(16, 16);
  ap_uint<1> __smt2c_ext_9 = ((ap_uint<25>)raw).range(15, 15);
  ap_uint<1> __smt2c_ext_10 = ((ap_uint<25>)raw).range(14, 14);
  ap_uint<1> __smt2c_ext_11 = ((ap_uint<25>)raw).range(13, 13);
  ap_uint<1> __smt2c_ext_12 = ((ap_uint<25>)raw).range(12, 12);
  ap_uint<1> __smt2c_ext_13 = ((ap_uint<25>)raw).range(11, 11);
  ap_uint<1> __smt2c_ext_14 = ((ap_uint<25>)raw).range(10, 10);
  ap_uint<1> __smt2c_ext_15 = ((ap_uint<25>)raw).range(9, 9);
  ap_uint<1> __smt2c_ext_16 = ((ap_uint<25>)raw).range(8, 8);
  ap_uint<1> __smt2c_ext_17 = ((ap_uint<25>)raw).range(7, 7);
  ap_uint<1> __smt2c_ext_18 = ((ap_uint<25>)raw).range(6, 6);
  ap_uint<1> __smt2c_ext_19 = ((ap_uint<25>)raw).range(5, 5);
  ap_uint<1> __smt2c_ext_20 = ((ap_uint<25>)raw).range(4, 4);
  ap_uint<1> __smt2c_ext_21 = ((ap_uint<25>)raw).range(3, 3);
  ap_uint<1> __smt2c_ext_22 = ((ap_uint<25>)raw).range(2, 2);
  ap_uint<1> __smt2c_ext_23 = ((ap_uint<25>)raw).range(1, 1);
  ap_uint<8> __smt2c_result;
  if(raw == 0) {
    __smt2c_result = 0;
  }
  else if(__smt2c_ext_0 == 1) {
    __smt2c_result = 1;
  }
  else if(__smt2c_ext_1 == 1) {
    __smt2c_result = 0;
  }
  else if(__smt2c_ext_2 == 1) {
    __smt2c_result = -1;
  }
  else if(__smt2c_ext_3 == 1) {
    __smt2c_result = -2;
  }
  else if(__smt2c_ext_4 == 1) {
    __smt2c_result = -3;
  }
  else if(__smt2c_ext_5 == 1) {
    __smt2c_result = -4;
  }
  else if(__smt2c_ext_6 == 1) {
    __smt2c_result = -5;
  }
  else if(__smt2c_ext_7 == 1) {
    __smt2c_result = -6;
  }
  else if(__smt2c_ext_8 == 1) {
    __smt2c_result = -7;
  }
  else if(__smt2c_ext_9 == 1) {
    __smt2c_result = -8;
  }
  else if(__smt2c_ext_10 == 1) {
    __smt2c_result = -9;
  }
  else if(__smt2c_ext_11 == 1) {
    __smt2c_result = -10;
  }
  else if(__smt2c_ext_12 == 1) {
    __smt2c_result = -11;
  }
  else if(__smt2c_ext_13 == 1) {
    __smt2c_result = -12;
  }
  else if(__smt2c_ext_14 == 1) {
    __smt2c_result = -13;
  }
  else if(__smt2c_ext_15 == 1) {
    __smt2c_result = -14;
  }
  else if(__smt2c_ext_16 == 1) {
    __smt2c_result = -15;
  }
  else if(__smt2c_ext_17 == 1) {
    __smt2c_result = -16;
  }
  else if(__smt2c_ext_18 == 1) {
    __smt2c_result = -17;
  }
  else if(__smt2c_ext_19 == 1) {
    __smt2c_result = -18;
  }
  else if(__smt2c_ext_20 == 1) {
    __smt2c_result = -19;
  }
  else if(__smt2c_ext_21 == 1) {
    __smt2c_result = -20;
  }
  else if(__smt2c_ext_22 == 1) {
    __smt2c_result = -21;
  }
  else if(__smt2c_ext_23 == 1) {
    __smt2c_result = -22;
  }
  else {
    __smt2c_result = -23;
  }
  return __smt2c_result;
}

ap_uint<32> fp32_sum(ap_uint<1> s1, ap_uint<8> e1, ap_uint<23> m1, ap_uint<1> s2, ap_uint<8> e2, ap_uint<23> m2) {
  ap_uint<24> _let_1 = (ap_uint<24>)1 << 23 | (ap_uint<24>)m1;
  ap_uint<24> _let_2 = (ap_uint<24>)1 << 23 | (ap_uint<24>)m2;
  bool _let_3 = e1 > e2;
  ap_uint<25> _let_4 = (ap_uint<25>)(_let_3 ? (ap_uint<24>)  _let_2 : (ap_uint<24>)  _let_1);
  ap_uint<25> _let_5 = (ap_uint<25>)(_let_3 ? (ap_uint<24>)  _let_1 : (ap_uint<24>)  _let_2);
  ap_uint<25> __smt2c_src_0 = _let_5 - _let_4;
  ap_uint<23> __smt2c_ext_1 = ((ap_uint<25>)__smt2c_src_0).range(22, 0);
  return (ap_uint<32>)s1 << 31 | (ap_uint<32>)((ap_uint<31>)((_let_3 ? (ap_uint<8>)  e1 : (ap_uint<8>)  e2) + exp_delta_from_raw(_let_5 + _let_4)) << 23 | (ap_uint<31>)__smt2c_ext_1);
}
