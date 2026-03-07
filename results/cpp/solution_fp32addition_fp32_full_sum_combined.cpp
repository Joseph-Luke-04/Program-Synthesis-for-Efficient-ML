#include <ap_int.h>

ap_uint<24> shr24_0_7(ap_uint<24> x, ap_uint<3> d3) {
  ap_uint<24> __smt2c_result;
  if(d3 == 0) {
    __smt2c_result = x;
  }
  else if(d3 == 1) {
    __smt2c_result = x >> 1;
  }
  else if(d3 == 2) {
    __smt2c_result = x >> 2;
  }
  else if(d3 == 3) {
    __smt2c_result = x >> 3;
  }
  else if(d3 == 4) {
    __smt2c_result = x >> 4;
  }
  else if(d3 == 5) {
    __smt2c_result = x >> 5;
  }
  else if(d3 == 6) {
    __smt2c_result = x >> 6;
  }
  else {
    __smt2c_result = x >> 7;
  }
  return __smt2c_result;
}

ap_uint<27> shr27_0_7(ap_uint<27> x, ap_uint<3> d3) {
  ap_uint<27> __smt2c_result;
  if(d3 == 0) {
    __smt2c_result = x;
  }
  else if(d3 == 1) {
    __smt2c_result = x >> 1;
  }
  else if(d3 == 2) {
    __smt2c_result = x >> 2;
  }
  else if(d3 == 3) {
    __smt2c_result = x >> 3;
  }
  else if(d3 == 4) {
    __smt2c_result = x >> 4;
  }
  else if(d3 == 5) {
    __smt2c_result = x >> 5;
  }
  else if(d3 == 6) {
    __smt2c_result = x >> 6;
  }
  else {
    __smt2c_result = x >> 7;
  }
  return __smt2c_result;
}

ap_uint<28> shr28_0_7(ap_uint<28> x, ap_uint<3> d3) {
  ap_uint<28> __smt2c_result;
  if(d3 == 0) {
    __smt2c_result = x;
  }
  else if(d3 == 1) {
    __smt2c_result = x >> 1;
  }
  else if(d3 == 2) {
    __smt2c_result = x >> 2;
  }
  else if(d3 == 3) {
    __smt2c_result = x >> 3;
  }
  else if(d3 == 4) {
    __smt2c_result = x >> 4;
  }
  else if(d3 == 5) {
    __smt2c_result = x >> 5;
  }
  else if(d3 == 6) {
    __smt2c_result = x >> 6;
  }
  else {
    __smt2c_result = x >> 7;
  }
  return __smt2c_result;
}

ap_uint<28> shl28_0_3(ap_uint<28> x, ap_uint<2> d2) {
  ap_uint<28> __smt2c_result;
  if(d2 == 0) {
    __smt2c_result = x;
  }
  else if(d2 == 1) {
    __smt2c_result = x << 1;
  }
  else if(d2 == 2) {
    __smt2c_result = x << 2;
  }
  else {
    __smt2c_result = x << 3;
  }
  return __smt2c_result;
}

ap_uint<32> fp32_sum(ap_uint<1> s1, ap_uint<8> e1, ap_uint<23> m1, ap_uint<1> s2, ap_uint<8> e2, ap_uint<23> m2) {
  return (ap_uint<32>)s2 << 31 | (ap_uint<32>)((ap_uint<31>)128 << 23 | (ap_uint<31>)m2);
}
