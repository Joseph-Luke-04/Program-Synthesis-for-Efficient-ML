#include <ap_int.h>

ap_uint<23> fp32_mult_mant(ap_uint<24> Ma, ap_uint<24> Mb, ap_uint<1> renorm) {
  ap_uint<48> prod = (ap_uint<48>)Ma * (ap_uint<48>)Mb;
  ap_uint<48> shifted = (renorm == 1) ? (prod >> 1) : prod;
  ap_uint<24> top = (ap_uint<24>)shifted.range(46, 23);
  ap_uint<1> round = (ap_uint<1>)shifted[22];
  ap_uint<24> rounded = top + (ap_uint<24>)round;
  return (ap_uint<23>)rounded.range(22, 0);
}
