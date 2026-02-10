#include <ap_int.h>

ap_uint<1> fp32_mult_renorm(ap_uint<24> Ma, ap_uint<24> Mb) {
  ap_uint<48> prod = (ap_uint<48>)Ma * (ap_uint<48>)Mb;
  return (ap_uint<1>)prod[47];
}


ap_uint<8> fp32_mult_exp(ap_uint<8> ea, ap_uint<8> eb, ap_uint<1> renorm, ap_uint<1> carry) {
  ap_uint<10> sum = (ap_uint<10>)ea + (ap_uint<10>)eb;
  ap_uint<10> adj = sum - (ap_uint<10>)127 + (ap_uint<10>)renorm;
  return (ap_uint<8>)adj;
}


ap_uint<23> fp32_mult_mant(ap_uint<24> Ma, ap_uint<24> Mb, ap_uint<1> renorm) {
  ap_uint<48> prod = (ap_uint<48>)Ma * (ap_uint<48>)Mb;
  ap_uint<48> pn = (renorm == 1) ? (prod >> 1) : prod;
  ap_uint<24> top = (ap_uint<24>)pn.range(46, 23);
  ap_uint<1> round = (ap_uint<1>)pn[22];
  ap_uint<24> rounded = top + (ap_uint<24>)round;
  return (ap_uint<23>)rounded.range(22, 0);
}


ap_uint<32> fp32_full_mul(ap_uint<32> a, ap_uint<32> b) {
  ap_uint<24> Ma = (ap_uint<24>)(((ap_uint<24>)1 << 23) | (ap_uint<23>)a.range(22, 0));
  ap_uint<24> Mb = (ap_uint<24>)(((ap_uint<24>)1 << 23) | (ap_uint<23>)b.range(22, 0));
  ap_uint<1> renorm = fp32_mult_renorm(Ma, Mb);
  ap_uint<8> exp = fp32_mult_exp((ap_uint<8>)a.range(30, 23),
                                 (ap_uint<8>)b.range(30, 23),
                                 renorm, (ap_uint<1>)0);
  ap_uint<23> frac = fp32_mult_mant(Ma, Mb, renorm);
  ap_uint<1> sign = (ap_uint<1>)(a[31] ^ b[31]);
  return (ap_uint<32>)(((ap_uint<32>)sign << 31) | ((ap_uint<32>)exp << 23) | (ap_uint<32>)frac);
}
