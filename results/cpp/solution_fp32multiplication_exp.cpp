#include <ap_int.h>

ap_uint<1> fp32_mult_renorm(ap_uint<24> Ma, ap_uint<24> Mb) {
  ap_uint<48> prod = (ap_uint<48>)Ma * (ap_uint<48>)Mb;
  return (ap_uint<1>)prod[47];
}


ap_uint<8> fp32_mult_exp(ap_uint<8> ea, ap_uint<8> eb, ap_uint<1> renorm, ap_uint<1> carry) {
  ap_uint<10> sum = (ap_uint<10>)ea + (ap_uint<10>)eb;
  ap_uint<10> adj = sum - (ap_uint<10>)127 + (ap_uint<10>)renorm + (ap_uint<10>)carry;
  return (ap_uint<8>)adj;
}
