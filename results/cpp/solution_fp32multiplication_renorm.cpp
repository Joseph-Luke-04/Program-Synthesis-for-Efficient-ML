#include <ap_int.h>

ap_uint<1> fp32_mult_renorm(ap_uint<24> Ma, ap_uint<24> Mb) {
  ap_uint<48> prod = (ap_uint<48>)Ma * (ap_uint<48>)Mb;
  return (ap_uint<1>)prod[47];
}
