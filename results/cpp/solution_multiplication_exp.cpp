#include <ap_int.h>

ap_uint<4> mult_mxint_exp(ap_uint<4> e1, ap_uint<4> e2, bool renorm_flag) {
  return renorm_flag ? ap_uint<4>(((e1 + e2) - 1)) : ap_uint<4>((e1 + e2));
}
