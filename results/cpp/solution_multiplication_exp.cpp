#include <ap_int.h>

ap_uint<4> mult_mxint_exp(ap_uint<4> e1, ap_uint<4> e2, ap_uint<1> renorm_flag) {
  if (renorm_flag == 1) return (e1 + e2) - 1; else return e1 + e2;
}
