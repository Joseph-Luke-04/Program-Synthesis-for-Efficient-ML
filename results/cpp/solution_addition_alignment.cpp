#include <ap_int.h>

ap_uint<4> select_exponent(ap_uint<4> e1, ap_uint<4> e2) {
  return (ap_int<4>)e1 >= (ap_int<4>)e2 ? ap_uint<4>((e1)) : ap_uint<4>((e2));
}
