#include <ap_int.h>

ap_uint<4> select_exponent(ap_uint<4> e1, ap_uint<4> e2) {
  return (ap_int<4>)e1 >= (ap_int<4>)e2 ? ap_uint<4>(((ap_uint<4>)  e1)) : ap_uint<4>(((ap_uint<4>)  e2));
}

ap_uint<8> align_mantissas(ap_uint<4> m1, ap_uint<4> e1, ap_uint<4> m2, ap_uint<4> e2) {
  return ((ap_int<4>)e1 >= (ap_int<4>)e2 ? (ap_uint<4>)  m1 : (ap_uint<4>)  (ap_uint<4>)((ap_int<4>)m1 >> (ap_int<4>)(e2 - e1)),(ap_int<4>)e1 >= (ap_int<4>)e2 ? (ap_uint<4>)  (ap_uint<4>)((ap_int<4>)m2 >> (ap_int<4>)(e1 - e2)) : (ap_uint<4>)  m2);
}

ap_uint<9> add_raw(ap_uint<4> m1, ap_uint<4> e1, ap_uint<4> m2, ap_uint<4> e2) {
  return ((ap_uint<5>)(ap_int<5>)(ap_int<4>)(ap_uint<4>((align_mantissas(m1, e1, m2, e2)))).range(7, 4) + (ap_uint<5>)(ap_int<5>)(ap_int<4>)(ap_uint<4>((align_mantissas(m1, e1, m2, e2)))).range(3, 0),select_exponent(e1, e2));
}
