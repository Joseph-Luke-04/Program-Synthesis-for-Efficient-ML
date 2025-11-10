#include <ap_int.h>

ap_uint<9> add_raw(ap_uint<4> m1, ap_uint<4> e1, ap_uint<4> m2, ap_uint<4> e2) {
  return ap_uint<9>((ap_uint<4>(((ap_uint<4>(((ap_uint<5>)(ap_int<5>)(ap_int<4>)((ap_int<4>)e1 >= (ap_int<4>)e2 ? (ap_uint<4>)  m1 : (ap_uint<4>)  (ap_uint<4>)((ap_int<4>)m1 >> (ap_int<4>)(e2 - e1)),(ap_int<4>)e1 >= (ap_int<4>)e2 ? (ap_uint<4>)  (ap_uint<4>)((ap_int<4>)m2 >> (ap_int<4>)(e1 - e2)) : (ap_uint<4>)  m2)))).range(7, 4) + (ap_uint<5>)(ap_int<5>)(ap_int<4>)((ap_int<4>)e1 >= (ap_int<4>)e2 ? (ap_uint<4>)  m1 : (ap_uint<4>)  (ap_uint<4>)((ap_int<4>)m1 >> (ap_int<4>)(e2 - e1)),(ap_int<4>)e1 >= (ap_int<4>)e2 ? (ap_uint<4>)  (ap_uint<4>)((ap_int<4>)m2 >> (ap_int<4>)(e1 - e2)) : (ap_uint<4>)  m2))).range(3, 0),(ap_int<4>)e1 >= (ap_int<4>)e2 ? (ap_uint<4>)  e1 : (ap_uint<4>)  e2));
}
