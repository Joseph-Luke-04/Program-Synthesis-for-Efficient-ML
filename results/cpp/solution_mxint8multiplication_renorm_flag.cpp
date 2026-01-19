#include <ap_int.h>

ap_uint<1> mult_renorm_flag(ap_uint<4> m1, ap_uint<4> m2) {
  return (ap_int<8>)((ap_int<8>)(ap_uint<8>((ap_int<8>((ap_int<4>((m1 * (ap_uint<8>)(ap_int<8>)(ap_int<4>)m2))))))) < (ap_int<8>)0 ? (ap_uint<8>)  -(ap_uint<8>((ap_int<8>((ap_int<4>((m1 * (ap_uint<8>)(ap_int<8>)(ap_int<4>)m2))))))) : ap_uint<8>((ap_uint<8>((ap_int<8>((ap_int<4>((m1 * (ap_uint<8>)(ap_int<8>)(ap_int<4>)m2))))))))) <= (ap_int<8>)32 ? ap_uint<1>(((ap_uint<1>)  1)) : ap_uint<1>(((ap_uint<1>)  0));
}
