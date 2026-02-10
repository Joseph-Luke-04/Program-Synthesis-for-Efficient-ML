#include <ap_int.h>

ap_uint<4> mult_mxint_mant(ap_uint<4> m1, ap_uint<4> m2) {
  return (ap_int<8>)((ap_int<8>)(ap_uint<8>((ap_int<8>((ap_int<4>((m1 * (ap_uint<8>)(ap_int<8>)(ap_int<4>) (m2))))))) < (ap_int<8>)0 ? ap_uint<8>(((ap_uint<8>)  -(ap_uint<8>((ap_int<8>((ap_int<4>((m1 * (ap_uint<8>)(ap_int<8>)(ap_int<4>)m2))))))))) : ap_uint<8>((ap_uint<8>((ap_int<8>((ap_int<4>((m1 * (ap_uint<8>)(ap_int<8>)(ap_int<4>)m2)))))))))) <= (ap_int<8>) (32 ? (ap_uint<8>)  (ap_uint<8>)((ap_int<8>)(ap_uint<8>((ap_int<8>((ap_int<4>((m1 * (ap_uint<8>)(ap_int<8>)(ap_int<4>)m2)))))) << 1) >> (ap_int<8>)3) : (ap_uint<8>)  (ap_uint<8>)(ap_uint<4>((((ap_int<8>)(ap_uint<8>((ap_int<8>((ap_int<4>((m1 * (ap_uint<8>)(ap_int<8>)(ap_int<4>)m2))))))) >> (ap_int<8>)3)))).range(3, 0));
}
