#include <ap_int.h>

ap_uint<8> normalise_addition(ap_uint<5> raw_sum, ap_uint<4> target_exp) {
  return ap_uint<8>(((ap_int<5>)raw_sum > (ap_int<5>)7 || (ap_int<5>)raw_sum < (ap_int<5>)24 ? (ap_uint<4>)  (ap_uint<5>)(ap_uint<4>((((ap_int<5>)raw_sum >> (ap_int<5>)1)))).range(3, 0) : (ap_uint<4>)  raw_sum[3, 0],(ap_int<5>)raw_sum > (ap_int<5>)7 || (ap_int<5>)raw_sum < (ap_int<5>)24 ? ap_uint<4>((target_exp + 1)) : ap_uint<4>((target_exp))));
}
