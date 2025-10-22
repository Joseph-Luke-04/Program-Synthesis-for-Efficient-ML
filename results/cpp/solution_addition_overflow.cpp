#include <ap_int.h>

ap_uint<1> detect_overflow(ap_uint<5> raw_sum) {
  if ((ap_int<5>)raw_sum > (ap_int<5>)7 || (ap_int<5>)raw_sum < (ap_int<5>)24) { return 1; }
else { return 0; }

}
