#include <ap_int.h>

ap_uint<26> fp32_raw_summer(ap_uint<1> s1, ap_uint<24> aligned_m1, ap_uint<1> s2, ap_uint<24> aligned_m2) {
  return (!(s1 == s2) && aligned_m1 == aligned_m2 ? (ap_uint<1>)  0 : (ap_uint<1>)  (s1 == s2 ? (ap_uint<1>)  s1 : (ap_uint<1>)  (aligned_m1 >= aligned_m2 ? (ap_uint<1>)  s1 : (ap_uint<1>)  s2)),s1 == s2 ? ap_uint<25>(((0,aligned_m1) + (0,aligned_m2))) : (ap_uint<25>)  (aligned_m1 >= aligned_m2 ? ap_uint<25>(((0,aligned_m1) - (0,aligned_m2))) : ap_uint<25>(((0,aligned_m2) - (0,aligned_m1)))));
}
