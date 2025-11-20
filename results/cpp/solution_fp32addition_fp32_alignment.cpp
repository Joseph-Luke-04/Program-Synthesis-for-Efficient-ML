#include <ap_int.h>

ap_uint<56> fp32_aligner(ap_uint<8> e1, ap_uint<23> m1, ap_uint<8> e2, ap_uint<23> m2) {
  return ap_uint<56>(((ap_uint<56>)((ap_uint<56>)((e1 >= e2 ? (ap_uint<24>)  (e1 == 0 ? (ap_uint<1>)  0 : (ap_uint<1>)  1,m1) : (ap_uint<24>)  (e1 == 0 ? (ap_uint<1>)  0 : (ap_uint<1>)  1,m1) >> (0,e1 >= e2 ? ap_uint<8>((e1 - e2)) : ap_uint<8>((e2 - e1))))) << 52)) | (ap_uint<4>)(((e1 >= e2 ? (ap_uint<24>)  (e2 == 0 ? (ap_uint<1>)  0 : (ap_uint<1>)  1,m2) >> (0,e1 >= e2 ? ap_uint<8>((e1 - e2)) : ap_uint<8>((e2 - e1))) : (ap_uint<24>)  (e2 == 0 ? (ap_uint<1>)  0 : (ap_uint<1>)  1,m2),e1 >= e2 ? (ap_uint<8>)  e1 : (ap_uint<8>)  e2))));
}
