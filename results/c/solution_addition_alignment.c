ap_uint<4> select_exponent(ap_uint<4> e1, ap_uint<4> e2) {
  return (ap_int<4>)e1 >= (ap_int<4>)e2 ? (ap_uint<4>)  e1 : (ap_uint<4>)  e2;
}

unsigned char align_mantissas(ap_uint<4> m1, ap_uint<4> e1, ap_uint<4> m2, ap_uint<4> e2) {
  return ((ap_int<4>)e1 >= (ap_int<4>)e2 ? (ap_uint<4>)  m1 : (ap_uint<4>)  (ap_uint<4>)((ap_int<4>)m1 >> (ap_int<4>)(e2 - e1)),(ap_int<4>)e1 >= (ap_int<4>)e2 ? (ap_uint<4>)  (ap_uint<4>)((ap_int<4>)m2 >> (ap_int<4>)(e1 - e2)) : (ap_uint<4>)  m2);
}
