ap_uint<4> select_exponent(ap_uint<4> e1, ap_uint<4> e2) {
  return (ap_int<4>)e1 >= (ap_int<4>)e2 ? (ap_uint<4>)  e1 : (ap_uint<4>)  e2;
}

unsigned char align_mantissas(ap_uint<4> m1, ap_uint<4> e1, ap_uint<4> m2, ap_uint<4> e2) {
  return ((ap_int<4>)e1 >= (ap_int<4>)e2 ? (ap_uint<4>)  m1 : (ap_uint<4>)  (ap_uint<4>)((ap_int<4>)m1 >> (ap_int<4>)(e2 - e1)),(ap_int<4>)e1 >= (ap_int<4>)e2 ? (ap_uint<4>)  (ap_uint<4>)((ap_int<4>)m2 >> (ap_int<4>)(e1 - e2)) : (ap_uint<4>)  m2);
}

ap_uint<9> add_raw(ap_uint<4> m1, ap_uint<4> e1, ap_uint<4> m2, ap_uint<4> e2) {
  return ((ap_uint<5>)(ap_int<5>)(ap_int<4>)align_mantissas(m1, e1, m2, e2)[4 + 3, 4] + (ap_uint<5>)(ap_int<5>)(ap_int<4>)align_mantissas(m1, e1, m2, e2)[0 + 3, 0],select_exponent(e1, e2));
}

unsigned char normalise_addition(ap_uint<5> raw_sum, ap_uint<4> target_exp) {
  return ((ap_int<5>)raw_sum > (ap_int<5>)7 || (ap_int<5>)raw_sum < (ap_int<5>)24 ? (ap_uint<4>)  (ap_uint<5>)((ap_int<5>)raw_sum >> (ap_int<5>)1)[0 + 3, 0] : (ap_uint<4>)  raw_sum << irep("(\"zero_extend\" \"\" (\"constant\" \"type\" (\"unsignedbv\" \"width\" (\"4\")) \"value\" (\"0\")) \"type\" (\"unsignedbv\" \"width\" (\"5\")))")[0 + 3, 0],(ap_int<5>)raw_sum > (ap_int<5>)7 || (ap_int<5>)raw_sum < (ap_int<5>)24 ? (ap_uint<4>)  target_exp + 1 : (ap_uint<4>)  target_exp - 0);
}

unsigned char add_full_sum(ap_uint<4> m1, ap_uint<4> e1, ap_uint<4> m2, ap_uint<4> e2) {
  return normalise_addition(add_raw(m1, e1, m2, e2)[4 + 4, 4], add_raw(m1, e1, m2, e2)[0 + 3, 0]);
}
