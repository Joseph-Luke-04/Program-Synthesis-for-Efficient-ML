unsigned char normalise_addition(ap_uint<5> raw_sum, ap_uint<4> target_exp) {
  return ((ap_int<5>)raw_sum > (ap_int<5>)7 || (ap_int<5>)raw_sum < (ap_int<5>)24 ? (ap_uint<4>)  (ap_uint<5>)((ap_int<5>)raw_sum >> (ap_int<5>)1)[0 + 3, 0] : (ap_uint<4>)  raw_sum << irep("(\"zero_extend\" \"\" (\"constant\" \"type\" (\"unsignedbv\" \"width\" (\"4\")) \"value\" (\"0\")) \"type\" (\"unsignedbv\" \"width\" (\"5\")))")[0 + 3, 0],(ap_int<5>)raw_sum > (ap_int<5>)7 || (ap_int<5>)raw_sum < (ap_int<5>)24 ? (ap_uint<4>)  target_exp + 1 : (ap_uint<4>)  target_exp - 0);
}
