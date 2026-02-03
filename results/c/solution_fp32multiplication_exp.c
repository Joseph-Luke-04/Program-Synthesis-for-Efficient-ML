ap_uint<1> fp32_mult_renorm(ap_uint<24> Ma, ap_uint<24> Mb) {
  return irep("(\"zero_extend\" \"\" (\"symbol\" \"type\" (\"unsignedbv\" \"width\" (\"24\")) \"identifier\" (\"Ma\")) \"type\" (\"unsignedbv\" \"width\" (\"48\")))") * irep("(\"zero_extend\" \"\" (\"symbol\" \"type\" (\"unsignedbv\" \"width\" (\"24\")) \"identifier\" (\"Mb\")) \"type\" (\"unsignedbv\" \"width\" (\"48\")))")[47 + 0, 47];
}

unsigned char fp32_mult_exp(unsigned char ea, unsigned char eb, ap_uint<1> renorm, ap_uint<1> carry) {
  return ((irep("(\"zero_extend\" \"\" (\"symbol\" \"type\" (\"unsignedbv\" \"width\" (\"8\")) \"identifier\" (\"ea\")) \"type\" (\"unsignedbv\" \"width\" (\"10\")))") + irep("(\"zero_extend\" \"\" (\"symbol\" \"type\" (\"unsignedbv\" \"width\" (\"8\")) \"identifier\" (\"eb\")) \"type\" (\"unsignedbv\" \"width\" (\"10\")))")) - 127) + irep("(\"zero_extend\" \"\" (\"symbol\" \"type\" (\"unsignedbv\" \"width\" (\"1\")) \"identifier\" (\"renorm\")) \"type\" (\"unsignedbv\" \"width\" (\"10\")))")[0 + 7, 0];
}
