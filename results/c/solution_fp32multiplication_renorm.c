ap_uint<1> fp32_mult_renorm(ap_uint<24> Ma, ap_uint<24> Mb) {
  return irep("(\"zero_extend\" \"\" (\"symbol\" \"type\" (\"unsignedbv\" \"width\" (\"24\")) \"identifier\" (\"Ma\")) \"type\" (\"unsignedbv\" \"width\" (\"48\")))") * irep("(\"zero_extend\" \"\" (\"symbol\" \"type\" (\"unsignedbv\" \"width\" (\"24\")) \"identifier\" (\"Mb\")) \"type\" (\"unsignedbv\" \"width\" (\"48\")))")[47 + 0, 47];
}
