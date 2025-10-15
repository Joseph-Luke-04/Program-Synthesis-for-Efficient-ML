unsigned __CPROVER_bitvector[4] mult_mxint_exp(unsigned __CPROVER_bitvector[4] e1, unsigned __CPROVER_bitvector[4] e2, unsigned __CPROVER_bitvector[1] renorm_flag) {
  return renorm_flag == 1 ? (e1 + e2) - 1 : e1 + e2;
}
