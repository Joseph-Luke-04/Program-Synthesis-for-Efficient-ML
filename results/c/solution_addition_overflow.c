unsigned __CPROVER_bitvector[1] detect_overflow(unsigned __CPROVER_bitvector[5] raw_sum) {
  return (signed __CPROVER_bitvector[5])raw_sum > (signed __CPROVER_bitvector[5])7 || (signed __CPROVER_bitvector[5])raw_sum < (signed __CPROVER_bitvector[5])24 ? 1 : 0;
}
