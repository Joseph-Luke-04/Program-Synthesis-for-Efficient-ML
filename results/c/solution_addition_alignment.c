unsigned __CPROVER_bitvector[4] select_exponent(unsigned __CPROVER_bitvector[4] e1, unsigned __CPROVER_bitvector[4] e2) {
  return (signed __CPROVER_bitvector[4])e1 >= (signed __CPROVER_bitvector[4])e2 ? e1 : e2;
}
