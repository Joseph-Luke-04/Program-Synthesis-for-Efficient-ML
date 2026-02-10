#include <ap_int.h>

ap_uint<32> fp32_sum(ap_uint<1> s1, ap_uint<8> e1, ap_uint<23> m1, ap_uint<1> s2, ap_uint<8> e2, ap_uint<23> m2) {
  ap_uint<24> let1 = (ap_uint<24>)(((ap_uint<24>)1 << 23) | (ap_uint<23>)m2);
  ap_uint<24> let2 = (ap_uint<24>)(((ap_uint<24>)1 << 23) | (ap_uint<23>)m1);

  bool let3 = (e1 < e2) || ((e1 == e2) && (let2 < let1));
  ap_uint<8> let4 = let3 ? e2 : e1;
  ap_uint<8> esmall = let3 ? e1 : e2;
  ap_uint<6> let5 = (ap_uint<6>)(let4 - esmall);

  ap_uint<27> small27 = (ap_uint<27>)(((ap_uint<27>)(let3 ? let2 : let1)) << 3);
  ap_uint<27> let6 = (ap_uint<27>)(small27 >> let5);
  ap_uint<1> let7 = (ap_uint<1>)(let5 > (ap_uint<6>)0b011010);

  ap_uint<28> let8 = (ap_uint<28>)(let7 ? (ap_uint<27>)0 : let6);
  ap_uint<27> big27 = (ap_uint<27>)(((ap_uint<27>)(let3 ? let1 : let2)) << 3);
  ap_uint<28> let9 = (ap_uint<28>)big27;
  ap_uint<28> let10 = (ap_uint<28>)(let9 - let8);

  ap_uint<1> let11 = (ap_uint<1>)(let3 ? s2 : s1);
  bool let12 = (let11 == (let3 ? s1 : s2));

  ap_uint<28> let13 = let12
      ? (ap_uint<28>)(let9 + (ap_uint<28>)(let7 ? (ap_uint<27>)1 : let6))
      : let10;
  ap_uint<1> let14 = (ap_uint<1>)(let13[27] == 1);
  ap_uint<28> let15 = let14
      ? (ap_uint<28>)((let12 ? (ap_uint<28>)(let9 + let8) : let10) >> 1)
      : let13;

  bool let16 = ((ap_uint<28>)(let15 << 1)) == 0;

  ap_uint<1> sign = let16 ? (ap_uint<1>)0 : let11;
  ap_uint<8> exp = let16
      ? (ap_uint<8>)0
      : (ap_uint<8>)((ap_uint<10>)let4 + (ap_uint<10>)(let14 ? 1 : 0));
  ap_uint<23> frac = let16 ? (ap_uint<23>)0 : (ap_uint<23>)let15.range(25, 3);

  return (ap_uint<32>)(((ap_uint<32>)sign << 31) | ((ap_uint<32>)exp << 23) | (ap_uint<32>)frac);
}
