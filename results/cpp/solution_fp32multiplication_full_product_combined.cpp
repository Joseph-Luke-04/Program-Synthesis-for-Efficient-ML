#include <ap_int.h>

#ifndef FP32_MUL_EFFECTIVE_MANT_BITS
#define FP32_MUL_EFFECTIVE_MANT_BITS 24
#endif
#if FP32_MUL_EFFECTIVE_MANT_BITS < 1
#error "FP32_MUL_EFFECTIVE_MANT_BITS must be >= 1"
#endif
#if FP32_MUL_EFFECTIVE_MANT_BITS > 24
#error "FP32_MUL_EFFECTIVE_MANT_BITS must be <= 24"
#endif

ap_uint<32> fp32_full_mul(ap_uint<32> a, ap_uint<32> b) {
  ap_uint<24> Ma = (ap_uint<24>)(((ap_uint<24>)1 << 23) | (ap_uint<23>)a.range(22, 0));
  ap_uint<24> Mb = (ap_uint<24>)(((ap_uint<24>)1 << 23) | (ap_uint<23>)b.range(22, 0));
  const int drop = 24 - FP32_MUL_EFFECTIVE_MANT_BITS;
  ap_uint<FP32_MUL_EFFECTIVE_MANT_BITS> Ma_eff =
      (ap_uint<FP32_MUL_EFFECTIVE_MANT_BITS>)(Ma >> drop);
  ap_uint<FP32_MUL_EFFECTIVE_MANT_BITS> Mb_eff =
      (ap_uint<FP32_MUL_EFFECTIVE_MANT_BITS>)(Mb >> drop);
  ap_uint<2 * FP32_MUL_EFFECTIVE_MANT_BITS> prod_eff =
      (ap_uint<2 * FP32_MUL_EFFECTIVE_MANT_BITS>)Ma_eff * (ap_uint<2 * FP32_MUL_EFFECTIVE_MANT_BITS>)Mb_eff;
  ap_uint<48> prod = ((ap_uint<48>)prod_eff) << (2 * drop);

  ap_uint<1> renorm = (ap_uint<1>)prod[47];
  ap_uint<48> pn = (renorm == 1) ? (prod >> 1) : prod;

  ap_uint<24> top = (ap_uint<24>)pn.range(46, 23);
  ap_uint<1> round = (ap_uint<1>)pn[22];
  ap_uint<25> rounded25 = (ap_uint<25>)(((ap_uint<25>)top) + (ap_uint<25>)round);
  ap_uint<23> frac = (ap_uint<23>)rounded25.range(22, 0);

  ap_uint<10> exp10 = (ap_uint<10>)a.range(30, 23) + (ap_uint<10>)b.range(30, 23);
  exp10 = exp10 - (ap_uint<10>)127;
  exp10 = exp10 + (ap_uint<10>)renorm;
  ap_uint<8> exp = (ap_uint<8>)exp10;

  ap_uint<1> sign = (ap_uint<1>)(a[31] ^ b[31]);

  return (ap_uint<32>)(((ap_uint<32>)sign << 31) | ((ap_uint<32>)exp << 23) | (ap_uint<32>)frac);
}
