#include <ap_int.h>

ap_uint<4> mult_mxint_mant(ap_uint<4> m1, ap_uint<4> m2) {
  {
    if ((signed char)((signed char)((unsigned char)(signed char)(ap_int<4>)m1 * (unsigned char)(signed char)(ap_int<4>)m2) < (signed char)0 ? -((unsigned char)(signed char)(ap_int<4>)m1 * (unsigned char)(signed char)(ap_int<4>)m2) : (unsigned char)(signed char)(ap_int<4>)m1 * (unsigned char)(signed char)(ap_int<4>)m2) <= (signed char)32) { return (unsigned char)((signed char)((unsigned char)(signed char)(ap_int<4>)m1 * (unsigned char)(signed char)(ap_int<4>)m2 << 1) >> (signed char)3); }
    else { return (ap_uint<4>((unsigned char)((signed char)((unsigned char)(signed char)(ap_int<4>)m1 * (unsigned char)(signed char)(ap_int<4>)m2) >> (signed char)3))); }
}

}
