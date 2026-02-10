#include <ap_int.h>

ap_uint<8> add_full_sum(ap_uint<4> m1, ap_uint<4> e1, ap_uint<4> m2, ap_uint<4> e2) {
  // Direct structured form of the synthesized BV expression from full_sum_combined.
  bool swap = ((ap_int<4>)e1 >= (ap_int<4>)e2);
  ap_int<4> mbig = (ap_int<4>)(swap ? m1 : m2);
  ap_int<4> msmall = (ap_int<4>)(swap ? m2 : m1);
  ap_uint<4> ebig = (ap_uint<4>)(swap ? e1 : e2);
  ap_uint<4> esmall = (ap_uint<4>)(swap ? e2 : e1);

  ap_uint<4> diff4 = (ap_uint<4>)(ebig - esmall);
  ap_uint<4> bias4 =
      (diff4 == (ap_uint<4>)1) ? (ap_uint<4>)1 :
      (diff4 == (ap_uint<4>)2) ? (ap_uint<4>)2 :
      (diff4 == (ap_uint<4>)3) ? (ap_uint<4>)4 : (ap_uint<4>)0;

  ap_int<4> bias_signed4 = ((ap_int<4>)msmall < 0) ? (ap_int<4>)(-(ap_int<4>)bias4) : (ap_int<4>)bias4;
  ap_int<5> sum_small5 = (ap_int<5>)msmall + (ap_int<5>)bias_signed4;

  ap_int<4> aligned_small4;
  if (diff4 >= (ap_uint<4>)4) {
    aligned_small4 = (ap_int<4>)0;
  } else if (diff4 == (ap_uint<4>)0) {
    aligned_small4 = msmall;
  } else if (diff4 == (ap_uint<4>)1) {
    aligned_small4 = (ap_int<4>)(sum_small5 >> 1);
  } else if (diff4 == (ap_uint<4>)2) {
    aligned_small4 = (ap_int<4>)(sum_small5 >> 2);
  } else if (diff4 == (ap_uint<4>)3) {
    aligned_small4 = (ap_int<4>)(sum_small5 >> 3);
  } else {
    aligned_small4 = (ap_int<4>)0;
  }

  ap_int<5> raw5 = (ap_int<5>)mbig + (ap_int<5>)aligned_small4;
  ap_int<5> abs5 = (raw5 < 0) ? (ap_int<5>)(-raw5) : raw5;
  bool is_zero = (raw5 == 0);

  bool is_b4 = (abs5[4] == 1);
  bool is_b3 = (abs5[3] == 1);
  bool is_b2 = (abs5[2] == 1);
  bool is_b1 = (abs5[1] == 1);

  ap_int<5> shifted5 = is_zero ? raw5 :
                      (is_b4 ? (ap_int<5>)(raw5 >> 2) :
                      (is_b3 ? (ap_int<5>)(raw5 >> 1) :
                      (is_b2 ? raw5 :
                      (is_b1 ? (ap_int<5>)(raw5 << 1) : (ap_int<5>)(raw5 << 2)))));

  ap_int<5> adj5 = is_zero ? (ap_int<5>)0 :
                  (is_b4 ? (ap_int<5>)2 :
                  (is_b3 ? (ap_int<5>)1 :
                  (is_b2 ? (ap_int<5>)0 :
                  (is_b1 ? (ap_int<5>)-1 : (ap_int<5>)-2))));

  ap_int<5> exp_adj5 = (ap_int<5>)((ap_int<4>)ebig) + adj5;
  ap_int<5> exp_clamp5 = (exp_adj5 > (ap_int<5>)7) ? (ap_int<5>)7 :
                         (exp_adj5 < (ap_int<5>)-8) ? (ap_int<5>)-8 : exp_adj5;

  ap_int<4> mant4 = is_zero ? (ap_int<4>)0 :
                   (shifted5 > (ap_int<5>)7) ? (ap_int<4>)7 :
                   (shifted5 < (ap_int<5>)-8) ? (ap_int<4>)-8 :
                   (ap_int<4>)shifted5;

  ap_uint<4> exp4 = is_zero ? (ap_uint<4>)0 : (ap_uint<4>)exp_clamp5;
  ap_uint<4> mant_u = (ap_uint<4>)mant4;
  return (ap_uint<8>)((((ap_uint<8>)mant_u) << 4) | (ap_uint<8>)exp4);
}
