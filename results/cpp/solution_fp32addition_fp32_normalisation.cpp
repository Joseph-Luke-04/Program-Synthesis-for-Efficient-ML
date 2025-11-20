#include <ap_int.h>

ap_uint<32> fp32_normaliser(ap_uint<25> raw_sum_mantissa, ap_uint<1> raw_sign, ap_uint<8> target_exponent) {
  if (raw_sum_mantissa == 0) {
    return (ap_uint<32>)((ap_uint<1>)0, (ap_uint<8>)0, (ap_uint<23>)0);
  }
  ap_uint<8> exp = target_exponent;
  ap_uint<24> norm24;
  if (raw_sum_mantissa[24]) { norm24 = raw_sum_mantissa.range(24,1); exp += 1; }
  else if (raw_sum_mantissa[23]) { norm24 = raw_sum_mantissa.range(23,0); }
  else if (raw_sum_mantissa[22]) { norm24 = (ap_uint<24>)raw_sum_mantissa.range(22,0) << 1; exp -= 1; }
  else if (raw_sum_mantissa[21]) { norm24 = (ap_uint<24>)raw_sum_mantissa.range(21,0) << 2; exp -= 2; }
  else if (raw_sum_mantissa[20]) { norm24 = (ap_uint<24>)raw_sum_mantissa.range(20,0) << 3; exp -= 3; }
  else if (raw_sum_mantissa[19]) { norm24 = (ap_uint<24>)raw_sum_mantissa.range(19,0) << 4; exp -= 4; }
  else if (raw_sum_mantissa[18]) { norm24 = (ap_uint<24>)raw_sum_mantissa.range(18,0) << 5; exp -= 5; }
  else if (raw_sum_mantissa[17]) { norm24 = (ap_uint<24>)raw_sum_mantissa.range(17,0) << 6; exp -= 6; }
  else if (raw_sum_mantissa[16]) { norm24 = (ap_uint<24>)raw_sum_mantissa.range(16,0) << 7; exp -= 7; }
  else if (raw_sum_mantissa[15]) { norm24 = (ap_uint<24>)raw_sum_mantissa.range(15,0) << 8; exp -= 8; }
  else if (raw_sum_mantissa[14]) { norm24 = (ap_uint<24>)raw_sum_mantissa.range(14,0) << 9; exp -= 9; }
  else if (raw_sum_mantissa[13]) { norm24 = (ap_uint<24>)raw_sum_mantissa.range(13,0) << 10; exp -= 10; }
  else if (raw_sum_mantissa[12]) { norm24 = (ap_uint<24>)raw_sum_mantissa.range(12,0) << 11; exp -= 11; }
  else if (raw_sum_mantissa[11]) { norm24 = (ap_uint<24>)raw_sum_mantissa.range(11,0) << 12; exp -= 12; }
  else if (raw_sum_mantissa[10]) { norm24 = (ap_uint<24>)raw_sum_mantissa.range(10,0) << 13; exp -= 13; }
  else if (raw_sum_mantissa[9])  { norm24 = (ap_uint<24>)raw_sum_mantissa.range(9,0)  << 14; exp -= 14; }
  else if (raw_sum_mantissa[8])  { norm24 = (ap_uint<24>)raw_sum_mantissa.range(8,0)  << 15; exp -= 15; }
  else if (raw_sum_mantissa[7])  { norm24 = (ap_uint<24>)raw_sum_mantissa.range(7,0)  << 16; exp -= 16; }
  else if (raw_sum_mantissa[6])  { norm24 = (ap_uint<24>)raw_sum_mantissa.range(6,0)  << 17; exp -= 17; }
  else if (raw_sum_mantissa[5])  { norm24 = (ap_uint<24>)raw_sum_mantissa.range(5,0)  << 18; exp -= 18; }
  else if (raw_sum_mantissa[4])  { norm24 = (ap_uint<24>)raw_sum_mantissa.range(4,0)  << 19; exp -= 19; }
  else if (raw_sum_mantissa[3])  { norm24 = (ap_uint<24>)raw_sum_mantissa.range(3,0)  << 20; exp -= 20; }
  else if (raw_sum_mantissa[2])  { norm24 = (ap_uint<24>)raw_sum_mantissa.range(2,0)  << 21; exp -= 21; }
  else if (raw_sum_mantissa[1])  { norm24 = (ap_uint<24>)raw_sum_mantissa.range(1,0)  << 22; exp -= 22; }
  else /* raw_sum_mantissa[0] */  { norm24 = (ap_uint<24>)raw_sum_mantissa.range(0,0)  << 23; exp -= 23; }
  ap_uint<1> sign = raw_sign; // zero already handled
  return (ap_uint<32>)((ap_uint<1>)sign, (ap_uint<8>)exp, (ap_uint<23>)norm24.range(22,0));
}
