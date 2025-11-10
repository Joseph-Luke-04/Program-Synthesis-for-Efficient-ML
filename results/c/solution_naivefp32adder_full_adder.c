ap_uint<4> max2(ap_uint<4> x, ap_uint<4> y) {
  return y > x ? (ap_uint<4>)  y : (ap_uint<4>)  x;
}
