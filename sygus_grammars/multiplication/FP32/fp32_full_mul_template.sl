(set-logic BV)

; naive_fp32_mul:
;  inputs:  s1:1, e1:8, m1:23, s2:1, e2:8, m2:23
;  output:  32-bit IEEE-754 single (sign | exponent | mantissa)

(synth-fun naive_fp32_mul
  ((s1 (_ BitVec 1)) (e1 (_ BitVec 8)) (m1 (_ BitVec 23))
   (s2 (_ BitVec 1)) (e2 (_ BitVec 8)) (m2 (_ BitVec 23)))
  (_ BitVec 32)

  ; -------- Nonterminals --------
  ((Start (_ BitVec 32))
   (B32   (_ BitVec 32))
   (B48   (_ BitVec 48))
   (B24   (_ BitVec 24))
   (B23   (_ BitVec 23))
   (B8    (_ BitVec 8))
   (B1    (_ BitVec 1))
   (P     Bool))

  ; -------- Productions --------
  (
    ; Top-level
    (Start (_ BitVec 32) (B32))

    ; 32-bit builder / general ops (keep compact)
    (B32 (_ BitVec 32) (
      ((_ zero_extend 24) B8)
      ((_ zero_extend 8)  B24)
      ((_ sign_extend 31) B1)
      (bvadd B32 B32)
      (bvsub B32 B32)
      (bvand B32 B32)
      (bvor  B32 B32)
      (bvxor B32 B32)
      (bvshl B32 B32)
      (bvlshr B32 B32)
      (bvashr B32 B32)
      (ite P B32 B32)
      (concat B1 (concat B8 B23))      ; assemble sign | exp | mant
      ((_ extract 31 0) B48)           ; take lower 32 if needed
    ))

    ; 48-bit intermediate (product + simple ops)
    (B48 (_ BitVec 48) (
      (concat B24 B24)
      (bvadd B48 B48)
      (bvsub B48 B48)
      (bvand B48 B48)
      (bvor  B48 B48)
      (bvxor B48 B48)
      (bvshl B48 B48)
      (bvlshr B48 B48)
      (ite P B48 B48)
      ; 24x24 -> 48 by zero-extending both operands
      (bvmul ((_ zero_extend 24) B24) ((_ zero_extend 24) B24))
    ))

    ; 24-bit significand (hidden-bit + mantissa, or slices of product)
    (B24 (_ BitVec 24) (
      (concat B1 B23)                 ; hidden-bit :: mantissa
      ((_ extract 47 24) B48)         ; top 24 bits (no shift)
      ((_ extract 46 23) B48)         ; top 24 bits of (product >> 1)
      (bvadd B24 B24)
      (bvsub B24 B24)
      (bvand B24 B24)
      (bvor  B24 B24)
      (bvxor B24 B24)
      (bvshl B24 B24)
      (bvlshr B24 B24)
      (ite P B24 B24)
    ))

    ; 23-bit mantissa source
    (B23 (_ BitVec 23) (
      m1
      m2
      ((_ extract 22 0) B24)         ; drop hidden bit after normalization
    ))

    ; 8-bit exponent arithmetic (sum, bias adjust, +1 on carry)
    (B8 (_ BitVec 8) (
      e1
      e2
      #x00 #xff #x7f #x01            ; 0, 255, bias=127, 1
      (bvadd B8 B8)
      (bvsub B8 B8)
      (bvand B8 B8)
      (bvor  B8 B8)
      (ite P B8 B8)
    ))

    ; 1-bit sign / hidden flags
    (B1 (_ BitVec 1) (
      s1
      s2
      #b0
      #b1
      (bvxor B1 B1)                   ; sign = s1 XOR s2
      (ite P B1 B1)
      ; hidden bit: (e != 0) ? 1 : 0
      (ite (= B8 #x00) #b0 #b1)
    ))

    ; Boolean predicates, including “is top bit set?” checks
    (P Bool (
      (and P P)
      (or  P P)
      (not P)
      (= B1 B1) (= B8 B8) (= B23 B23) (= B24 B24) (= B48 B48) (= B32 B32)
      (bvult B8 B8) (bvugt B8 B8) (bvslt B8 B8) (bvsle B8 B8)
      (bvult B24 B24) (bvugt B24 B24)
      (= B1 #b1)
      ; normalization condition(s) from product
      (= ((_ extract 47 47) B48) #b1)
      (= ((_ extract 46 46) B48) #b1)
    ))
  )
)
