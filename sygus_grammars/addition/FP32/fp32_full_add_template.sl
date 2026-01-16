(set-logic BV)

; Naive full FP32 adder: 
;   inputs  : s1(1), e1(8), m1(23), s2(1), e2(8), m2(23)
;   output  : 32-bit IEEE754 (concat sign (concat exponent mantissa))

(synth-fun naive_fp32_add
  ((s1 (_ BitVec 1)) (e1 (_ BitVec 8)) (m1 (_ BitVec 23))
   (s2 (_ BitVec 1)) (e2 (_ BitVec 8)) (m2 (_ BitVec 23)))
  (_ BitVec 32)

  ;; nonterminals (order matters for cvc5)
  ((Start32 (_ BitVec 32)) (B Bool)
   (BV24   (_ BitVec 24))  (BV23 (_ BitVec 23))
   (BV8    (_ BitVec 8))   (BV1  (_ BitVec 1)))

  (
    ;; 1) Start32
    (Start32 (_ BitVec 32) (
      (concat BV8 BV24)
      (concat BV1 (concat BV8 BV23))
      ((_ zero_extend 8)  BV24)
      ((_ zero_extend 24) BV8)
      ((_ zero_extend 31) BV1)
      ((_ zero_extend 9)  BV23)
      (bvadd Start32 Start32)
      (bvsub Start32 Start32)
      (bvor  Start32 Start32)
      (bvand Start32 Start32)
      (bvxor Start32 Start32)
      (bvshl Start32 Start32)
      (bvlshr Start32 Start32)
      (bvashr Start32 Start32)
      (ite B Start32 Start32)
    ))

    ;; 2 - B
    (B Bool (
      (bvuge BV8 BV8)  (bvugt BV8 BV8)  (bvult BV8 BV8)
      (bvslt BV8 BV8)  (bvsle BV8 BV8)
      (bvuge BV24 BV24) (bvugt BV24 BV24) (bvult BV24 BV24)
      (bvslt BV24 BV24) (bvsle BV24 BV24)
      (= BV24 BV24) (= BV23 BV23) (= BV8 BV8) (= BV1 BV1)
      (and B B) (or B B) (not B)
      (= BV1 #b1)                ; cast bv1->Bool
    ))

    ;; 3 - BV24
    (BV24 (_ BitVec 24) (
      (concat BV1 BV23)
      ((_ zero_extend 16) BV8)
      ((_ zero_extend 1)  BV23)
      ((_ extract 23 0) Start32)
      (bvadd BV24 BV24)
      (bvsub BV24 BV24)
      (bvor  BV24 BV24)
      (bvand BV24 BV24)
      (bvxor BV24 BV24)
      (bvshl BV24 BV24)
      (bvlshr BV24 BV24)
      (ite B BV24 BV24)
    ))

    ;; 4 - BV23
    (BV23 (_ BitVec 23) (
      m1 m2
      ((_ extract 22 0) BV24)
      (bvadd BV23 BV23)
      (bvsub BV23 BV23)
      (bvor  BV23 BV23)
      (bvand BV23 BV23)
      (bvshl BV23 BV23)
      (bvlshr BV23 BV23)
      (ite B BV23 BV23)
    ))

    ;; 5 - BV8
    (BV8 (_ BitVec 8) (
      e1 e2
      ((_ extract 31 24) Start32)
      (bvadd BV8 BV8)
      (bvsub BV8 BV8)
      (bvor  BV8 BV8)
      (bvand BV8 BV8)
      (ite B BV8 BV8)
    ))

    ;; 6 - BV1
    (BV1 (_ BitVec 1) (
      s1 s2
      #b0 #b1
      ((_ extract 31 31) Start32)
      (ite B #b1 #b0)
      ((_ extract 0 0) BV8)
    ))
  )
)
