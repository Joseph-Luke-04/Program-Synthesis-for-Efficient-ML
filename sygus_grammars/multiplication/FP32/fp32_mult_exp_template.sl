(set-logic BV)

; Exponent for normals-only multiply.
; Expected shape (one valid option in grammar):
;   e_out = ea + eb - 127 + renorm + carry
; where ea/eb are biased exponents (8-bit), renorm/carry are 1-bit.
(synth-fun fp32_mult_exp
  ((ea (_ BitVec 8)) (eb (_ BitVec 8)) (renorm (_ BitVec 1)) (carry (_ BitVec 1)))
  (_ BitVec 8)

  (
    (Start8 (_ BitVec 8))
    (Base8  (_ BitVec 8))
    (Inc8   (_ BitVec 8))
    (Sum8   (_ BitVec 8))
    (W9     (_ BitVec 9))
    (W10    (_ BitVec 10))
    (Cond   Bool)
  )
  (
    (Start8 (_ BitVec 8) (
      Sum8
      Base8
      (bvadd Base8 Inc8)
      (bvsub Base8 Inc8)
      (ite Cond (bvadd Base8 Inc8) Base8)
    ))

    ; Base exponent candidates (includes the standard one, plus nearby variants)
    (Base8 (_ BitVec 8) (
      (bvsub (bvadd ea eb) #b01111111)          ; ea+eb-127 (standard)
      (bvsub (bvadd ea eb) #b01111110)          ; ea+eb-126
      (bvsub (bvadd ea eb) #b10000000)          ; ea+eb-128
      (bvadd ea eb)                             ; no bias sub (alternative)
      (bvsub ea #b01111111)
      (bvsub eb #b01111111)
    ))

    ; Increment candidates from renorm/carry (lets synth explore)
    (Inc8 (_ BitVec 8) (
      #b00000000
      #b00000001
      #b00000010
      ((_ zero_extend 7) renorm)
      ((_ zero_extend 7) carry)
      (bvadd ((_ zero_extend 7) renorm) ((_ zero_extend 7) carry))
      (bvor  ((_ zero_extend 7) renorm) ((_ zero_extend 7) carry))
      (bvand ((_ zero_extend 7) renorm) ((_ zero_extend 7) carry))
    ))

    (Sum8 (_ BitVec 8) (
      (bvadd Base8 Inc8)
      ((_ extract 7 0) W9)
      ((_ extract 7 0) W10)
    ))

    ; Another way: do the math in wider bitwidth then take low 8 bits
    (W9 (_ BitVec 9) (
      (bvsub (bvadd ((_ zero_extend 1) ea) ((_ zero_extend 1) eb)) (_ bv127 9))
      (bvadd (bvsub (bvadd ((_ zero_extend 1) ea) ((_ zero_extend 1) eb)) (_ bv127 9))
             ((_ zero_extend 8) renorm))
      (bvadd (bvsub (bvadd ((_ zero_extend 1) ea) ((_ zero_extend 1) eb)) (_ bv127 9))
             ((_ zero_extend 8) carry))
      (bvadd (bvsub (bvadd ((_ zero_extend 1) ea) ((_ zero_extend 1) eb)) (_ bv127 9))
             (bvadd ((_ zero_extend 8) renorm) ((_ zero_extend 8) carry)))
    ))

    (W10 (_ BitVec 10) (
      (bvsub (bvadd ((_ zero_extend 2) ea) ((_ zero_extend 2) eb)) (_ bv127 10))
      (bvadd (bvsub (bvadd ((_ zero_extend 2) ea) ((_ zero_extend 2) eb)) (_ bv127 10))
             ((_ zero_extend 9) renorm))
      (bvadd (bvsub (bvadd ((_ zero_extend 2) ea) ((_ zero_extend 2) eb)) (_ bv127 10))
             ((_ zero_extend 9) carry))
    ))

    (Cond Bool (
      (= renorm #b1)
      (= carry #b1)
      (and (= renorm #b1) (= carry #b1))
      (or  (= renorm #b1) (= carry #b1))
      (bvugt ea eb)
      (bvugt eb ea)
    ))
  )
)