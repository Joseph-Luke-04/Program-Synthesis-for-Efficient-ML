(set-logic BV)

; renorm is set to 1 if the 48-bit mantissa product is >= 2.0 in fixed-point,
; i.e. MSB (bit 47) is 1 for product of 24-bit mantissas.
(synth-fun fp32_mult_renorm
  ((Ma (_ BitVec 24)) (Mb (_ BitVec 24)))
  (_ BitVec 1)

  (
    (Start1 (_ BitVec 1))
    (P48    (_ BitVec 48))
    (B1     (_ BitVec 1))
    (Cond   Bool)
  )
  (
    (Start1 (_ BitVec 1) (
      B1
      #b0
      #b1
      (ite Cond #b1 #b0)
    ))

    (P48 (_ BitVec 48) (
      (bvmul ((_ zero_extend 24) Ma) ((_ zero_extend 24) Mb))
      (bvlshr (bvmul ((_ zero_extend 24) Ma) ((_ zero_extend 24) Mb)) (_ bv1 48))
      (bvshl  (bvmul ((_ zero_extend 24) Ma) ((_ zero_extend 24) Mb)) (_ bv1 48))
    ))

    (B1 (_ BitVec 1) (
      ((_ extract 47 47) P48)   ; the “correct” renorm bit
      ((_ extract 46 46) P48)
      ((_ extract 45 45) P48)
    ))

    (Cond Bool (
      (= B1 #b1)
      (= ((_ extract 47 47) P48) #b1)
      (bvugt P48 (_ bv0 48))
      (bvuge P48 (_ bv0 48))
    ))
  )
)