(set-logic BV)

; Pipeline for MXINT8 addition that reuses the previously synthesised stages:
;   1) align_mantissas/select_exponent   (alignment)
;   2) add_raw                           (raw sum + target exp)
;   3) normalise_addition                (normalisation)

(synth-fun add_full_sum
  ((m1 (_ BitVec 4)) (e1 (_ BitVec 4)) (m2 (_ BitVec 4)) (e2 (_ BitVec 4)))
  (_ BitVec 8)

  (
    (Start8 (_ BitVec 8))
    (Raw9   (_ BitVec 9))
    (Raw5   (_ BitVec 5))
    (Texp   (_ BitVec 4))
  )

  (
    ; Final output: normalise the raw sum using the target exponent.
    (Start8 (_ BitVec 8) (
      (normalise_addition Raw5 Texp)
    ))

    ; Stage outputs
    (Raw9 (_ BitVec 9) (
      (add_raw m1 e1 m2 e2)
    ))
    (Raw5 (_ BitVec 5) (
      ((_ extract 8 4) Raw9)
    ))
    (Texp (_ BitVec 4) (
      ((_ extract 3 0) Raw9)
    ))
  )
)
