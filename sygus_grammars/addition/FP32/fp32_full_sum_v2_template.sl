(set-logic BV)

; ===============================================================
; Monolithic FP32 adder — V2 "structural sketch" grammar.
; Encodes the pipeline stages (ordering → alignment → raw sum →
; normalisation → packing) but leaves implementation choices at
; each stage open for the solver to discover.
; Search space ≈ 15 500 combinations (vs V1 ≈ 15 000 000).
; ===============================================================

(define-fun shr24_sat ((x (_ BitVec 24)) (d (_ BitVec 8))) (_ BitVec 24)
  (ite (bvuge d (_ bv24 8))
       (_ bv0 24)
       (bvlshr x ((_ zero_extend 16) d))))

(define-fun norm24_from_raw ((raw (_ BitVec 25))) (_ BitVec 24)
  (ite (= raw (_ bv0 25)) (_ bv0 24)
    (ite (= ((_ extract 24 24) raw) #b1) ((_ extract 24 1) raw)
      (ite (= ((_ extract 23 23) raw) #b1) ((_ extract 23 0) raw)
        (ite (= ((_ extract 22 22) raw) #b1) (concat ((_ extract 22 0) raw) (_ bv0 1))
          (ite (= ((_ extract 21 21) raw) #b1) (concat ((_ extract 21 0) raw) (_ bv0 2))
            (ite (= ((_ extract 20 20) raw) #b1) (concat ((_ extract 20 0) raw) (_ bv0 3))
              (ite (= ((_ extract 19 19) raw) #b1) (concat ((_ extract 19 0) raw) (_ bv0 4))
                (ite (= ((_ extract 18 18) raw) #b1) (concat ((_ extract 18 0) raw) (_ bv0 5))
                  (ite (= ((_ extract 17 17) raw) #b1) (concat ((_ extract 17 0) raw) (_ bv0 6))
                    (ite (= ((_ extract 16 16) raw) #b1) (concat ((_ extract 16 0) raw) (_ bv0 7))
                      (ite (= ((_ extract 15 15) raw) #b1) (concat ((_ extract 15 0) raw) (_ bv0 8))
                        (ite (= ((_ extract 14 14) raw) #b1) (concat ((_ extract 14 0) raw) (_ bv0 9))
                          (ite (= ((_ extract 13 13) raw) #b1) (concat ((_ extract 13 0) raw) (_ bv0 10))
                            (ite (= ((_ extract 12 12) raw) #b1) (concat ((_ extract 12 0) raw) (_ bv0 11))
                              (ite (= ((_ extract 11 11) raw) #b1) (concat ((_ extract 11 0) raw) (_ bv0 12))
                                (ite (= ((_ extract 10 10) raw) #b1) (concat ((_ extract 10 0) raw) (_ bv0 13))
                                  (ite (= ((_ extract 9 9) raw) #b1) (concat ((_ extract 9 0) raw) (_ bv0 14))
                                    (ite (= ((_ extract 8 8) raw) #b1) (concat ((_ extract 8 0) raw) (_ bv0 15))
                                      (ite (= ((_ extract 7 7) raw) #b1) (concat ((_ extract 7 0) raw) (_ bv0 16))
                                        (ite (= ((_ extract 6 6) raw) #b1) (concat ((_ extract 6 0) raw) (_ bv0 17))
                                          (ite (= ((_ extract 5 5) raw) #b1) (concat ((_ extract 5 0) raw) (_ bv0 18))
                                            (ite (= ((_ extract 4 4) raw) #b1) (concat ((_ extract 4 0) raw) (_ bv0 19))
                                              (ite (= ((_ extract 3 3) raw) #b1) (concat ((_ extract 3 0) raw) (_ bv0 20))
                                                (ite (= ((_ extract 2 2) raw) #b1) (concat ((_ extract 2 0) raw) (_ bv0 21))
                                                  (ite (= ((_ extract 1 1) raw) #b1) (concat ((_ extract 1 0) raw) (_ bv0 22))
                                                    (concat ((_ extract 0 0) raw) (_ bv0 23))))))))))))))))))))))))))))

(define-fun exp_delta_from_raw ((raw (_ BitVec 25))) (_ BitVec 8)
  (ite (= raw (_ bv0 25)) (_ bv0 8)
    (ite (= ((_ extract 24 24) raw) #b1) (_ bv1 8)
      (ite (= ((_ extract 23 23) raw) #b1) (_ bv0 8)
        (ite (= ((_ extract 22 22) raw) #b1) (bvneg (_ bv1 8))
          (ite (= ((_ extract 21 21) raw) #b1) (bvneg (_ bv2 8))
            (ite (= ((_ extract 20 20) raw) #b1) (bvneg (_ bv3 8))
              (ite (= ((_ extract 19 19) raw) #b1) (bvneg (_ bv4 8))
                (ite (= ((_ extract 18 18) raw) #b1) (bvneg (_ bv5 8))
                  (ite (= ((_ extract 17 17) raw) #b1) (bvneg (_ bv6 8))
                    (ite (= ((_ extract 16 16) raw) #b1) (bvneg (_ bv7 8))
                      (ite (= ((_ extract 15 15) raw) #b1) (bvneg (_ bv8 8))
                        (ite (= ((_ extract 14 14) raw) #b1) (bvneg (_ bv9 8))
                          (ite (= ((_ extract 13 13) raw) #b1) (bvneg (_ bv10 8))
                            (ite (= ((_ extract 12 12) raw) #b1) (bvneg (_ bv11 8))
                              (ite (= ((_ extract 11 11) raw) #b1) (bvneg (_ bv12 8))
                                (ite (= ((_ extract 10 10) raw) #b1) (bvneg (_ bv13 8))
                                  (ite (= ((_ extract 9 9) raw) #b1) (bvneg (_ bv14 8))
                                    (ite (= ((_ extract 8 8) raw) #b1) (bvneg (_ bv15 8))
                                      (ite (= ((_ extract 7 7) raw) #b1) (bvneg (_ bv16 8))
                                        (ite (= ((_ extract 6 6) raw) #b1) (bvneg (_ bv17 8))
                                          (ite (= ((_ extract 5 5) raw) #b1) (bvneg (_ bv18 8))
                                            (ite (= ((_ extract 4 4) raw) #b1) (bvneg (_ bv19 8))
                                              (ite (= ((_ extract 3 3) raw) #b1) (bvneg (_ bv20 8))
                                                (ite (= ((_ extract 2 2) raw) #b1) (bvneg (_ bv21 8))
                                                  (ite (= ((_ extract 1 1) raw) #b1) (bvneg (_ bv22 8))
                                                    (bvneg (_ bv23 8))))))))))))))))))))))))))))

(synth-fun fp32_sum
  ((s1 (_ BitVec 1)) (e1 (_ BitVec 8)) (m1 (_ BitVec 23))
   (s2 (_ BitVec 1)) (e2 (_ BitVec 8)) (m2 (_ BitVec 23)))
  (_ BitVec 32)
  (
    (Start32      (_ BitVec 32))
    (Cmp          Bool)
    (SameSign     Bool)
    (BigM         (_ BitVec 24))
    (SmallM       (_ BitVec 24))
    (BigE         (_ BitVec 8))
    (Gap8         (_ BitVec 8))
    (AlignedBig   (_ BitVec 24))
    (AlignedSmall (_ BitVec 24))
    (MagGE        Bool)
    (Raw25        (_ BitVec 25))
    (IsZero       Bool)
    (FinalSign    (_ BitVec 1))
    (FinalExp     (_ BitVec 8))
    (FinalMant    (_ BitVec 23))
  )
  (
    (Start32 (_ BitVec 32)
      ((concat FinalSign (concat FinalExp FinalMant))))

    ; --- Stage 1: Ordering ---
    ; Solver must choose strict vs non-strict unsigned comparison.
    (Cmp Bool (
      (bvuge e1 e2)
      (bvugt e1 e2)
    ))

    (SameSign Bool (
      (= s1 s2)
    ))

    ; Solver must figure out which operand is "big" vs "small".
    (BigM (_ BitVec 24) (
      (ite Cmp (concat #b1 m1) (concat #b1 m2))
      (ite Cmp (concat #b1 m2) (concat #b1 m1))
    ))

    (SmallM (_ BitVec 24) (
      (ite Cmp (concat #b1 m2) (concat #b1 m1))
      (ite Cmp (concat #b1 m1) (concat #b1 m2))
    ))

    (BigE (_ BitVec 8) (
      (ite Cmp e1 e2)
      (ite Cmp e2 e1)
    ))

    ; Solver must discover correct gap computation.
    (Gap8 (_ BitVec 8) (
      (ite Cmp (bvsub e1 e2) (bvsub e2 e1))
      (bvsub e1 e2)
      (bvsub e2 e1)
    ))

    ; --- Stage 2: Alignment ---
    ; Does the bigger mantissa stay unshifted, or get shifted too?
    (AlignedBig (_ BitVec 24) (
      BigM
      (shr24_sat BigM Gap8)
    ))

    ; Solver chooses the right alignment strategy for the smaller mantissa.
    (AlignedSmall (_ BitVec 24) (
      (shr24_sat SmallM Gap8)
      (bvlshr SmallM ((_ zero_extend 16) Gap8))
      SmallM
    ))

    ; --- Stage 3: Raw sum ---
    (MagGE Bool (
      (bvuge AlignedBig AlignedSmall)
      (bvugt AlignedBig AlignedSmall)
    ))

    ; Solver must discover: add when same sign, subtract when different
    ; (and which order to subtract in).
    (Raw25 (_ BitVec 25) (
      (ite SameSign
           (bvadd ((_ zero_extend 1) AlignedBig) ((_ zero_extend 1) AlignedSmall))
           (ite MagGE
                (bvsub ((_ zero_extend 1) AlignedBig) ((_ zero_extend 1) AlignedSmall))
                (bvsub ((_ zero_extend 1) AlignedSmall) ((_ zero_extend 1) AlignedBig))))
      (bvadd ((_ zero_extend 1) AlignedBig) ((_ zero_extend 1) AlignedSmall))
      (bvsub ((_ zero_extend 1) AlignedBig) ((_ zero_extend 1) AlignedSmall))
    ))

    ; --- Stage 4: Normalisation & packing ---
    (IsZero Bool (
      (= Raw25 (_ bv0 25))
      (= ((_ extract 23 0) Raw25) (_ bv0 24))
    ))

    ; Solver must discover sign logic for mixed-sign operands.
    (FinalSign (_ BitVec 1) (
      (ite IsZero
           #b0
           (ite SameSign
                s1
                (ite MagGE
                     (ite Cmp s1 s2)
                     (ite Cmp s2 s1))))
      s1
      (ite Cmp s1 s2)
    ))

    ; Solver must discover that exponent needs a normalisation delta.
    (FinalExp (_ BitVec 8) (
      (ite IsZero
           (_ bv0 8)
           (bvadd BigE (exp_delta_from_raw Raw25)))
      (bvadd BigE (exp_delta_from_raw Raw25))
      BigE
    ))

    ; Solver must discover that the mantissa needs leading-one normalisation.
    (FinalMant (_ BitVec 23) (
      (ite IsZero
           (_ bv0 23)
           ((_ extract 22 0) (norm24_from_raw Raw25)))
      ((_ extract 22 0) (norm24_from_raw Raw25))
      ((_ extract 22 0) Raw25)
    ))
  )
)
