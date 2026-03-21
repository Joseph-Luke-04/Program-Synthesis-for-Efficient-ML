(set-logic BV)

; ===============================================================
; Monolithic MXINT8 multiplier — V2 "structural sketch" grammar.
; Encodes the pipeline stages (multiply → renorm → shift/round →
; saturate → exponent adjust) but leaves implementation choices
; at each stage open for the solver to discover.
; Search space ≈ 25 000 combinations (vs V1 ≈ many millions).
; ===============================================================

(synth-fun mult_mxint_full_product
  ((m1 (_ BitVec 4)) (e1 (_ BitVec 4))
   (m2 (_ BitVec 4)) (e2 (_ BitVec 4))
   (renorm_flag (_ BitVec 1)))
  (_ BitVec 8)

  (
    (Start8 (_ BitVec 8))

    (Prod8 (_ BitVec 8))
    (Abs8 (_ BitVec 8))

    (Thresh8 (_ BitVec 8))
    (Renorm Bool)
    (Renorm1 (_ BitVec 1))
    (Flag1 (_ BitVec 1))
    (DoRenorm Bool)

    (DoRound Bool)
    (RoundK8 (_ BitVec 8))
    (Rounded8 (_ BitVec 8))

    (ShiftAmt8 (_ BitVec 8))
    (MantShifted8 (_ BitVec 8))
    (DoSat Bool)
    (Mant4 (_ BitVec 4))

    (Corr4 (_ BitVec 4))
    (Sum5 (_ BitVec 5))
    (Corr5 (_ BitVec 5))
    (ExpAdj5 (_ BitVec 5))
    (DoClampE Bool)
    (ExpClamped5 (_ BitVec 5))
    (Exp4 (_ BitVec 4))
  )

  (
    (Start8 (_ BitVec 8)
      (
        (concat Exp4 Mant4)
      )
    )

    (Prod8 (_ BitVec 8)
      (
        (bvmul ((_ sign_extend 4) m1) ((_ sign_extend 4) m2))
      )
    )

    (Abs8 (_ BitVec 8)
      (
        (ite (bvslt Prod8 #x00) (bvneg Prod8) Prod8)
      )
    )

    ; threshold choices
    (Thresh8 (_ BitVec 8)
      (
        #x1F  ; 31
        #x20  ; 32
        #x21  ; 33
        #x28  ; 40
        #x2A  ; 42
      )
    )

    (Renorm Bool
      (
        (bvsle Abs8 Thresh8)
        (bvslt Abs8 Thresh8)
      )
    )

    (Renorm1 (_ BitVec 1)
      (
        (ite Renorm #b1 #b0)
      )
    )

    ; allow: use passed flag, recompute, or force on/off
    (Flag1 (_ BitVec 1)
      (
        renorm_flag
        Renorm1
        #b0
        #b1
      )
    )

    (DoRenorm Bool
      (
        (= Flag1 #b1)
      )
    )

    ; optional rounding before shift
    (DoRound Bool
      (
        false
        true
      )
    )

    ; rounding constants: for >>3 use 4, for >>2 use 2 (sign-aware)
    (RoundK8 (_ BitVec 8)
      (
        #x00
        #x02
        #x04
      )
    )

    (Rounded8 (_ BitVec 8)
      (
        Prod8
        (ite DoRound
             (bvadd Prod8 (ite (bvslt Prod8 #x00) (bvneg RoundK8) RoundK8))
             Prod8)
      )
    )

    (ShiftAmt8 (_ BitVec 8)
      (
        (ite DoRenorm #x03 #x02)  ; large prod (renorm) => >>3, small => >>2
      )
    )

    (MantShifted8 (_ BitVec 8)
      (
        (bvashr Rounded8 ShiftAmt8)
      )
    )

    ; optional saturation of mantissa to signed 4-bit range [-8,7]
    (DoSat Bool
      (
        false
        true
      )
    )

    (Mant4 (_ BitVec 4)
      (
        ((_ extract 3 0) MantShifted8)
        (ite DoSat
             (ite (bvsgt MantShifted8 #x07) #b0111
                  (ite (bvslt MantShifted8 #xF8) #b1000
                       ((_ extract 3 0) MantShifted8)))
             ((_ extract 3 0) MantShifted8))
      )
    )

    (Corr4 (_ BitVec 4)
      (
        #b0000
        #b0001
        #b0010
      )
    )

    ; exponent in 5-bit signed, then either wrap or clamp back to 4-bit
    (Sum5 (_ BitVec 5)
      (
        (bvadd ((_ sign_extend 1) e1) ((_ sign_extend 1) e2))
      )
    )

    (Corr5 (_ BitVec 5)
      (
        ((_ sign_extend 1) Corr4)
      )
    )

    (ExpAdj5 (_ BitVec 5)
      (
        (ite DoRenorm Sum5 (bvsub Sum5 Corr5))  ; large prod: no corr; small prod: subtract 1
        Sum5
      )
    )

    (DoClampE Bool
      (
        false
        true
      )
    )

    (ExpClamped5 (_ BitVec 5)
      (
        (ite (bvsgt ExpAdj5 #b00111) #b00111
             (ite (bvslt ExpAdj5 #b11000) #b11000 ExpAdj5))
        ExpAdj5
      )
    )

    (Exp4 (_ BitVec 4)
      (
        ((_ extract 3 0) ExpAdj5)       ; wrap
        ((_ extract 3 0) ExpClamped5)   ; clamp
      )
    )
  )
)
