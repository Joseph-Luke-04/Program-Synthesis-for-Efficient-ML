(set-logic BV)

; Monolithic MXINT8 multiplier baseline grammar (V1).
; Deliberately broader than the guided combined grammar:
;   - wider renorm thresholds,
;   - wider rounding and shift options,
;   - weaker exponent correction/clamp choices.

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

    (Thresh8 (_ BitVec 8)
      (
        #x18
        #x1F
        #x20
        #x21
        #x24
        #x28
        #x2A
        #x30
        #x40
      )
    )

    (Renorm Bool
      (
        (bvsle Abs8 Thresh8)
        (bvslt Abs8 Thresh8)
        (bvsge Abs8 Thresh8)
        (bvsgt Abs8 Thresh8)
      )
    )

    (Renorm1 (_ BitVec 1)
      (
        (ite Renorm #b1 #b0)
      )
    )

    (Flag1 (_ BitVec 1)
      (
        renorm_flag
        Renorm1
        (bvxor renorm_flag Renorm1)
        #b0
        #b1
      )
    )

    (DoRenorm Bool
      (
        (= Flag1 #b1)
      )
    )

    (DoRound Bool
      (
        false
        true
      )
    )

    (RoundK8 (_ BitVec 8)
      (
        #x00
        #x01
        #x02
        #x03
        #x04
        #x08
      )
    )

    (Rounded8 (_ BitVec 8)
      (
        Prod8
        (ite DoRound
             (bvadd Prod8 (ite (bvslt Prod8 #x00) (bvneg RoundK8) RoundK8))
             Prod8)
        (bvadd Prod8 (ite (bvslt Prod8 #x00) (bvneg RoundK8) RoundK8))
        (bvsub Prod8 RoundK8)
      )
    )

    (ShiftAmt8 (_ BitVec 8)
      (
        (ite DoRenorm #x03 #x02)  ; large prod => >>3, small => >>2
        #x01
        #x02
        #x03
        #x04
      )
    )

    (MantShifted8 (_ BitVec 8)
      (
        (bvashr Rounded8 ShiftAmt8)
        (bvashr Prod8 ShiftAmt8)
        Rounded8
        Prod8
      )
    )

    (DoSat Bool
      (
        false
        true
      )
    )

    (Mant4 (_ BitVec 4)
      (
        ((_ extract 3 0) MantShifted8)
        ((_ extract 3 0) Rounded8)
        ((_ extract 3 0) Prod8)
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
        #b0011
      )
    )

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
        (ite DoRenorm (bvadd Sum5 Corr5) Sum5)
        (bvsub Sum5 Corr5)
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
        ((_ extract 3 0) ExpAdj5)
        ((_ extract 3 0) ExpClamped5)
        e1
        e2
      )
    )
  )
)
