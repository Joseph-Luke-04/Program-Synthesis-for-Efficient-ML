(set-logic BV)

; ===============================================================
; MXINT8 addition normalisation — "in-between" structural sketch.
; Normalises the 5-bit raw sum back to signed 4-bit mantissa
; and adjusts the exponent accordingly.
; Search space ≈ 270 combinations.
; ShiftAmt5(3) × Shifted5(3) × Mant4(5) × ExpDelta5(2) × Exp4(3) = 270
; ===============================================================

(synth-fun normalise_addition
  ((raw_sum (_ BitVec 5)) (target_exp (_ BitVec 4)))
  (_ BitVec 8)
  (
    (Start8     (_ BitVec 8))
    (Abs5       (_ BitVec 5))
    (IsZero     Bool)
    (IsB4       Bool)
    (IsB3       Bool)
    (IsB2       Bool)
    (IsB1       Bool)
    (ShiftAmt5  (_ BitVec 5))
    (Shifted5   (_ BitVec 5))
    (Mant4      (_ BitVec 4))
    (ExpDelta5  (_ BitVec 5))
    (ExpAdj5    (_ BitVec 5))
    (Exp4       (_ BitVec 4))
  )
  (
    (Start8 (_ BitVec 8) (
      (concat Exp4 Mant4)
    ))

    ; --- Helpers: absolute value and MSB detection ---
    (Abs5 (_ BitVec 5) (
      (ite (bvslt raw_sum #b00000) (bvneg raw_sum) raw_sum)
    ))

    (IsZero Bool ( (= raw_sum #b00000) ))
    (IsB4 Bool ( (= ((_ extract 4 4) Abs5) #b1) ))
    (IsB3 Bool ( (= ((_ extract 3 3) Abs5) #b1) ))
    (IsB2 Bool ( (= ((_ extract 2 2) Abs5) #b1) ))
    (IsB1 Bool ( (= ((_ extract 1 1) Abs5) #b1) ))

    ; --- Stage 1: Compute shift amount from leading-one position ---
    ; Different calibrations for how the LZC maps to shift amounts.
    (ShiftAmt5 (_ BitVec 5) (
      (ite IsZero #b00000
           (ite IsB4 #b00010
                (ite IsB3 #b00001
                     (ite IsB2 #b00000
                          (ite IsB1 #b11111 #b11110)))))
      (ite IsZero #b00000
           (ite IsB4 #b00001
                (ite IsB3 #b00000
                     (ite IsB2 #b11111
                          (ite IsB1 #b11110 #b11101)))))
      (ite IsZero #b00000
           (ite IsB4 #b00010
                (ite IsB3 #b00001
                     (ite IsB2 #b00000
                          (ite IsB1 #b00000 #b00000)))))
    ))

    ; --- Stage 2: Shift raw sum to normalise ---
    (Shifted5 (_ BitVec 5) (
      (ite (bvsge ShiftAmt5 #b00000)
           (bvashr raw_sum ShiftAmt5)
           (bvshl raw_sum (bvneg ShiftAmt5)))
      (bvashr raw_sum ShiftAmt5)
      (ite (bvsge ShiftAmt5 #b00000)
           (bvlshr raw_sum ShiftAmt5)
           (bvshl raw_sum (bvneg ShiftAmt5)))
    ))

    ; --- Stage 3: Extract mantissa ---
    (Mant4 (_ BitVec 4) (
      (ite IsZero #b0000
           (ite (bvsgt Shifted5 #b00111) #b0111
                (ite (bvslt Shifted5 #b11000) #b1000
                     ((_ extract 3 0) Shifted5))))
      (ite IsZero #b0000 ((_ extract 3 0) Shifted5))
      ((_ extract 3 0) Shifted5)
      ((_ extract 3 0) raw_sum)
      (ite IsZero #b0000 ((_ extract 4 1) Shifted5))
    ))

    ; --- Stage 4: Exponent adjustment ---
    (ExpDelta5 (_ BitVec 5) (
      ShiftAmt5
      (ite IsZero #b00000 ShiftAmt5)
    ))

    (ExpAdj5 (_ BitVec 5) (
      (bvadd ((_ sign_extend 1) target_exp) ExpDelta5)
    ))

    ; --- Stage 5: Clamp exponent to signed 4-bit range ---
    (Exp4 (_ BitVec 4) (
      (ite IsZero #b0000
           ((_ extract 3 0)
            (ite (bvsgt ExpAdj5 #b00111) #b00111
                 (ite (bvslt ExpAdj5 #b11000) #b11000 ExpAdj5))))
      (ite IsZero #b0000 ((_ extract 3 0) ExpAdj5))
      ((_ extract 3 0) ExpAdj5)
    ))
  )
)

(declare-var raw_sum (_ BitVec 5))
(declare-var target_exp (_ BitVec 4))
