(set-logic BV)

; Monolithic MXINT8 adder — V2 "structural sketch" grammar.
; Encodes the pipeline stages (ordering → alignment → raw sum →
; normalisation → packing) but leaves implementation choices at
; each stage open for the solver to discover.
; Search space ≈ 27 000 combinations (vs V1 ≈ many millions).

(define-fun norm_shifted5 ((raw (_ BitVec 5))) (_ BitVec 5)
  (let ((abs5 (ite (bvslt raw #b00000) (bvneg raw) raw)))
    (ite (= raw #b00000)
         raw
         (ite (= ((_ extract 4 4) abs5) #b1)
              (bvashr raw #b00010)
              (ite (= ((_ extract 3 3) abs5) #b1)
                   (bvashr raw #b00001)
                   (ite (= ((_ extract 2 2) abs5) #b1)
                        raw
                        (ite (= ((_ extract 1 1) abs5) #b1)
                             (bvshl raw #b00001)
                             (bvshl raw #b00010))))))))

(define-fun exp_delta5_from_raw ((raw (_ BitVec 5))) (_ BitVec 5)
  (let ((abs5 (ite (bvslt raw #b00000) (bvneg raw) raw)))
    (ite (= raw #b00000)
         #b00000
         (ite (= ((_ extract 4 4) abs5) #b1)
              #b00010
              (ite (= ((_ extract 3 3) abs5) #b1)
                   #b00001
                   (ite (= ((_ extract 2 2) abs5) #b1)
                        #b00000
                        (ite (= ((_ extract 1 1) abs5) #b1)
                             #b11111
                             #b11110)))))))

(define-fun sat_mant4 ((shifted (_ BitVec 5))) (_ BitVec 4)
  (ite (bvsgt shifted #b00111)
       #b0111
       (ite (bvslt shifted #b11000)
            #b1000
            ((_ extract 3 0) shifted))))

(define-fun clamp_exp4 ((exp_adj (_ BitVec 5))) (_ BitVec 4)
  ((_ extract 3 0)
   (ite (bvsgt exp_adj #b00111)
        #b00111
        (ite (bvslt exp_adj #b11000) #b11000 exp_adj))))

(synth-fun add_full_sum
  ((m1 (_ BitVec 4)) (e1 (_ BitVec 4)) (m2 (_ BitVec 4)) (e2 (_ BitVec 4)))
  (_ BitVec 8)
  (
    (Start8        (_ BitVec 8))
    (Cmp           Bool)
    (BigM          (_ BitVec 4))
    (SmallM        (_ BitVec 4))
    (BigE          (_ BitVec 4))
    (SmallE        (_ BitVec 4))
    (Gap5          (_ BitVec 5))
    (Gap4          (_ BitVec 4))
    (Bias4         (_ BitVec 4))
    (SignedBias5   (_ BitVec 5))
    (RoundedSmall5 (_ BitVec 5))
    (AlignedS      (_ BitVec 4))
    (Raw5          (_ BitVec 5))
    (IsZero        Bool)
    (ExpAdj5       (_ BitVec 5))
    (FinalMant4    (_ BitVec 4))
    (FinalExp4     (_ BitVec 4))
  )
  (
    (Start8 (_ BitVec 8)
      ((concat FinalExp4 FinalMant4)))

    ; --- Stage 1: Ordering ---
    ; Solver must choose strict vs non-strict signed comparison.
    (Cmp Bool (
      (bvsge e1 e2)
      (bvsgt e1 e2)
    ))

    ; Solver must figure out which operand is "big" vs "small".
    (BigM (_ BitVec 4) (
      (ite Cmp m1 m2)
      (ite Cmp m2 m1)
    ))

    (SmallM (_ BitVec 4) (
      (ite Cmp m2 m1)
      (ite Cmp m1 m2)
    ))

    (BigE (_ BitVec 4) (
      (ite Cmp e1 e2)
      (ite Cmp e2 e1)
    ))

    (SmallE (_ BitVec 4) (
      (ite Cmp e2 e1)
      (ite Cmp e1 e2)
    ))

    (Gap5 (_ BitVec 5) (
      (bvsub ((_ sign_extend 1) BigE)
             ((_ sign_extend 1) SmallE))
    ))

    (Gap4 (_ BitVec 4) (
      ((_ extract 3 0) Gap5)
    ))

    ; --- Stage 2: Alignment ---
    ; Solver must discover the rounding-bias table, or that no bias is needed.
    (Bias4 (_ BitVec 4) (
      (ite (= Gap4 #b0001)
           #b0001
           (ite (= Gap4 #b0010)
                #b0010
                (ite (= Gap4 #b0011) #b0100 #b0000)))
      Gap4
      #b0000
    ))

    ; Solver must discover sign-aware biasing.
    (SignedBias5 (_ BitVec 5) (
      ((_ sign_extend 1)
       (ite (bvslt SmallM #b0000)
            (bvneg Bias4)
            Bias4))
      ((_ sign_extend 1) Bias4)
    ))

    ; Solver chooses whether to apply rounding before the shift.
    (RoundedSmall5 (_ BitVec 5) (
      (bvadd ((_ sign_extend 1) SmallM) SignedBias5)
      ((_ sign_extend 1) SmallM)
    ))

    ; Solver must discover the alignment shift with saturation.
    (AlignedS (_ BitVec 4) (
      (ite (bvsge Gap5 #b00100)
           #b0000
           (ite (= Gap5 #b00000)
                SmallM
                ((_ extract 3 0) (bvashr RoundedSmall5 Gap5))))
      ((_ extract 3 0) (bvashr RoundedSmall5 Gap5))
      SmallM
    ))

    ; --- Stage 3: Raw sum ---
    ; Solver must discover that aligned values should be added, not raw inputs.
    (Raw5 (_ BitVec 5) (
      (bvadd ((_ sign_extend 1) BigM) ((_ sign_extend 1) AlignedS))
      (bvadd ((_ sign_extend 1) BigM) ((_ sign_extend 1) SmallM))
    ))

    ; --- Stage 4: Normalisation & packing ---
    (IsZero Bool (
      (= Raw5 #b00000)
      (= ((_ extract 3 0) Raw5) #b0000)
    ))

    ; Solver must discover that the exponent needs a normalisation delta.
    (ExpAdj5 (_ BitVec 5) (
      (bvadd ((_ sign_extend 1) BigE) (exp_delta5_from_raw Raw5))
      ((_ sign_extend 1) BigE)
    ))

    ; Solver must discover that the mantissa needs normalisation and saturation.
    (FinalMant4 (_ BitVec 4) (
      (ite IsZero
           #b0000
           (sat_mant4 (norm_shifted5 Raw5)))
      (ite IsZero
           #b0000
           (sat_mant4 Raw5))
      ((_ extract 3 0) Raw5)
    ))

    ; Solver must discover that the exponent needs clamping.
    (FinalExp4 (_ BitVec 4) (
      (ite IsZero
           #b0000
           (clamp_exp4 ExpAdj5))
      ((_ extract 3 0) ExpAdj5)
    ))
  )
)
