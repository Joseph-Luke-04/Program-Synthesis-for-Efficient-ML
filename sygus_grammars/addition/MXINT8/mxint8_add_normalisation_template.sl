(set-logic BV)

(synth-fun normalise_addition
  ((raw_sum (_ BitVec 5)) (target_exp (_ BitVec 4)))
  (_ BitVec 8)

  (
    (Start8        (_ BitVec 8))
    (Mant4         (_ BitVec 4))
    (Exp4          (_ BitVec 4))
    (Shifted5      (_ BitVec 5))
    (ExpAdj5       (_ BitVec 5))
    (ExpClamp5     (_ BitVec 5))
    (Abs5          (_ BitVec 5))
    (IsZero        Bool)
    (IsB4          Bool)
    (IsB3          Bool)
    (IsB2          Bool)
    (IsB1          Bool)
  )

  (
    (Start8 (_ BitVec 8) (
      (concat Mant4 Exp4)
    ))

    ; IMPORTANT: extract only from Shifted5 (a symbol), not from an expression
    ; Saturate to signed 4-bit range after normalization.
    (Mant4 (_ BitVec 4) (
      (ite IsZero
           #b0000
           (ite (bvsgt Shifted5 #b00111) #b0111
                (ite (bvslt Shifted5 #b11000) #b1000
                     ((_ extract 3 0) Shifted5))))
    ))

    (Exp4 (_ BitVec 4) (
      ((_ extract 3 0) ExpClamp5)
    ))

    (Shifted5 (_ BitVec 5) (
      (ite IsZero
           raw_sum
           (ite IsB4
                (bvashr
                  (bvadd raw_sum (ite (bvslt raw_sum #b00000) (bvneg #b00010) #b00010))
                  #b00010)                     ; rounded >>2 when msb=4
                (ite IsB3
                     (bvashr
                       (bvadd raw_sum (ite (bvslt raw_sum #b00000) (bvneg #b00001) #b00001))
                       #b00001)               ; rounded >>1 when msb=3
                     (ite IsB2
                          raw_sum             ; no shift when msb=2
                          (ite IsB1
                               (bvshl raw_sum #b00001) ; <<1 when msb=1
                               (bvshl raw_sum #b00010) ; <<2 when msb=0
                          )))))
    ))

    (ExpAdj5 (_ BitVec 5) (
      (ite IsZero
           #b00000
           (ite IsB4
                (bvadd ((_ sign_extend 1) target_exp) #b00010) ; +2
                (ite IsB3
                     (bvadd ((_ sign_extend 1) target_exp) #b00001) ; +1
                     (ite IsB2
                          ((_ sign_extend 1) target_exp)           ; +0
                          (ite IsB1
                               (bvsub ((_ sign_extend 1) target_exp) #b00001) ; -1
                               (bvsub ((_ sign_extend 1) target_exp) #b00010) ; -2
                          )))))
    ))

    (ExpClamp5 (_ BitVec 5) (
      (ite (bvsgt ExpAdj5 #b00111) #b00111
           (ite (bvslt ExpAdj5 #b11000) #b11000 ExpAdj5))
    ))

    (Abs5 (_ BitVec 5) (
      (ite (bvslt raw_sum #b00000) (bvneg raw_sum) raw_sum)
    ))

    (IsZero Bool (
      (= raw_sum #b00000)
    ))

    (IsB4 Bool ( (= ((_ extract 4 4) Abs5) #b1) ))
    (IsB3 Bool ( (= ((_ extract 3 3) Abs5) #b1) ))
    (IsB2 Bool ( (= ((_ extract 2 2) Abs5) #b1) ))
    (IsB1 Bool ( (= ((_ extract 1 1) Abs5) #b1) ))
  )
)
