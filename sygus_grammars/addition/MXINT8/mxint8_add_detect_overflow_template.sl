(set-logic BV)

; ===============================================================
; MXINT8 addition overflow detection — "in-between" structural sketch.
; Detects whether the 5-bit raw sum overflows signed 4-bit range.
; Returns 1 if overflow, 0 otherwise.
; Search space ≈ 75 combinations.
; Abs5(3) × Threshold5(5) × Overflows(5) = 75
; ===============================================================

; Helper definitions are injected by the synthesis driver.

(synth-fun detect_overflow
    ((raw_sum (_ BitVec 5)))
    (_ BitVec 1)
    (
        (Start1     (_ BitVec 1))
        (Abs5       (_ BitVec 5))
        (Threshold5 (_ BitVec 5))
        (Overflows  Bool)
    )
    (
      (Start1 (_ BitVec 1) (
        (ite Overflows #b1 #b0)
        #b0
      ))

      ; --- Stage 1: Absolute value computation ---
      (Abs5 (_ BitVec 5) (
        (ite (bvslt raw_sum #b00000) (bvneg raw_sum) raw_sum)
        raw_sum
        (bvand raw_sum #b01111)
      ))

      ; --- Stage 2: Overflow threshold ---
      (Threshold5 (_ BitVec 5) (
        #b00111       ; 7
        #b01000       ; 8
        #b01111       ; 15
        #b00100       ; 4
        #b01010       ; 10
      ))

      ; --- Stage 3: Overflow detection ---
      ; Solver discovers comparison type and strategy.
      (Overflows Bool (
        (bvsgt Abs5 Threshold5)
        (bvsge Abs5 Threshold5)
        (bvugt Abs5 Threshold5)
        (bvuge Abs5 Threshold5)
        (not (= ((_ extract 4 4) raw_sum) ((_ extract 3 3) raw_sum)))
      ))
    )
)

(declare-var raw_sum (_ BitVec 5))
