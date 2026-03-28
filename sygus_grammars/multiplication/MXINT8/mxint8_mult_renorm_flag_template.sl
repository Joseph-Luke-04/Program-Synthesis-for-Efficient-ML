(set-logic BV)

; MXINT8 renorm flag: detects |prod| >= 32 (needs >>3 rather than >>2).
; Search space ≈ 64 combinations. Abs8(2) × Thresh8(3) × Cmp(5) + BitDetect(2).

(synth-fun mult_renorm_flag ((m1 (_ BitVec 4)) (m2 (_ BitVec 4))) (_ BitVec 1)
  (
    (Start1    (_ BitVec 1))
    (Prod8     (_ BitVec 8))
    (Abs8      (_ BitVec 8))
    (BitDetect (_ BitVec 1))
    (Thresh8   (_ BitVec 8))
    (Cmp       Bool)
  )
  (
    ; --- Output: threshold comparison or direct bit extraction ---
    (Start1 (_ BitVec 1) (
      (ite Cmp #b1 #b0)
      BitDetect
    ))

    ; --- Stage 1: Raw signed product ---
    (Prod8 (_ BitVec 8) (
      (bvmul ((_ sign_extend 4) m1) ((_ sign_extend 4) m2))
    ))

    ; --- Stage 2: Absolute value (or raw if sign is irrelevant) ---
    (Abs8 (_ BitVec 8) (
      (ite (bvslt Prod8 #x00) (bvneg Prod8) Prod8)
      Prod8
    ))

    ; --- Stage 2a: Direct bit detection (|prod|>=32 sets bit 5) ---
    (BitDetect (_ BitVec 1) (
      ((_ extract 5 5) Abs8)   ; set iff |prod| >= 32
      ((_ extract 6 6) Abs8)   ; set iff |prod| >= 64
    ))

    ; --- Stage 3: Threshold ---
    (Thresh8 (_ BitVec 8) (
      #x1F  ; 31
      #x20  ; 32
      #x21  ; 33
    ))

    ; --- Stage 4: Comparison direction ---
    (Cmp Bool (
      (bvsge Abs8 Thresh8)
      (bvsgt Abs8 Thresh8)
      (bvsle Abs8 Thresh8)
      (bvslt Abs8 Thresh8)
      (= Abs8 Thresh8)
    ))
  )
)

(declare-var m1 (_ BitVec 4))
(declare-var m2 (_ BitVec 4))
