(set-logic BV)

; ===============================================================
; FP32 addition normalisation — "in-between" structural sketch.
; Takes the raw signed-magnitude sum and normalises it to IEEE 754.
; The LZC priority encoder and exponent delta are fixed define-funs
; (not part of the grammar search). Solver discovers: mantissa
; extraction, exponent adjustment, sign handling, zero detection.
; Search space ≈ 240 combinations.
; IsZero(2) × Frac23(5) × ExpOut(4) × SignOut(3) × Start32(2) = 240
; ===============================================================

; ---- Fixed helpers: LZC normalisation and exponent delta ----

(define-fun fp32_norm24 ((rsm (_ BitVec 25))) (_ BitVec 24)
  (ite (= ((_ extract 24 24) rsm) #b1) ((_ extract 24 1) rsm)
  (ite (= ((_ extract 23 23) rsm) #b1) ((_ extract 23 0) rsm)
  (ite (= ((_ extract 22 22) rsm) #b1) (concat ((_ extract 22 0) rsm) (_ bv0 1))
  (ite (= ((_ extract 21 21) rsm) #b1) (concat ((_ extract 21 0) rsm) (_ bv0 2))
  (ite (= ((_ extract 20 20) rsm) #b1) (concat ((_ extract 20 0) rsm) (_ bv0 3))
  (ite (= ((_ extract 19 19) rsm) #b1) (concat ((_ extract 19 0) rsm) (_ bv0 4))
  (ite (= ((_ extract 18 18) rsm) #b1) (concat ((_ extract 18 0) rsm) (_ bv0 5))
  (ite (= ((_ extract 17 17) rsm) #b1) (concat ((_ extract 17 0) rsm) (_ bv0 6))
  (ite (= ((_ extract 16 16) rsm) #b1) (concat ((_ extract 16 0) rsm) (_ bv0 7))
  (ite (= ((_ extract 15 15) rsm) #b1) (concat ((_ extract 15 0) rsm) (_ bv0 8))
  (ite (= ((_ extract 14 14) rsm) #b1) (concat ((_ extract 14 0) rsm) (_ bv0 9))
  (ite (= ((_ extract 13 13) rsm) #b1) (concat ((_ extract 13 0) rsm) (_ bv0 10))
  (ite (= ((_ extract 12 12) rsm) #b1) (concat ((_ extract 12 0) rsm) (_ bv0 11))
  (ite (= ((_ extract 11 11) rsm) #b1) (concat ((_ extract 11 0) rsm) (_ bv0 12))
  (ite (= ((_ extract 10 10) rsm) #b1) (concat ((_ extract 10 0) rsm) (_ bv0 13))
  (ite (= ((_ extract  9  9) rsm) #b1) (concat ((_ extract  9 0) rsm) (_ bv0 14))
  (ite (= ((_ extract  8  8) rsm) #b1) (concat ((_ extract  8 0) rsm) (_ bv0 15))
  (ite (= ((_ extract  7  7) rsm) #b1) (concat ((_ extract  7 0) rsm) (_ bv0 16))
  (ite (= ((_ extract  6  6) rsm) #b1) (concat ((_ extract  6 0) rsm) (_ bv0 17))
  (ite (= ((_ extract  5  5) rsm) #b1) (concat ((_ extract  5 0) rsm) (_ bv0 18))
  (ite (= ((_ extract  4  4) rsm) #b1) (concat ((_ extract  4 0) rsm) (_ bv0 19))
  (ite (= ((_ extract  3  3) rsm) #b1) (concat ((_ extract  3 0) rsm) (_ bv0 20))
  (ite (= ((_ extract  2  2) rsm) #b1) (concat ((_ extract  2 0) rsm) (_ bv0 21))
  (ite (= ((_ extract  1  1) rsm) #b1) (concat ((_ extract  1 0) rsm) (_ bv0 22))
  (ite (= ((_ extract  0  0) rsm) #b1) (concat ((_ extract  0 0) rsm) (_ bv0 23))
       (_ bv0 24)))))))))))))))))))))))))))

(define-fun fp32_exp_delta ((rsm (_ BitVec 25))) (_ BitVec 8)
  (ite (= ((_ extract 24 24) rsm) #b1) (_ bv1 8)
  (ite (= ((_ extract 23 23) rsm) #b1) (_ bv0 8)
  (ite (= ((_ extract 22 22) rsm) #b1) (bvneg (_ bv1 8))
  (ite (= ((_ extract 21 21) rsm) #b1) (bvneg (_ bv2 8))
  (ite (= ((_ extract 20 20) rsm) #b1) (bvneg (_ bv3 8))
  (ite (= ((_ extract 19 19) rsm) #b1) (bvneg (_ bv4 8))
  (ite (= ((_ extract 18 18) rsm) #b1) (bvneg (_ bv5 8))
  (ite (= ((_ extract 17 17) rsm) #b1) (bvneg (_ bv6 8))
  (ite (= ((_ extract 16 16) rsm) #b1) (bvneg (_ bv7 8))
  (ite (= ((_ extract 15 15) rsm) #b1) (bvneg (_ bv8 8))
  (ite (= ((_ extract 14 14) rsm) #b1) (bvneg (_ bv9 8))
  (ite (= ((_ extract 13 13) rsm) #b1) (bvneg (_ bv10 8))
  (ite (= ((_ extract 12 12) rsm) #b1) (bvneg (_ bv11 8))
  (ite (= ((_ extract 11 11) rsm) #b1) (bvneg (_ bv12 8))
  (ite (= ((_ extract 10 10) rsm) #b1) (bvneg (_ bv13 8))
  (ite (= ((_ extract  9  9) rsm) #b1) (bvneg (_ bv14 8))
  (ite (= ((_ extract  8  8) rsm) #b1) (bvneg (_ bv15 8))
  (ite (= ((_ extract  7  7) rsm) #b1) (bvneg (_ bv16 8))
  (ite (= ((_ extract  6  6) rsm) #b1) (bvneg (_ bv17 8))
  (ite (= ((_ extract  5  5) rsm) #b1) (bvneg (_ bv18 8))
  (ite (= ((_ extract  4  4) rsm) #b1) (bvneg (_ bv19 8))
  (ite (= ((_ extract  3  3) rsm) #b1) (bvneg (_ bv20 8))
  (ite (= ((_ extract  2  2) rsm) #b1) (bvneg (_ bv21 8))
  (ite (= ((_ extract  1  1) rsm) #b1) (bvneg (_ bv22 8))
  (ite (= ((_ extract  0  0) rsm) #b1) (bvneg (_ bv23 8))
       (_ bv0 8)))))))))))))))))))))))))))

; ---- Synth-fun: the final assembly choices are searched ----

(synth-fun fp32_normaliser
  ((raw_sum_mantissa (_ BitVec 25))
   (raw_sign        (_ BitVec 1))
   (target_exponent (_ BitVec 8)))
  (_ BitVec 32)

  (
    (Start32  (_ BitVec 32))
    (IsZero   Bool)
    (Norm24   (_ BitVec 24))
    (Frac23   (_ BitVec 23))
    (ExpAdj8  (_ BitVec 8))
    (ExpOut   (_ BitVec 8))
    (SignOut  (_ BitVec 1))
  )

  (
    ; --- Output packing ---
    (Start32 (_ BitVec 32) (
      (concat SignOut (concat ExpOut Frac23))
      (ite IsZero (_ bv0 32) (concat SignOut (concat ExpOut Frac23)))
    ))

    ; --- Zero detection ---
    (IsZero Bool (
      (= raw_sum_mantissa (_ bv0 25))
      (= raw_sum_mantissa #b0000000000000000000000000)
    ))

    ; --- Normalised 24-bit value (via define-fun helper) ---
    (Norm24 (_ BitVec 24) (
      (fp32_norm24 raw_sum_mantissa)
    ))

    ; --- Mantissa: strip hidden bit from normalised value ---
    (Frac23 (_ BitVec 23) (
      (ite IsZero (_ bv0 23) ((_ extract 22 0) Norm24))
      ((_ extract 22 0) Norm24)
      ((_ extract 22 0) raw_sum_mantissa)
      (ite IsZero (_ bv0 23) ((_ extract 23 1) Norm24))
      ((_ extract 23 1) Norm24)
    ))

    ; --- Exponent delta (via define-fun helper) ---
    (ExpAdj8 (_ BitVec 8) (
      (bvadd target_exponent (fp32_exp_delta raw_sum_mantissa))
    ))

    ; --- Exponent output ---
    (ExpOut (_ BitVec 8) (
      (ite IsZero (_ bv0 8) ExpAdj8)
      ExpAdj8
      target_exponent
      (ite IsZero (_ bv0 8) target_exponent)
    ))

    ; --- Sign output ---
    (SignOut (_ BitVec 1) (
      (ite IsZero #b0 raw_sign)
      raw_sign
      #b0
    ))
  )
)
