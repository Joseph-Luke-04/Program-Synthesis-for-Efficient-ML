(set-logic BV)

; =================================================================
; Helper components
; =================================================================

(define-fun fp32_aligner
  ((e1 (_ BitVec 8)) (m1 (_ BitVec 23))
   (e2 (_ BitVec 8)) (m2 (_ BitVec 23)))
  (_ BitVec 56)
  (let ((_let_1 (bvuge e1 e2)))
    (let ((_let_2 (concat (ite (= e2 #b00000000) #b0 #b1) m2)))
    (let ((_let_3 (concat #b0000000000000000 (ite _let_1 (bvsub e1 e2) (bvsub e2 e1)))))
    (let ((_let_4 (concat (ite (= e1 #b00000000) #b0 #b1) m1)))
      (concat
        (ite _let_1 _let_4 (bvlshr _let_4 _let_3))
        (concat
          (ite _let_1 (bvlshr _let_2 _let_3) _let_2)
          (ite _let_1 e1 e2))))))))

(define-fun fp32_raw_summer
  ((s1 (_ BitVec 1)) (aligned_m1 (_ BitVec 24))
   (s2 (_ BitVec 1)) (aligned_m2 (_ BitVec 24)))
  (_ BitVec 26)
  (let ((_let_1 (concat #b0 aligned_m1)))
  (let ((_let_2 (concat #b0 aligned_m2)))
  (let ((_let_3 (bvuge aligned_m1 aligned_m2)))
  (let ((_let_4 (= s1 s2)))
    (concat
      (ite (and (not _let_4) (= aligned_m1 aligned_m2))
           #b0
           (ite _let_4 s1 (ite _let_3 s1 s2)))
      (ite _let_4
           (bvadd _let_1 _let_2)
           (ite _let_3 (bvsub _let_1 _let_2) (bvsub _let_2 _let_1)))))))))

(define-fun fp32_normaliser
  ((raw_sum_mantissa (_ BitVec 25))
   (raw_sign        (_ BitVec 1))
   (target_exponent (_ BitVec 8)))
  (_ BitVec 32)
  (let ((_let_1 ((_ extract 0 0) raw_sum_mantissa)))
  (let ((_let_2 (= _let_1 #b1)))
  (let ((_let_3 (= ((_ extract 1 1) raw_sum_mantissa) #b1)))
  (let ((_let_4 (= ((_ extract 2 2) raw_sum_mantissa) #b1)))
  (let ((_let_5 (= ((_ extract 3 3) raw_sum_mantissa) #b1)))
  (let ((_let_6 (= ((_ extract 4 4) raw_sum_mantissa) #b1)))
  (let ((_let_7 (= ((_ extract 5 5) raw_sum_mantissa) #b1)))
  (let ((_let_8 (= ((_ extract 6 6) raw_sum_mantissa) #b1)))
  (let ((_let_9 (= ((_ extract 7 7) raw_sum_mantissa) #b1)))
  (let ((_let_10 (= ((_ extract 8 8) raw_sum_mantissa) #b1)))
  (let ((_let_11 (= ((_ extract 9 9) raw_sum_mantissa) #b1)))
  (let ((_let_12 (= ((_ extract 10 10) raw_sum_mantissa) #b1)))
  (let ((_let_13 (= ((_ extract 11 11) raw_sum_mantissa) #b1)))
  (let ((_let_14 (= ((_ extract 12 12) raw_sum_mantissa) #b1)))
  (let ((_let_15 (= ((_ extract 13 13) raw_sum_mantissa) #b1)))
  (let ((_let_16 (= ((_ extract 14 14) raw_sum_mantissa) #b1)))
  (let ((_let_17 (= ((_ extract 15 15) raw_sum_mantissa) #b1)))
  (let ((_let_18 (= ((_ extract 16 16) raw_sum_mantissa) #b1)))
  (let ((_let_19 (= ((_ extract 17 17) raw_sum_mantissa) #b1)))
  (let ((_let_20 (= ((_ extract 18 18) raw_sum_mantissa) #b1)))
  (let ((_let_21 (= ((_ extract 19 19) raw_sum_mantissa) #b1)))
  (let ((_let_22 (= ((_ extract 20 20) raw_sum_mantissa) #b1)))
  (let ((_let_23 (= ((_ extract 21 21) raw_sum_mantissa) #b1)))
  (let ((_let_24 (= ((_ extract 22 22) raw_sum_mantissa) #b1)))
  (let ((_let_25 (= ((_ extract 23 23) raw_sum_mantissa) #b1)))
  (let ((_let_26 (= ((_ extract 24 24) raw_sum_mantissa) #b1)))
  (let ((_let_27 (= raw_sum_mantissa #b0000000000000000000000000)))
    (concat
      (ite _let_27 #b0 raw_sign)
      (concat
        (ite _let_27 #b00000000
             (bvadd target_exponent
               (ite _let_26 #b00000001
               (ite _let_25 #b00000000
               (ite _let_24 (bvneg #b00000001)
               (ite _let_23 (bvneg #b00000010)
               (ite _let_22 (bvneg #b00000011)
               (ite _let_21 (bvneg #b00000100)
               (ite _let_20 (bvneg #b00000101)
               (ite _let_19 (bvneg #b00000110)
               (ite _let_18 (bvneg #b00000111)
               (ite _let_17 (bvneg #b00001000)
               (ite _let_16 (bvneg #b00001001)
               (ite _let_15 (bvneg #b00001010)
               (ite _let_14 (bvneg #b00001011)
               (ite _let_13 (bvneg #b00001100)
               (ite _let_12 (bvneg #b00001101)
               (ite _let_11 (bvneg #b00001110)
               (ite _let_10 (bvneg #b00001111)
               (ite _let_9  (bvneg #b00010000)
               (ite _let_8  (bvneg #b00010001)
               (ite _let_7  (bvneg #b00010010)
               (ite _let_6  (bvneg #b00010011)
               (ite _let_5  (bvneg #b00010100)
               (ite _let_4  (bvneg #b00010101)
               (ite _let_3  (bvneg #b00010110)
               (ite _let_2  (bvneg #b00010111) #b00000000)))))))))))))))))))))))))))
        ((_ extract 22 0)
          (ite _let_26 ((_ extract 24 1) raw_sum_mantissa)
          (ite _let_25 ((_ extract 23 0) raw_sum_mantissa)
          (ite _let_24 (concat ((_ extract 22 0) raw_sum_mantissa) #b0)
          (ite _let_23 (concat ((_ extract 21 0) raw_sum_mantissa) #b00)
          (ite _let_22 (concat ((_ extract 20 0) raw_sum_mantissa) #b000)
          (ite _let_21 (concat ((_ extract 19 0) raw_sum_mantissa) #b0000)
          (ite _let_20 (concat ((_ extract 18 0) raw_sum_mantissa) #b00000)
          (ite _let_19 (concat ((_ extract 17 0) raw_sum_mantissa) #b000000)
          (ite _let_18 (concat ((_ extract 16 0) raw_sum_mantissa) #b0000000)
          (ite _let_17 (concat ((_ extract 15 0) raw_sum_mantissa) #b00000000)
          (ite _let_16 (concat ((_ extract 14 0) raw_sum_mantissa) #b000000000)
          (ite _let_15 (concat ((_ extract 13 0) raw_sum_mantissa) #b0000000000)
          (ite _let_14 (concat ((_ extract 12 0) raw_sum_mantissa) #b00000000000)
          (ite _let_13 (concat ((_ extract 11 0) raw_sum_mantissa) #b000000000000)
          (ite _let_12 (concat ((_ extract 10 0) raw_sum_mantissa) #b0000000000000)
          (ite _let_11 (concat ((_ extract 9 0) raw_sum_mantissa) #b00000000000000)
          (ite _let_10 (concat ((_ extract 8 0) raw_sum_mantissa) #b000000000000000)
          (ite _let_9  (concat ((_ extract 7 0) raw_sum_mantissa) #b0000000000000000)
          (ite _let_8  (concat ((_ extract 6 0) raw_sum_mantissa) #b00000000000000000)
          (ite _let_7  (concat ((_ extract 5 0) raw_sum_mantissa) #b000000000000000000)
          (ite _let_6  (concat ((_ extract 4 0) raw_sum_mantissa) #b0000000000000000000)
          (ite _let_5  (concat ((_ extract 3 0) raw_sum_mantissa) #b00000000000000000000)
          (ite _let_4  (concat ((_ extract 2 0) raw_sum_mantissa) #b000000000000000000000)
          (ite _let_3  (concat ((_ extract 1 0) raw_sum_mantissa) #b0000000000000000000000)
          (ite _let_2  (concat _let_1 #b00000000000000000000000)
                       #b000000000000000000000000))))))))))))))))))))))))))))))))))))))))))))))))))))))))

; =================================================================
; Synthesize the composed FP32 adder
; =================================================================

(synth-fun fp32_sum
  ((s1 (_ BitVec 1)) (e1 (_ BitVec 8)) (m1 (_ BitVec 23))
   (s2 (_ BitVec 1)) (e2 (_ BitVec 8)) (m2 (_ BitVec 23)))
  (_ BitVec 32)

  (
    (Start32  (_ BitVec 32))
    (AlignOut (_ BitVec 56))
    (A1       (_ BitVec 24))
    (A2       (_ BitVec 24))
    (Texp     (_ BitVec 8))
    (RawOut   (_ BitVec 26))
    (Rsign    (_ BitVec 1))
    (Rmant    (_ BitVec 25))
  )

  (
    ; 1 - Final packing: normaliser output
    (Start32 (_ BitVec 32)
      ((fp32_normaliser Rmant Rsign Texp)))

    ; 2 - Stage 1: alignment
    (AlignOut (_ BitVec 56)
      ((fp32_aligner e1 m1 e2 m2)))
    (A1   (_ BitVec 24) (((_ extract 55 32) AlignOut)))
    (A2   (_ BitVec 24) (((_ extract 31 8)  AlignOut)))
    (Texp (_ BitVec 8)  (((_ extract 7  0)  AlignOut)))

    ; 3 - Stage 2: raw sum
    (RawOut (_ BitVec 26)
      ((fp32_raw_summer s1 A1 s2 A2)))
    (Rsign (_ BitVec 1)  (((_ extract 25 25) RawOut)))
    (Rmant (_ BitVec 25) (((_ extract 24  0) RawOut)))
  )
)
