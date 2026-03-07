(set-logic BV)

; ===============================================================
; "MINIMAL-HANDHOLDING v3" monolithic FP32 adder grammar (normals-only intent)
;
; Key changes vs v2:
;   A) Remove shift recursion: shifts only apply to *base* terms (BV24B/BV27B/BV28B).
;   B) Remove recursive boolean combos: only base predicates + optional NOT.
;   C) Keep monolithic: no explicit staging variables like Swap/Ebig/etc.
;
; This should reduce timeouts substantially while still letting the solver
; "discover" the structure via BV building blocks.
; ===============================================================

; -------------------- helper: shr 24 by 0..7 --------------------
(define-fun shr24_0_7 ((x (_ BitVec 24)) (d3 (_ BitVec 3))) (_ BitVec 24)
  (ite (= d3 #b000) x
    (ite (= d3 #b001) (bvlshr x (_ bv1 24))
      (ite (= d3 #b010) (bvlshr x (_ bv2 24))
        (ite (= d3 #b011) (bvlshr x (_ bv3 24))
          (ite (= d3 #b100) (bvlshr x (_ bv4 24))
            (ite (= d3 #b101) (bvlshr x (_ bv5 24))
              (ite (= d3 #b110) (bvlshr x (_ bv6 24))
                (bvlshr x (_ bv7 24))))))))))

; -------------------- helper: shr 27 by 0..7 --------------------
(define-fun shr27_0_7 ((x (_ BitVec 27)) (d3 (_ BitVec 3))) (_ BitVec 27)
  (ite (= d3 #b000) x
    (ite (= d3 #b001) (bvlshr x (_ bv1 27))
      (ite (= d3 #b010) (bvlshr x (_ bv2 27))
        (ite (= d3 #b011) (bvlshr x (_ bv3 27))
          (ite (= d3 #b100) (bvlshr x (_ bv4 27))
            (ite (= d3 #b101) (bvlshr x (_ bv5 27))
              (ite (= d3 #b110) (bvlshr x (_ bv6 27))
                (bvlshr x (_ bv7 27))))))))))

; -------------------- helper: shr 28 by 0..7 --------------------
(define-fun shr28_0_7 ((x (_ BitVec 28)) (d3 (_ BitVec 3))) (_ BitVec 28)
  (ite (= d3 #b000) x
    (ite (= d3 #b001) (bvlshr x (_ bv1 28))
      (ite (= d3 #b010) (bvlshr x (_ bv2 28))
        (ite (= d3 #b011) (bvlshr x (_ bv3 28))
          (ite (= d3 #b100) (bvlshr x (_ bv4 28))
            (ite (= d3 #b101) (bvlshr x (_ bv5 28))
              (ite (= d3 #b110) (bvlshr x (_ bv6 28))
                (bvlshr x (_ bv7 28))))))))))

; -------------------- helper: shl 28 by 0..3 --------------------
(define-fun shl28_0_3 ((x (_ BitVec 28)) (d2 (_ BitVec 2))) (_ BitVec 28)
  (ite (= d2 #b00) x
    (ite (= d2 #b01) (bvshl x (_ bv1 28))
      (ite (= d2 #b10) (bvshl x (_ bv2 28))
        (bvshl x (_ bv3 28))))))

; ===============================================================
; Synthesised FP32 sum
; ===============================================================
(synth-fun fp32_sum
  ((s1 (_ BitVec 1)) (e1 (_ BitVec 8)) (m1 (_ BitVec 23))
   (s2 (_ BitVec 1)) (e2 (_ BitVec 8)) (m2 (_ BitVec 23)))
  (_ BitVec 32)
  (
    (Start32 (_ BitVec 32))

    (B Bool)
    (B0 Bool)

    (S (_ BitVec 1))
    (E (_ BitVec 8))
    (F (_ BitVec 23))

    (BV1 (_ BitVec 1))
    (BV2 (_ BitVec 2))
    (BV3 (_ BitVec 3))
    (BV8 (_ BitVec 8))
    (BV10 (_ BitVec 10))

    (BV23 (_ BitVec 23))
    (BV24B (_ BitVec 24))
    (BV24 (_ BitVec 24))

    (BV27B (_ BitVec 27))
    (BV27 (_ BitVec 27))

    (BV28B (_ BitVec 28))
    (BV28 (_ BitVec 28))
  )
  (
    ; IEEE-like packing forced, content discovered.
    (Start32 (_ BitVec 32) ((concat S (concat E F))))

    (B Bool (
      B0
      (not B0)
    ))
    ; ---- Boolean controls (bounded) ----
    (B0 Bool (
      true false
      (= s1 s2)
      (= e1 e2)
      (bvult e1 e2)
      (bvugt e1 e2)
      ; "gap >= 8?" style predicate
      (bvugt (bvsub (ite (bvult e1 e2) e2 e1) (ite (bvult e1 e2) e1 e2)) (_ bv7 8))
      ; "gap <= 3?" style predicate (helps cancellations)
      (bvule (bvsub (ite (bvult e1 e2) e2 e1) (ite (bvult e1 e2) e1 e2)) (_ bv3 8))
    ))

    (S (_ BitVec 1) (BV1))
    (E (_ BitVec 8) (BV8))
    (F (_ BitVec 23) (BV23))

    ; ---- 1-bit ----
    (BV1 (_ BitVec 1) (
      s1 s2 #b0 #b1
      (ite B s1 s2)
      (ite B BV1 BV1)
      (bvand BV1 BV1)
      (bvor  BV1 BV1)
      (bvnot BV1)

      ; taps (supports G/R/S discovery)
      ((_ extract 0 0) BV27)
      ((_ extract 0 0) BV28)
      ((_ extract 1 1) BV28)
      ((_ extract 2 2) BV28)
      ((_ extract 27 27) BV28)
    ))

    ; ---- shift amounts (bounded, derived from exponents) ----
    (BV2 (_ BitVec 2) (
      #b00 #b01 #b10 #b11
      ((_ extract 1 0) (bvsub e1 e2))
      ((_ extract 1 0) (bvsub e2 e1))
    ))

    (BV3 (_ BitVec 3) (
      #b000 #b001 #b010 #b011 #b100 #b101 #b110 #b111
      ((_ extract 2 0) (bvsub e1 e2))
      ((_ extract 2 0) (bvsub e2 e1))
    ))

    ; ---- exponents ----
    (BV8 (_ BitVec 8) (
      e1 e2
      (_ bv0 8) (_ bv1 8) (_ bv2 8) (_ bv3 8)
      (_ bv127 8) (_ bv128 8)
      (ite B e1 e2)
      (bvadd e1 e2)
      (bvsub e1 e2)
      (bvsub e2 e1)
      ((_ extract 7 0) BV10)
    ))

    (BV10 (_ BitVec 10) (
      ((_ zero_extend 2) BV8)
      (_ bv0 10) (_ bv1 10) (_ bv2 10) (_ bv3 10)
      (bvadd BV10 BV10)
      (bvsub BV10 BV10)
    ))

    ; ---- fractions / mantissas ----
    (BV23 (_ BitVec 23) (
      m1 m2
      (_ bv0 23)
      (ite B m1 m2)
      (bvand m1 m2)
      (bvor  m1 m2)
      (bvadd m1 m2)
      (bvsub m1 m2)

      ; taps from wider candidates
      ((_ extract 22 0) BV24)
      ((_ extract 22 0) ((_ extract 26 3) BV28))
    ))

    ; ---- 24-bit base mantissas (hidden-bit discoverable) ----
    (BV24B (_ BitVec 24) (
      (concat #b1 m1)
      (concat #b1 m2)
      (concat #b0 m1)
      (concat #b0 m2)
      (_ bv0 24)
      (ite B (concat #b1 m1) (concat #b1 m2))
    ))

    ; BV24 can do simple ops, and can align by shifting BV24B (not BV24 itself).
    (BV24 (_ BitVec 24) (
      BV24B
      (bvadd BV24B BV24B)
      (bvsub BV24B BV24B)
      (bvand BV24B BV24B)
      (bvor  BV24B BV24B)
      (shr24_0_7 BV24B BV3)
      (ite B BV24B (shr24_0_7 BV24B BV3))
    ))

    ; ---- 27-bit base (GRS widening) ----
    (BV27B (_ BitVec 27) (
      (concat BV24 #b000)
      (concat (shr24_0_7 BV24B BV3) #b000)
      (_ bv0 27)
    ))

    ; BV27: simple ops + shift of BV27B (not BV27 itself)
    (BV27 (_ BitVec 27) (
      BV27B
      (bvadd BV27B BV27B)
      (bvsub BV27B BV27B)
      (bvand BV27B BV27B)
      (bvor  BV27B BV27B)
      (shr27_0_7 BV27B BV3)
      (ite B BV27B (shr27_0_7 BV27B BV3))
    ))

    ; ---- 28-bit base (raw add/sub + normalize candidates) ----
    (BV28B (_ BitVec 28) (
      ((_ zero_extend 1) BV27)
      (bvadd ((_ zero_extend 1) BV27) ((_ zero_extend 1) BV27))
      (bvsub ((_ zero_extend 1) BV27) ((_ zero_extend 1) BV27))
      (_ bv0 28)
    ))

    ; BV28: normalize candidates are applied to BV28B only (no chaining).
    (BV28 (_ BitVec 28) (
      BV28B
      (shr28_0_7 BV28B BV3)
      (bvlshr BV28B (_ bv1 28))     ; overflow normalize-by-1 candidate
      (shl28_0_3 BV28B BV2)         ; small left-normalize candidate
      (ite B BV28B (bvlshr BV28B (_ bv1 28)))
    ))
  )
)
