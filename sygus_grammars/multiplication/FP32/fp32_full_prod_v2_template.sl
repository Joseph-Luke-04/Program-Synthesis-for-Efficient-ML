(set-logic BV)

; ===============================================================
; Monolithic FP32 multiplier (V2)
; Encodes the pipeline stages (unpack → multiply → renorm →
; GRS rounding → exponent bias) but leaves implementation choices
; at each stage open for the solver to discover.
; ===============================================================

(synth-fun fp32_full_mul ((a (_ BitVec 32)) (b (_ BitVec 32))) (_ BitVec 32)
  (
    (Start32 (_ BitVec 32))

    (Sa (_ BitVec 1)) (Sb (_ BitVec 1))
    (Ea (_ BitVec 8)) (Eb (_ BitVec 8))
    (Fa (_ BitVec 23)) (Fb (_ BitVec 23))
    (Sout (_ BitVec 1))

    (Ma (_ BitVec 24)) (Mb (_ BitVec 24))
    (P48 (_ BitVec 48))
    (Ren (_ BitVec 1))
    (PN48 (_ BitVec 48))

    (Top24 (_ BitVec 24))
    (G (_ BitVec 1))
    (R (_ BitVec 1))
    (LowK (_ BitVec 21))
    (S (_ BitVec 1))
    (LSB (_ BitVec 1))

    (Inc1 (_ BitVec 1))
    (Rounded25 (_ BitVec 25))
    (Top24R (_ BitVec 24))
    (Frac23 (_ BitVec 23))

    (Base8 (_ BitVec 8))
    (Eout (_ BitVec 8))
  )

  (
    (Start32 (_ BitVec 32) (
      (concat Sout (concat Eout Frac23))
    ))

    ; unpack (fixed)
    (Sa (_ BitVec 1) (((_ extract 31 31) a)))
    (Sb (_ BitVec 1) (((_ extract 31 31) b)))
    (Ea (_ BitVec 8) (((_ extract 30 23) a)))
    (Eb (_ BitVec 8) (((_ extract 30 23) b)))
    (Fa (_ BitVec 23) (((_ extract 22 0) a)))
    (Fb (_ BitVec 23) (((_ extract 22 0) b)))

    ; sign (fixed correct)
    (Sout (_ BitVec 1) ((bvxor Sa Sb)))

    ; normals-only mantissas (fixed)
    (Ma (_ BitVec 24) ((concat #b1 Fa)))
    (Mb (_ BitVec 24) ((concat #b1 Fb)))

    (P48 (_ BitVec 48) (
      (bvmul ((_ zero_extend 24) Ma) ((_ zero_extend 24) Mb))
    ))

    ; keep ambiguity: which bit declares renorm
    (Ren (_ BitVec 1) (
      ((_ extract 47 47) P48)     ; correct
      ((_ extract 46 46) P48)     ; one “nearby” alternative
      ((_ extract 45 45) P48)     ; looser alternative
    ))

    (PN48 (_ BitVec 48) (
      (ite (= Ren #b1) (bvlshr P48 (_ bv1 48)) P48)
    ))

    ; loose slice + GRS candidates
    (Top24 (_ BitVec 24) (
      ((_ extract 46 23) PN48)
      ((_ extract 47 24) PN48)
      ((_ extract 45 22) PN48)
      ((_ extract 46 23) P48)
    ))
    (G (_ BitVec 1) (
      ((_ extract 22 22) PN48)
      ((_ extract 23 23) PN48)
      ((_ extract 21 21) PN48)
    ))
    (R (_ BitVec 1) (
      ((_ extract 21 21) PN48)
      ((_ extract 22 22) PN48)
      ((_ extract 20 20) PN48)
    ))
    (LowK (_ BitVec 21) (
      ((_ extract 20 0) PN48)
      (concat #b0 ((_ extract 19 0) PN48))
      ((_ extract 21 1) PN48)
    ))
    (S (_ BitVec 1) ((ite (= LowK (_ bv0 21)) #b0 #b1)))
    (LSB (_ BitVec 1) (((_ extract 0 0) Top24)))

    ; keep ambiguity: rounding mode
    (Inc1 (_ BitVec 1) (
      #b0
      G
      R
      S
      (bvor R S)
      (bvand G (bvor R S))
      (bvand G (bvor R (bvor S LSB))) ; RNE
    ))

    (Rounded25 (_ BitVec 25) (
      (bvadd ((_ zero_extend 1) Top24) ((_ zero_extend 24) Inc1))
    ))

    ; (for normals-only multiply, carry-out renorm is effectively unreachable,
    ;  but keeping this doesn’t hurt if you later extend the model)
    (Top24R (_ BitVec 24) (
      ((_ extract 23 0) Rounded25)
    ))

    (Frac23 (_ BitVec 23) (
      ((_ extract 22 0) Top24R)
      ((_ extract 22 0) Top24)
      ((_ extract 22 0) PN48)
      ((_ extract 22 0) P48)
    ))

    ; exponent: keep mild ambiguity in biasing
    (Base8 (_ BitVec 8) (
      (bvsub (bvadd Ea Eb) #b01111111)
      (bvsub (bvadd Ea Eb) #b01111110)
      (bvsub (bvadd Ea Eb) #b10000000)
    ))

    (Eout (_ BitVec 8) (
      (bvadd Base8 ((_ zero_extend 7) Ren))
    ))
  )
)
