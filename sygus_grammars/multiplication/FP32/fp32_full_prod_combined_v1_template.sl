(set-logic BV)

; Monolithic FP32 multiplier baseline grammar (V1).
; Broader than the current guided V2 grammar:
;   - more renorm-bit choices,
;   - more shifted-product and GRS slice choices,
;   - weaker exponent and packing alternatives.

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
    (Carry1 (_ BitVec 1))
    (Eout (_ BitVec 8))
  )

  (
    (Start32 (_ BitVec 32) (
      (concat Sout (concat Eout Frac23))
    ))

    (Sa (_ BitVec 1) (((_ extract 31 31) a)))
    (Sb (_ BitVec 1) (((_ extract 31 31) b)))
    (Ea (_ BitVec 8) (((_ extract 30 23) a)))
    (Eb (_ BitVec 8) (((_ extract 30 23) b)))
    (Fa (_ BitVec 23) (((_ extract 22 0) a)))
    (Fb (_ BitVec 23) (((_ extract 22 0) b)))

    (Sout (_ BitVec 1) (
      (bvxor Sa Sb)
      Sa
      Sb
      #b0
    ))

    (Ma (_ BitVec 24) (
      (concat #b1 Fa)
      ((_ zero_extend 1) Fa)
    ))

    (Mb (_ BitVec 24) (
      (concat #b1 Fb)
      ((_ zero_extend 1) Fb)
    ))

    (P48 (_ BitVec 48) (
      (bvmul ((_ zero_extend 24) Ma) ((_ zero_extend 24) Mb))
    ))

    (Ren (_ BitVec 1) (
      ((_ extract 47 47) P48)
      ((_ extract 46 46) P48)
      ((_ extract 45 45) P48)
      ((_ extract 44 44) P48)
      ((_ extract 43 43) P48)
    ))

    (PN48 (_ BitVec 48) (
      (ite (= Ren #b1) (bvlshr P48 (_ bv1 48)) P48)
      (ite (= Ren #b1) (bvlshr P48 (_ bv2 48)) P48)
      P48
    ))

    (Top24 (_ BitVec 24) (
      ((_ extract 46 23) PN48)
      ((_ extract 47 24) PN48)
      ((_ extract 45 22) PN48)
      ((_ extract 44 21) PN48)
      ((_ extract 46 23) P48)
      ((_ extract 47 24) P48)
    ))

    (G (_ BitVec 1) (
      ((_ extract 22 22) PN48)
      ((_ extract 23 23) PN48)
      ((_ extract 21 21) PN48)
      ((_ extract 22 22) P48)
    ))

    (R (_ BitVec 1) (
      ((_ extract 21 21) PN48)
      ((_ extract 22 22) PN48)
      ((_ extract 20 20) PN48)
      ((_ extract 21 21) P48)
    ))

    (LowK (_ BitVec 21) (
      ((_ extract 20 0) PN48)
      (concat #b0 ((_ extract 19 0) PN48))
      ((_ extract 21 1) PN48)
      ((_ extract 20 0) P48)
    ))

    (S (_ BitVec 1) (
      (ite (= LowK (_ bv0 21)) #b0 #b1)
      #b0
      #b1
    ))

    (LSB (_ BitVec 1) (
      ((_ extract 0 0) Top24)
      ((_ extract 0 0) Ma)
      ((_ extract 0 0) Mb)
    ))

    (Inc1 (_ BitVec 1) (
      #b0
      #b1
      G
      R
      S
      (bvor R S)
      (bvand G (bvor R S))
      (bvand G (bvor R (bvor S LSB)))
    ))

    (Rounded25 (_ BitVec 25) (
      (bvadd ((_ zero_extend 1) Top24) ((_ zero_extend 24) Inc1))
      ((_ zero_extend 1) Top24)
    ))

    (Top24R (_ BitVec 24) (
      ((_ extract 23 0) Rounded25)
      Top24
    ))

    (Frac23 (_ BitVec 23) (
      ((_ extract 22 0) Top24R)
      ((_ extract 22 0) Top24)
      ((_ extract 22 0) PN48)
      ((_ extract 22 0) P48)
      ((_ extract 22 0) Rounded25)
    ))

    (Base8 (_ BitVec 8) (
      (bvsub (bvadd Ea Eb) #b01111111)
      (bvsub (bvadd Ea Eb) #b01111110)
      (bvsub (bvadd Ea Eb) #b10000000)
      (bvadd Ea Eb)
    ))

    (Carry1 (_ BitVec 1) (
      ((_ extract 24 24) Rounded25)
      Inc1
      #b0
      #b1
    ))

    (Eout (_ BitVec 8) (
      Base8
      (bvadd Base8 ((_ zero_extend 7) Ren))
      (bvadd Base8 ((_ zero_extend 7) Carry1))
      (bvadd (bvadd Base8 ((_ zero_extend 7) Ren)) ((_ zero_extend 7) Carry1))
    ))
  )
)
