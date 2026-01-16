(set-logic BV)

(synth-fun naive_int_add ((x (_ BitVec 8)) (y (_ BitVec 8))) (_ BitVec 8)
  ((B8 (_ BitVec 8)) (P Bool))
  (
    (B8 (_ BitVec 8) (
        x
        y
        #x00
        #xff
        (bvadd B8 B8)
        (bvsub B8 B8)
        (bvor  B8 B8)
        (bvand B8 B8)
        (bvxor B8 B8)
        (bvshl B8 B8)
        (bvlshr B8 B8)
        (bvashr B8 B8)
        (bvnot B8)
        (bvneg B8)
        (ite P B8 B8)
    ))
    (P Bool (
        (= B8 B8)
        (bvult B8 B8)
        (bvugt B8 B8)
        (bvslt B8 B8)
        (bvsle B8 B8)
        (and P P)
        (or  P P)
        (not P)
    ))
  )
)