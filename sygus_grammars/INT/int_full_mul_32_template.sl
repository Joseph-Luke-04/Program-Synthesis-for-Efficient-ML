(set-logic BV)

(synth-fun naive_int_mul ((x (_ BitVec 32)) (y (_ BitVec 32))) (_ BitVec 32)
  ((B32 (_ BitVec 32)) (P Bool))
  (
    (B32 (_ BitVec 32) (
        x
        y
        #x00000000
        #xffffffff
        (bvmul B32 B32)
        (bvadd B32 B32)
        (bvsub B32 B32)
        (bvor  B32 B32)
        (bvand B32 B32)
        (bvxor B32 B32)
        (bvshl B32 B32)
        (bvlshr B32 B32)
        (bvashr B32 B32)
        (bvnot B32)
        (bvneg B32)
        (ite P B32 B32)
    ))
    (P Bool (
        (= B32 B32)
        (bvult B32 B32)
        (bvugt B32 B32)
        (bvslt B32 B32)
        (bvsle B32 B32)
        (and P P)
        (or  P P)
        (not P)
    ))
  )
)
