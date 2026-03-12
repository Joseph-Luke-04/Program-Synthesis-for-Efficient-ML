(set-logic BV)

(synth-fun mult_renorm_flag ((m1 (_ BitVec 4)) (m2 (_ BitVec 4))) (_ BitVec 1)
  (
    (Start1 (_ BitVec 1))
    (BV8 (_ BitVec 8))
    (BoolExpr Bool)
  )
  (
    (Start1 (_ BitVec 1) (
      (ite BoolExpr #b1 #b0)
    ))

    (BV8 (_ BitVec 8) (
      (bvmul ((_ sign_extend 4) m1) ((_ sign_extend 4) m2))
      (ite (bvslt BV8 #x00) (bvneg BV8) BV8)
      (bvadd BV8 BV8)
      (bvsub BV8 BV8)
      (bvor BV8 BV8)
      (bvand BV8 BV8)
      (Constant (_ BitVec 8))
    ))

    (BoolExpr Bool (
      (bvsle BV8 BV8)
      (bvslt BV8 BV8)
      (bvsge BV8 BV8)
      (bvsgt BV8 BV8)
    ))
  )
)

(declare-var m1 (_ BitVec 4))
(declare-var m2 (_ BitVec 4))
