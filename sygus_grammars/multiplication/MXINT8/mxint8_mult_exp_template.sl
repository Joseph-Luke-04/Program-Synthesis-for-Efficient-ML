(set-logic BV)

(synth-fun mult_mxint_exp ((e1 (_ BitVec 4)) (e2 (_ BitVec 4)) (renorm_flag (_ BitVec 1))) (_ BitVec 4)
  (
    (Start4 (_ BitVec 4))
    (BV4 (_ BitVec 4))
    (BoolExpr Bool)
  )
  (
    (Start4 (_ BitVec 4) (
      (ite BoolExpr BV4 BV4)
      BV4
    ))

    (BV4 (_ BitVec 4) (
      e1
      e2
      (bvadd BV4 BV4)
      (bvsub BV4 BV4)
      (bvor BV4 BV4)
      (bvand BV4 BV4)
      (ite BoolExpr BV4 BV4)
      (Constant (_ BitVec 4))
    ))

    (BoolExpr Bool (
      (= renorm_flag #b1)
      (= renorm_flag #b0)
      (bvslt BV4 BV4)
      (bvsge BV4 BV4)
    ))
  )
)
