(set-logic BV)

(synth-fun select_exponent 
    ((e1 (_ BitVec 4)) (e2 (_ BitVec 4))) 
    (_ BitVec 4)
    (
        (Start4 (_ BitVec 4))
        (Condition Bool)
    )
    (
      (Start4 (_ BitVec 4) ( (ite Condition e1 e2) ))
      (Condition Bool ( (bvsge e1 e2) ))
    )
)

(synth-fun align_mantissas
    ((m1 (_ BitVec 4)) (e1 (_ BitVec 4)) (m2 (_ BitVec 4)) (e2 (_ BitVec 4)))
    (_ BitVec 8)
    (
        (Start8 (_ BitVec 8))
        (AlignedM1 (_ BitVec 4))
        (AlignedM2 (_ BitVec 4))
        (ShiftAmount (_ BitVec 4))
        (Condition Bool)
        (LargeShift Bool)
    )
    (
      (Start8 (_ BitVec 8) ( (concat AlignedM1 AlignedM2) ))

      (AlignedM1 (_ BitVec 4) (
        (ite Condition
             m1
             (ite LargeShift
                  #b0000
                  (bvashr m1 ShiftAmount)))
      ))

      (AlignedM2 (_ BitVec 4) (
        (ite Condition
             (ite LargeShift
                  #b0000
                  (bvashr m2 ShiftAmount))
             m2)
      ))

      (ShiftAmount (_ BitVec 4) (
        (ite Condition (bvsub e1 e2) (bvsub e2 e1))
      ))

      (Condition Bool ( (bvsge e1 e2) ))
      (LargeShift Bool ( (bvuge ShiftAmount #b0100) ))
    )
)

(declare-var m1 (_ BitVec 4))
(declare-var e1 (_ BitVec 4))
(declare-var m2 (_ BitVec 4))
(declare-var e2 (_ BitVec 4))
