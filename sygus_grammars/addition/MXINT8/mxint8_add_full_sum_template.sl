(set-logic BV)

; Compose the MXINT8 adder from alignment + raw sum + normalisation.
(synth-fun add_full_sum
    ((m1 (_ BitVec 4)) (e1 (_ BitVec 4)) (m2 (_ BitVec 4)) (e2 (_ BitVec 4)))
    (_ BitVec 8)

    (
        (Start8 (_ BitVec 8))
        (Raw9   (_ BitVec 9))
    )

    (
      (Start8 (_ BitVec 8) (
        (let ((raw Raw9))
          (normalise_addition ((_ extract 8 4) raw) ((_ extract 3 0) raw)))
      ))

      (Raw9 (_ BitVec 9) (
        (add_raw m1 e1 m2 e2)
      ))
    )
)

(declare-var m1 (_ BitVec 4))
(declare-var e1 (_ BitVec 4))
(declare-var m2 (_ BitVec 4))
(declare-var e2 (_ BitVec 4))
