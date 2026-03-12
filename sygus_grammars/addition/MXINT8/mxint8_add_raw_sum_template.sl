(set-logic BV)

; ===============================================================
; MXINT8 addition raw sum — "in-between" structural sketch.
; Calls align_mantissas to get aligned (m1', m2'), then combines
; them and passes through the selected exponent.
; Fixed plumbing: alignment and exponent selection are delegated
; to their respective subcomponents.
; Search space ≈ 1 (plumbing only).
; ===============================================================

(synth-fun add_raw
    ((m1 (_ BitVec 4)) (e1 (_ BitVec 4)) (m2 (_ BitVec 4)) (e2 (_ BitVec 4)))
    (_ BitVec 9)

    (
        (Start9          (_ BitVec 9))
        (AlignedResult8  (_ BitVec 8))
        (AlignedM1       (_ BitVec 4))
        (AlignedM2       (_ BitVec 4))
        (RawSum5         (_ BitVec 5))
        (TargetExp4      (_ BitVec 4))
    )

    (
      (Start9 (_ BitVec 9) (
        (concat RawSum5 TargetExp4)
      ))

      (AlignedResult8 (_ BitVec 8) (
        (align_mantissas m1 e1 m2 e2)
      ))

      (AlignedM1 (_ BitVec 4) (
        ((_ extract 7 4) AlignedResult8)
      ))

      (AlignedM2 (_ BitVec 4) (
        ((_ extract 3 0) AlignedResult8)
      ))

      (RawSum5 (_ BitVec 5) (
        (bvadd ((_ sign_extend 1) AlignedM1)
               ((_ sign_extend 1) AlignedM2))
      ))

      (TargetExp4 (_ BitVec 4) (
        (select_exponent e1 e2)
      ))
    )
)

(declare-var m1 (_ BitVec 4))
(declare-var e1 (_ BitVec 4))
(declare-var m2 (_ BitVec 4))
(declare-var e2 (_ BitVec 4))
