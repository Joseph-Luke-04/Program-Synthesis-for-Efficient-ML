(set-logic BV)

; =================================================================

(define-fun select_exponent ((e1 (_ BitVec 4)) (e2 (_ BitVec 4))) (_ BitVec 4) (ite (bvsge e1 e2) e1 e2))
(define-fun align_mantissas ((m1 (_ BitVec 4)) (e1 (_ BitVec 4)) (m2 (_ BitVec 4)) (e2 (_ BitVec 4))) (_ BitVec 8) (let ((_let_1 (bvsge e1 e2))) (concat (ite _let_1 m1 (bvashr m1 (bvsub e2 e1))) (ite _let_1 (bvashr m2 (bvsub e1 e2)) m2))))

; =================================================================


(synth-fun add_raw
    ((m1 (_ BitVec 4)) (e1 (_ BitVec 4)) (m2 (_ BitVec 4)) (e2 (_ BitVec 4)))
    (_ BitVec 9)


    (
        (Start9 (_ BitVec 9))
        (RawSum5 (_ BitVec 5))
        (TargetExp4 (_ BitVec 4))
        (AlignedM1_4bit (_ BitVec 4))
        (AlignedM2_4bit (_ BitVec 4))
        (AlignedResult8 (_ BitVec 8))
    )


    (

      (Start9 (_ BitVec 9) (
        (concat RawSum5 TargetExp4)
      ))


      (RawSum5 (_ BitVec 5) (
        (bvadd ((_ sign_extend 1) AlignedM1_4bit)
               ((_ sign_extend 1) AlignedM2_4bit))
      ))
      
      
      (TargetExp4 (_ BitVec 4) (
        (select_exponent e1 e2)
      ))
      
    
      (AlignedM1_4bit (_ BitVec 4) (
          ((_ extract 7 4) AlignedResult8)
      ))
      

      (AlignedM2_4bit (_ BitVec 4) (
          ((_ extract 3 0) AlignedResult8)
      ))

    
      (AlignedResult8 (_ BitVec 8) (
        (align_mantissas m1 e1 m2 e2)
      ))
    )
)


(declare-var m1 (_ BitVec 4))
(declare-var e1 (_ BitVec 4))
(declare-var m2 (_ BitVec 4))
(declare-var e2 (_ BitVec 4))
