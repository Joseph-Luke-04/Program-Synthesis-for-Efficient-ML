(set-logic BV)

(define-fun select_exponent ((e1 (_ BitVec 4)) (e2 (_ BitVec 4))) (_ BitVec 4) (ite (bvsge e1 e2) e1 e2))
(define-fun align_mantissas ((m1 (_ BitVec 4)) (e1 (_ BitVec 4)) (m2 (_ BitVec 4)) (e2 (_ BitVec 4))) (_ BitVec 8) (let ((_let_1 (bvsge e1 e2))) (concat (ite _let_1 m1 (bvashr m1 (bvsub e2 e1))) (ite _let_1 (bvashr m2 (bvsub e1 e2)) m2))))
(define-fun add_raw ((m1 (_ BitVec 4)) (e1 (_ BitVec 4)) (m2 (_ BitVec 4)) (e2 (_ BitVec 4))) (_ BitVec 9) (let ((_let_1 (align_mantissas m1 e1 m2 e2))) (concat (bvadd ((_ sign_extend 1) ((_ extract 7 4) _let_1)) ((_ sign_extend 1) ((_ extract 3 0) _let_1))) (select_exponent e1 e2))))

(synth-fun detect_overflow
    ((raw_sum (_ BitVec 5)))
    (_ BitVec 1)
    (
        (Start1 (_ BitVec 1))
        (Condition Bool)
        (Constant5 (_ BitVec 5))
    )
    (
      (Start1 (_ BitVec 1) ( (ite Condition #b1 #b0) ))
      (Condition Bool ( (or (bvsgt raw_sum Constant5) (bvslt raw_sum Constant5)) ))
      (Constant5 (_ BitVec 5) (
        #b00111
        #b11000
      ))
    )
)

(declare-var raw_sum (_ BitVec 5))