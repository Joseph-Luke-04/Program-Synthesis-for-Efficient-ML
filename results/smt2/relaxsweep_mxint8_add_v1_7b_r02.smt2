(define-fun norm_shifted5 ((raw (_ BitVec 5))) (_ BitVec 5)
  (let ((abs5 (ite (bvslt raw #b00000) (bvneg raw) raw)))
    (ite (= raw #b00000)
         raw
         (ite (= ((_ extract 4 4) abs5) #b1)
              (bvashr raw #b00010)
              (ite (= ((_ extract 3 3) abs5) #b1)
                   (bvashr raw #b00001)
                   (ite (= ((_ extract 2 2) abs5) #b1)
                        raw
                        (ite (= ((_ extract 1 1) abs5) #b1)
                             (bvshl raw #b00001)
                             (bvshl raw #b00010))))))))

(define-fun exp_delta5_from_raw ((raw (_ BitVec 5))) (_ BitVec 5)
  (let ((abs5 (ite (bvslt raw #b00000) (bvneg raw) raw)))
    (ite (= raw #b00000)
         #b00000
         (ite (= ((_ extract 4 4) abs5) #b1)
              #b00010
              (ite (= ((_ extract 3 3) abs5) #b1)
                   #b00001
                   (ite (= ((_ extract 2 2) abs5) #b1)
                        #b00000
                        (ite (= ((_ extract 1 1) abs5) #b1)
                             #b11111
                             #b11110)))))))

(define-fun sat_mant4 ((shifted (_ BitVec 5))) (_ BitVec 4)
  (ite (bvsgt shifted #b00111)
       #b0111
       (ite (bvslt shifted #b11000)
            #b1000
            ((_ extract 3 0) shifted))))

(define-fun clamp_exp4 ((exp_adj (_ BitVec 5))) (_ BitVec 4)
  ((_ extract 3 0)
   (ite (bvsgt exp_adj #b00111)
        #b00111
        (ite (bvslt exp_adj #b11000) #b11000 exp_adj))))

(define-fun add_full_sum ((m1 (_ BitVec 4)) (e1 (_ BitVec 4)) (m2 (_ BitVec 4)) (e2 (_ BitVec 4))) (_ BitVec 8) (let ((_let_1 ((_ sign_extend 1) e1))) (let ((_let_2 ((_ sign_extend 1) e2))) (let ((_let_3 (bvsge e1 e2))) (let ((_let_4 (ite _let_3 (bvsub _let_1 _let_2) (bvsub _let_2 _let_1)))) (let ((_let_5 ((_ sign_extend 1) (ite _let_3 m2 m1)))) (let ((_let_6 ((_ sign_extend 1) (ite _let_3 m1 m2)))) (concat ((_ extract 3 0) (bvadd ((_ sign_extend 1) (ite (bvsgt e1 e2) e1 e2)) (exp_delta5_from_raw (bvadd _let_6 (bvadd _let_5 ((_ sign_extend 1) ((_ extract 3 0) _let_4))))))) (ite (= _let_6 #b00000) #b0000 (sat_mant4 (norm_shifted5 (bvadd _let_6 ((_ sign_extend 1) ((_ extract 3 0) (bvashr _let_5 _let_4)))))))))))))))