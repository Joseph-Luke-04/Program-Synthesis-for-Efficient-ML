(set-logic BV)

; Monolithic MXINT8 adder grammar aligned to software ground truth.
(synth-fun add_full_sum
  ((m1 (_ BitVec 4)) (e1 (_ BitVec 4)) (m2 (_ BitVec 4)) (e2 (_ BitVec 4)))
  (_ BitVec 8)
  (
    (Start8 (_ BitVec 8))
  )
  (
    (Start8 (_ BitVec 8)
      (
        (let ((swap (bvsge e1 e2)))
          (let ((mbig (ite swap m1 m2)))
            (let ((msmall (ite swap m2 m1)))
              (let ((ebig (ite swap e1 e2)))
                (let ((esmall (ite swap e2 e1)))
                  (let ((diff4 (bvsub ebig esmall)))
                    (let ((bias4
                           (ite (= diff4 #b0001) #b0001
                             (ite (= diff4 #b0010) #b0010
                               (ite (= diff4 #b0011) #b0100 #b0000)))))
                      (let ((bias_signed4 (ite (bvslt msmall #b0000) (bvneg bias4) bias4)))
                        ; Match software model: apply rounding bias in wider signed domain
                        ; before shifting, then truncate back to 4 bits.
                        (let ((aligned_small4
                               (ite (bvuge diff4 #b0100) #b0000
                                 (ite (= diff4 #b0000) msmall
                                   (ite (= diff4 #b0001)
                                     ((_ extract 3 0)
                                      (bvashr
                                        (bvadd ((_ sign_extend 1) msmall)
                                               ((_ sign_extend 1) bias_signed4))
                                        #b00001))
                                     (ite (= diff4 #b0010)
                                       ((_ extract 3 0)
                                        (bvashr
                                          (bvadd ((_ sign_extend 1) msmall)
                                                 ((_ sign_extend 1) bias_signed4))
                                          #b00010))
                                       (ite (= diff4 #b0011)
                                         ((_ extract 3 0)
                                          (bvashr
                                            (bvadd ((_ sign_extend 1) msmall)
                                                   ((_ sign_extend 1) bias_signed4))
                                            #b00011))
                                         #b0000)))))))
                          (let ((raw5 (bvadd ((_ sign_extend 1) mbig) ((_ sign_extend 1) aligned_small4))))
                            (let ((abs5 (ite (bvslt raw5 #b00000) (bvneg raw5) raw5)))
                              (let ((is_zero (= raw5 #b00000)))
                                (let ((is_b4 (= ((_ extract 4 4) abs5) #b1)))
                                  (let ((is_b3 (= ((_ extract 3 3) abs5) #b1)))
                                    (let ((is_b2 (= ((_ extract 2 2) abs5) #b1)))
                                      (let ((is_b1 (= ((_ extract 1 1) abs5) #b1)))
                                        (let ((shifted5
                                               (ite is_zero raw5
                                                 (ite is_b4 (bvashr raw5 #b00010)
                                                   (ite is_b3 (bvashr raw5 #b00001)
                                                     (ite is_b2 raw5
                                                       (ite is_b1 (bvshl raw5 #b00001)
                                                         (bvshl raw5 #b00010))))))))
                                          (let ((adj5
                                                 (ite is_zero #b00000
                                                   (ite is_b4 #b00010
                                                     (ite is_b3 #b00001
                                                       (ite is_b2 #b00000
                                                         (ite is_b1 #b11111 #b11110)))))))
                                            (let ((exp_adj5 (bvadd ((_ sign_extend 1) ebig) adj5)))
                                              (let ((exp_clamp5
                                                     (ite (bvsgt exp_adj5 #b00111) #b00111
                                                       (ite (bvslt exp_adj5 #b11000) #b11000 exp_adj5))))
                                                (let ((mant4
                                                       (ite is_zero #b0000
                                                         (ite (bvsgt shifted5 #b00111) #b0111
                                                           (ite (bvslt shifted5 #b11000) #b1000
                                                             ((_ extract 3 0) shifted5))))))
                                                  (let ((exp4 (ite is_zero #b0000 ((_ extract 3 0) exp_clamp5))))
                                                    (concat mant4 exp4))))))))))))))))))))))))
      )
    )
  )
