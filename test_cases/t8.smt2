(set-logic QF_UF)

(declare-sort MySortA 0)
(declare-fun a () MySortA)
(declare-fun b () MySortA)
(declare-fun c () MySortA)
(declare-fun d () MySortA)

(declare-fun f (MySortA) MySortA)
(declare-fun g (MySortA) MySortA)
(declare-fun h (MySortA MySortA MySortA) MySortA)

(assert
    (and
      (= a b)
      (= (f b) (g a))
      (= (f (g a)) (f (g b)))


;;      (not (= (f a) b))
;;      (not (= (f a) c))
      (not (= (f b) (g b)))
;;      (not (= (f c) (f a)))
    )
)

(check-sat)

