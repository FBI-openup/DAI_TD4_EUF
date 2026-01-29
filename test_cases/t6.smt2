(set-logic QF_UF)

(declare-sort MySortA 0)
(declare-fun a () MySortA)
(declare-fun b () MySortA)
(declare-fun f (MySortA) MySortA)

(assert
    (and
      (= a b)
      (= (f (f (f a))) b)
      (not (= (f (f (f b))) (f (f b))))
      (not (= (f a) b))
    )
)

(check-sat)

