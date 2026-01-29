(set-logic QF_UF)

(declare-sort MySort 0)
(declare-fun a () MySort)
(declare-fun b () MySort)
(declare-fun f (MySort) MySort)

(declare-fun g (MySort MySort) MySort)

(assert
    (and
      (= (f a) (f (g a b)))
      (= (g a a) (f b))
      (not (= (f b) (f a)))
      (= (g a a) (f (g a b)))
    )
)

(check-sat)

