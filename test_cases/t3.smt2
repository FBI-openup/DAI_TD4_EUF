(set-logic QF_UF)

(declare-sort MySort 0)
(declare-fun a () MySort)
(declare-fun b () MySort)
(declare-fun f (MySort) MySort)

(declare-fun g (MySort MySort) MySort)

(assert
    (and

;;    f(a) = f(g(a,b))
      (= (f a) (f (g a b)))
;;    g(a,a) = f(b)
      (= (g a a) (f b))
;;    not f(b) = f(a)
      (not (= (f b) (f a)))
    )
)

(check-sat)

