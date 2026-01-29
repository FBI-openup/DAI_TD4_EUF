(set-logic QF_UF)

(declare-sort MySort 0)
(declare-fun x () MySort)
(declare-fun y () MySort)
(declare-fun z () MySort)
(declare-fun f (MySort MySort) MySort)
(declare-fun g (MySort) MySort)

(assert
    (and
         (= (f x y) x)
;;         (= (g y) (g x))
         (= (f (f x y) y) z)
         (not (= (g x) (g z)))
    )
)

(check-sat)