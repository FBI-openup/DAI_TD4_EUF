;; Example 9.16

(set-logic QF_UF)

(declare-sort MySort 0)
(declare-fun a () MySort)
(declare-fun b () MySort)
(declare-fun f (MySort MySort) MySort)

(assert
    (and
         (= (f a b) a)
         (not (= (f (f a b) b) a))
    )
)

(check-sat)