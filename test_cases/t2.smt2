;; Example 9.17

(set-logic QF_UF)

(declare-sort MySort 0)
(declare-fun a () MySort)
(declare-fun b () MySort)
(declare-fun f (MySort) MySort)

(assert
    (and
         (= (f (f (f a))) a)
         (= (f (f (f (f (f a))))) a)
         (not (= (f a) a))
    )
)

(check-sat)

