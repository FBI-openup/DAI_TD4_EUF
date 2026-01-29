;; Example 9.16

(set-logic QF_UF)

(declare-sort MySort 0)
(declare-fun a () MySort)

(assert
  (= a a)
)

(check-sat)