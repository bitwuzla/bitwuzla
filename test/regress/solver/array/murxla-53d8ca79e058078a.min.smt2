(declare-const i Bool)
(declare-const AAA (Array Bool (Array Bool (Array Bool Bool))))
(set-info :status sat)
(check-sat-assuming ((select (select (select (store AAA i (select AAA i)) true) false) false) (= AAA (store AAA i (select AAA i))) (= AAA (store AAA i (select AAA false)))))
