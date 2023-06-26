; Lemma IsEqual_obligation3: forall (x : F) (y : F) (v : F), True -> True -> True -> ((((v = 0%F) \/ (v = 1%F)) /\ (((v = 1%F) -> ((x - y)%F = 0%F)) /\ ((v = 0%F) -> ~((x - y)%F = 0%F)))) -> (((v = 0%F) \/ (v = 1%F)) /\ (((v = 1%F) -> (x = y)) /\ ((v = 0%F) -> ~(x = y))))).

(declare-const (x F))
(declare-const (y F))
(declare-const (v F))
(assert (or (= x 0) (= x 1)))
(assert (or (= y 0) (= y 1)))
(assert
  (and
    (or (= v 0) (= v 1))
    (=> (= v 1) (= (- x y) 0))
    (=> (= v 0) (not (= (- x y) 0)))))
(assert
  (and
    (or (= v 0) (= v 1))
    (=> (= v 1) (= x y))
    (=> (= v 0) (not (= x y)))))