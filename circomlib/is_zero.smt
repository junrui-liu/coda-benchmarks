; Lemma IsZero_obligation8: forall (_in : F) (inv : F) (out : F) (u1 : unit) (u2 : unit) (v : F), True -> True -> True -> (out = (1%F + (0%F - (_in * inv)%F)%F)%F) -> ((_in * out)%F = 0%F) -> True -> ((v = out) -> (((v = 0%F) \/ (v = 1%F)) /\ (((v = 1%F) -> (_in = 0%F)) /\ ((v = 0%F) -> ~(_in = 0%F))))).

(declare-const (_in F))
(declare-const (inv F))
(declare-const (out F))
(declare-const (v F))
(assert (= out (+ 1 (- 0 (* _in inv)))))
(assert (= (* _in out) 0))
(assert (= v out))
(assert
  (and
    (or (= v 0) (= v 1))
    (=> (= v 1) (= _in 0))
    (=> (= v 0) (not (= _in 0)))))