; Lemma Not_obligation6: forall (_in : F) (v : F), ((_in = 0%F) \/ (_in = 1%F)) -> True -> ((v = ((_in + 1%F)%F - (2%F * _in)%F)%F) -> (((v = 0%F) \/ (v = 1%F)) /\ (((v = 1%F) -> (f_not _in)) /\ ((v = 0%F) -> ~(f_not _in))))).

(declare-const (_in F))
(declare-const (v F))
(assert (or (= _in 0) (= _in 1)))
(assert (= v (- (+ _in 1) (* 2 _in))))
(define-fun f_to_bool (x F) F (= x 1))
(assert
  (and
    (or (= v 0) (= v 1))
    (=> (= v 1) (not (f_to_bool _in)))
    (=> (= v 0) (not (not (f_to_bool _in))))))