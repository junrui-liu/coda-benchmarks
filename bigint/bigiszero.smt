; Lemma BigIsZero_obligation7: forall (k : nat) (xs : (list F)) (i : nat) (x : F) (ise : F) (v : F), ((k <= C.k) /\ True) -> Forall (fun x7 => True) xs -> ((length xs) = k) -> (i < k) -> (((^ x) <= i) /\ ((((^ x) = i) -> (forall (bie_j:nat), 0%nat <= bie_j < i -> ((xs!bie_j) = 0%F))) /\ (~(((^ x) = i)) -> (exists (bie_j:nat), 0%nat <= bie_j < i /\ ~(((xs!bie_j) = 0%F))))))


; assumes a function toZ that converts a field element into an integer

(declare-const (k Int))
(declare-const xs (Array Int F))
(declare-const x F)
(declare-const ise F)
(declare-const v F)

(assert (<= 0 k))
(assert (<= k 254)) ; 254 = bit width of the prime
(assert (= (length xs) k))
(assert (< i k))

(assert
    (and
        (<= (toZ x) i)
        (=> (= (toZ x) i)
        (forall ((bie_j Int)
            (=> (and (<= 0 bie_j) (< bie_j i))
            (= (select xs bie_j) 0)))))
        (=> (not (= (toZ x) i))
        (exists ((bie_j Int)
            (and (<= 0 bie_j) (< bie_j i)) (not (= (select xs bie_j) 0)))))))

; -> (((ise = 0%F) \/ (ise = 1%F)) /\ (((ise = 1%F) -> ((xs!i) = 0%F)) /\ ((ise = 0%F) -> ~((xs!i) = 0%F)))) -> True -> 

(assert
  (and
    (or (= ise 0) (= ise 1))
    (=> (= ise 1) (= (select xs i) 0))
    (=> (= ise 0) (not (= (select xs i) 0)))))


; ((v = (x + ise)%F) -> (((^ v) <= (i + 1%nat)%nat) /\ ((((^ v) = (i + 1%nat)%nat) -> (forall (bie_j:nat), 0%nat <= bie_j < (i + 1%nat)%nat -> ((xs!bie_j) = 0%F))) /\ (~(((^ v) = (i + 1%nat)%nat)) -> (exists (bie_j:nat), 0%nat <= bie_j < (i + 1%nat)%nat /\ ~(((xs!bie_j) = 0%F))))))).

(assert (= v (+ x ise)))
(assert
    (not 
    (and
        (<= (toZ v) (+ i 1))
        (=> (= (toZ v) (+ i 1))
            (forall ((bie_j Int)
                (=> (and (<= 0 bie_j) (< bie_j (+ i 1)))
                (= (select xs bie_j) 0)))))
        (=> (not (= (toZ x) (+ i 1)))
            (exists ((bie_j Int)
                (and (<= 0 bie_j) (< bie_j (+ i 1)) (not (= (select xs bie_j) 0)))))))))

