; Lemma BigAddModP_obligation30: 

(declare-const (Ck Int))
(assert (<= 0 Ck 256))

; forall 
;   (n : nat) 
(declare-const (n Int))
(assert (<= 0 n))
;   (k : nat) 
(declare-const (k Int))
(assert (<= 0 k))
;   (a : (list F)) 
(declare-const a (Array Int F))
;   (b : (list F)) 
(declare-const b (Array Int F))
;   (p : (list F)) 
(declare-const p (Array Int F))
;   (add : (list F)) 
(declare-const add (Array Int F))
;   (lt : F) 
(declare-const lt (Array Int F))
;   (p' : (list F)) 
(declare-const p' (Array Int F))
;   (sub_uf : ((list F) * F)) 
;   (uf : F) 
;   (sub : (list F)) 
;   (_u0 : ((list F) * F)) 
(declare-const sub (Array Int F))
(declare-const uf F)
;   (v : (list F)), 
(declare-const v (Array Int F))


; ((n <= (C.k - 2%nat)%Z) /\ ((1%nat <= n) /\ True)) -> 
(assert (<= n (- Ck 2)))
(assert (<= 1 n))

; (1%nat <= k) -> 
(assert (<= 1 k))
; Forall (fun x137 => ((^ x137) <= ((2%nat ^ n)%Z - 1%nat)%Z)) a -> 
; (((as_le n a) <= ((as_le n p) - 1%nat)%Z) /\ ((length a) = k)) -> 
(assert ((forall ((j Int)) (=> (<= 0 j k)
            (<= (toZ (select a j)) (- (^ 2 n) 1))))))
(assert (<= (as_le n a) (- (as_le n p) 1)))
(assert (= (length a) k))
; Forall (fun x138 => ((^ x138) <= ((2%nat ^ n)%Z - 1%nat)%Z)) b -> 
; (((as_le n b) <= ((as_le n p) - 1%nat)%Z) /\ ((length b) = k)) -> 
(assert ((forall ((j Int)) (=> (<= 0 j k)
            (<= (toZ (select b j)) (- (^ 2 n) 1))))))
(assert (<= (as_le n b) (- (as_le n p) 1)))
(assert (= (length b) k))
; Forall (fun x139 => ((^ x139) <= ((2%nat ^ n)%Z - 1%nat)%Z)) p -> 
; ((length p) = k) -> 
(assert ((forall ((j Int)) (=> (<= 0 j k)
            (<= (toZ (select p j)) (- (^ 2 n) 1))))))
(assert (= (length p) k))
; Forall (fun x140 => ((^ x140) <= ((2%nat ^ n)%Z - 1%nat)%Z)) add -> 
; (((length add) = (k + 1%nat)%nat) /\ 
(assert ((forall ((j Int)) (=> (<= 0 j (+ k 1))
            (<= (toZ (select add j)) (- (^ 2 n) 1))))))
(assert (= (length add) (+ k 1)))
; ((as_le n add) = ((as_le n a) + (as_le n b))%Z)) -> 
(assert (= (as_le n add) (+ (as_le n a) (as_le n b))))
; (((lt = 0%F) \/ (lt = 1%F)) /\ 
(assert (|| (= lt 0) (= lt 1)))
; (((lt = 1%F) -> ((as_le n add) < (as_le n (p ++ (0%F :: nil))))) /\
(assert (=> (= lt 1) (< (as_le n add) (as_le n (concat p (cons 0 nil))))))
; ((lt = 0%F) -> ~((as_le n add) < (as_le n (p ++ (0%F :: nil))))))) -> 
(assert (=> (= lt 0) (not (< (as_le n add) (as_le n (concat p (cons 0 nil)))))))
; Forall (fun x141 => True) p' -> 
; ((forall (scale_j:nat), 0%nat <= scale_j < (k + 1%nat)%nat -> 
; ((p'!scale_j) = ((1%F - lt)%F * ((p ++ (0%F :: nil))!scale_j))%F)) /\ 
(assert ((forall ((j Int))
            (=> (<= 0 j (+ k 1)) (= (select p' j) (* (- 1 lt) (select (concat p (cons 0 nil)) j)))))))
; ((length p') = (k + 1%nat)%nat)) -> 
(assert (= (length p') (+ k 1)))
; match sub_uf with (x143,x144) => Forall (fun x142 => ((^ x142) <= ((2%nat ^ n)%Z - 1%nat)%Z)) x143 end -> 
; match sub_uf with (x143,x144) => ((length x143) = (k + 1%nat)%nat) end -> 
(assert ((forall ((j Int)) (=> (<= 0 j (+ k 1))
            (<= (toZ (select sub j)) (- (^ 2 n) 1))))))
(assert (<= (as_le sub b) (- (as_le n p) 1)))
(assert (= (length sub) (+ k 1)))
; match sub_uf with (x143,x144) => 
; (((x144 = 0%F) \/ (x144 = 1%F)) /\ 
; (((x144 = 1%F) -> ((as_le n add) < (as_le n p'))) /\ 
; ((x144 = 0%F) -> ~((as_le n add) < (as_le n p'))))) end -> 
(assert (|| (= uf 0) (= uf 1)))
(assert (=> (= uf 1) (< (as_le n add) (as_le n p'))))
(assert (=> (= uf 0) (not (< (as_le n add) (as_le n p')))))
; match sub_uf with (x143,x144) => 
; ((as_le n x143) = (((as_le n add) - (as_le n p'))%Z + ((2%nat ^ (n * (k + 1%nat)%nat)%Z)%Z * (^ x144))%Z)%Z) end -> 
(assert (= (as_le n sub) (+ (- (as_le n add) (as_le n p')) (^ 2 (* n (+ k 1))))))
; ((((uf = 0%F) \/ (uf = 1%F)) /\ (((uf = 1%F) -> ((as_le n add) < (as_le n p'))) /\ ((uf = 0%F) -> ~((as_le n add) < (as_le n p'))))) /\ (uf = (snd sub_uf))) -> Forall (fun x145 => ((^ x145) <= ((2%nat ^ n)%Z - 1%nat)%Z)) sub -> (((length sub) = (k + 1%nat)%nat) /\ (sub = (fst sub_uf))) -> 
; match _u0 with (x147,x148) => Forall (fun x146 => True) x147 end -> 
; match _u0 with (x147,x148) => True end -> 
; match _u0 with (x147,x148) => True end -> 
; match _u0 with (x147,x148) => (((as_le n sub) = (((as_le n add) - (as_le n p'))%Z + ((2%nat ^ (n * (k + 1%nat)%nat)%Z)%Z * (^ uf))%Z)%Z) /\ (sub_uf = sub_uf)) end -> 
; Forall (fun x149 => True) v -> 
; True ->
; (((v = (sub[:k])) /\ ((length v) = k)) -> 
(assert (= v (firstn (sub k))))
(assert (= (length v) k))
; ((((as_le n v) = (((as_le n a) + (as_le n b))%Z mod (as_le n p))%Z) /\ ((length v) = k)) /\ (forall (i0:nat), 0%nat <= i0 < (length v) -> ((^ (v!i0)) <= ((2%nat ^ n)%Z - 1%nat)%Z)))).
(assert (not 
    (and
        (= (as_le n v) (mod (+ (as_le n a) (as_le n b)) (as_le n p)))
        (= (length v) k)
        (assert ((forall ((j Int)) (=> (<= 0 j k)
            (<= (toZ (select v j)) (- (^ 2 n) 1))))))

    )))