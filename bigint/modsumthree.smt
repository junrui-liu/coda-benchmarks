; Lemma ModSumThree

; assumes toZ that converts a field element into an integer
; assumes mapi :: forall a b. (int -> a -> b) -> a list -> b list
; assumes sum :: forall a. a list -> int

(declare-const (k Int))

(assert (<= 0 k))
(assert (<= k 254)) ; 254 = bit width of the prime
(declare-const (n Int))
(declare-const (s F))
(declare-const (carry F))
(declare-const (a F))
(declare-const (b F))
(declare-const (c F))
(declare-const (bits (Array Int F)))
(assert (= (length bits) (+ n 1)))
(assert (forall ((i Int)
            (=> (and (<= 0 i) (< i (length bits))))
            (or (= (select xs i) 0) (= (select xs i) 1)))))
(assert (< (toZ a) (pow 2 n)))
(assert (< (toZ b) (pow 2 n)))
(assert (< (toZ c) (pow 2 n)))
(assert (= (+ a b c)
    (sum (mapi (lambda ((i Int) (bit F)) (* b (pow 2 i))(bits)) bits))))
(assert (= s (slice bits 0 n)))
(assert (= carry (nth bits n)))
(assert (not (and 
    (< (toZ s) (pow 2 n)))
    (forall ((i Int)
            (=> (and (<= 0 i) (< i (length s))))
            (or (= (select xs i) 0) (= (select xs i) 1))))
    (or (= carry 0) (= carry 1))
    (= (+ s (* c (pow 2 n))))))