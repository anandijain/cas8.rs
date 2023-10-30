(* combinators *)
(Set skrules 
    (List 
        (Rule (((s (Pattern x (Blank))) (Pattern y (Blank))) (Pattern z (Blank))) ((x z) (y z))) 
        (Rule ((k (Pattern x (Blank))) (Pattern y (Blank))) 
        x)))

(Set succ (s ((s (k s)) k)))
(SetDelayed (skn (Pattern n (Blank Integer))) (Nest succ (s k) n))

(Set skplus ((s (k s)) (s (k ((s (k s)) k)))))
(Set sktimes ((s (k s)) k))
(Set skpow ((s (k (s ((s k) k)))) k))

(* CA *)
(* (Set (rule30 (Pattern p (Blank)) (Pattern q (Blank)) (Pattern r (Blank))) (Xor p (Or q r))) *)
(Set (rule30 (Pattern p (Blank)) (Pattern q (Blank)) (Pattern r (Blank))) (Xor p (Or q r)))

(SetDelayed (rule30 
    (List 
        (Pattern p (Blank)) 
        (Pattern q (Blank)) 
        (Pattern r (Blank)))) 
    (Xor p (Or q r)))

(* (setd (pad_zero (Pattern xs (Blank List))) (Join (List 0) xs (List 0)))
(setd (idxs (Pattern n (Blank Integer))) (Table (Plus i n_) (List n_ 0 n))) *)

(SetDelayed (padval 
    (Pattern xs (Blank List))
    (Pattern val (Blank)))
    (Join (List val) xs (List val)))

(SetDelayed (lilpartition3
    (Pattern xs (Blank List)))
    (Table (List (Part xs i) (Part xs (Plus i 1)) (Part xs (Plus i 2))) (List i (Plus (Length xs) -2))
    ))

(SetDelayed (foo (Pattern xs (Blank List)))
    (Map rule30 (lilpartition3 (padval xs False))))

(Set u0 (ReplaceAll (List 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (List (Rule 0 False) (Rule 1 True))))

(Set ls (ReplaceAll (NestList foo u0 20) (List (Rule False 0) (Rule True 1))))

(* rendering *)
(Set ps (ReplaceAll ls (List (Rule 0 (List 1. 1. 1.)) (Rule 1 (List 0. 0. 0.)))))
(Export "rule_30.svg" ps)
