(SetDelayed (D (Pattern c (Blank Integer)) (Pattern x (Blank Symbol))) 0)
(SetDelayed (D (Pattern c (Blank Real)) (Pattern x (Blank Symbol))) 0)

(SetDelayed (D (Pattern x (Blank Symbol)) (Pattern x (Blank Symbol))) 1)

(SetDelayed (D (Times (Pattern a (Blank Integer)) (Pattern x (Blank Symbol))) (Pattern x (Blank Symbol))) a)
(SetDelayed (D (Times (Pattern a (Blank Real)) (Pattern x (Blank Symbol))) (Pattern x (Blank Symbol))) a)

(SetDelayed (D (Times (Pattern x (Blank Symbol)) (Pattern a (Blank Integer))) (Pattern x (Blank Symbol))) a)
(SetDelayed (D (Times (Pattern x (Blank Symbol)) (Pattern a (Blank Real))) (Pattern x (Blank Symbol))) a)

(SetDelayed (D (Plus 
        (Pattern expr1 (Blank)) 
        (Pattern expr2 (Blank))) 
        (Pattern x (Blank Symbol))) 
        (Plus (D expr1 x) (D expr2 x))) 

(SetDelayed (D (Times 
        (Pattern expr1 (Blank)) 
        (Pattern expr2 (Blank))) 
        (Pattern x (Blank Symbol))) 
        (Plus (Times expr1 (D expr2 x)) (Times expr2 (D expr1 x))))

(SetDelayed (D (Power 
        (Pattern expr1 (Blank)) 
        (Pattern n (Blank Integer))) 
        (Pattern x (Blank Symbol))) 
        (Times n (Power expr1 (Plus n -1)) (D expr1 x)))

(SetDelayed (D (Exp 
        (Pattern expr (Blank))) 
        (Pattern x (Blank Symbol))) 
        (Times (D expr x) (Exp expr)))

(SetDelayed (D (Sin 
        (Pattern expr (Blank))) 
        (Pattern x (Blank Symbol))) 
        (Times (D expr x) (Cos expr)))


(SetDelayed (D (Cos (Pattern expr (Blank))) (Pattern x (Blank Symbol))) (Times (Times -1 (D expr x)) (Sin expr)))

(* Todo make (D x y) -> 0 work *)