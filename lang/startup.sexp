(* bool *)
(Set (And True True) True)
(Set (And True False) False)
(Set (And False True) False)
(Set (And False False) False)

(Set (Or True True) True)
(Set (Or True False) True)
(Set (Or False True) True)
(Set (Or False False) False)

(Set (Xor True True) False)
(Set (Xor True False) True)
(Set (Xor False True) True)
(Set (Xor False False) False)

(Set (Nand True True) False)
(Set (Nand True False) True)
(Set (Nand False True) True)
(Set (Nand False False) True)

(Set (Not True) False)
(Set (Not False) True)

(Set (Not (Not (Pattern x (Blank)))) x)

(SetDelayed (If True (Pattern x (Blank)) (Pattern y (Blank))) x)
(SetDelayed (If False (Pattern x (Blank)) (Pattern y (Blank))) y)

(SetDelayed (If True (Pattern x (Blank))) x)
(SetDelayed (If False (Pattern x (Blank))) Null)

(SetDelayed (If True (Pattern x (Blank)) (Pattern y (Blank)) (Pattern z (Blank))) x)
(SetDelayed (If False (Pattern x (Blank)) (Pattern y (Blank)) (Pattern z (Blank))) y)
(SetDelayed (If (Pattern t (Blank)) (Pattern x (Blank)) (Pattern y (Blank)) (Pattern z (Blank))) z)

(SetDelayed (Nest (Pattern f (Blank)) (Pattern x (Blank)) 0) x)
(SetDelayed (Nest (Pattern f (Blank)) (Pattern x (Blank)) (Pattern n (Blank Integer))) (f (Nest f x (Plus n -1))))

(SetDelayed (First (List (Pattern x (Blank)) (Pattern rest (BlankNullSequence)))) x)
(SetDelayed (First (Pattern xs (BlankNullSequence))) (First (List xs)))
(SetDelayed (Rest (List (Blank) (Pattern rest (BlankNullSequence)))) (List rest))
(SetDelayed (Rest (Pattern xs (BlankNullSequence))) (Rest (List xs)))

(SetDelayed (Plus) 0)
(SetDelayed (Plus (Pattern x (Blank))) x)

(SetDelayed (Times) 1)
(SetDelayed (Times (Pattern x (Blank))) x)
