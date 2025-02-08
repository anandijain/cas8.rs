(Set (Attributes HoldPattern) (List HoldAll))
(Set (Attributes Attributes) (List HoldAll))
(Set (Attributes RuleDelayed) (List HoldRest SequenceHold))
(Set (Attributes Set) (List HoldFirst SequenceHold))
(Set (Attributes DownValues) (List HoldAll))

(Set (Attributes SetDelayed) (List HoldAll SequenceHold))
(Set (Attributes Clear) (List HoldAll))
(Set (Attributes Hold) (List HoldAll))
(Set (Attributes Pattern) (List HoldFirst))
(* (Set (Attributes PatternTest) (List HoldRest)) *)

(* (Set (Attributes True) (List locked protected))
(Set (Attributes False) (List locked protected)) *)

(Set (Attributes Rule) (List SequenceHold))
(Set (Attributes Table) (List HoldAll))
(Set (Attributes Timing) (List HoldAll))

(* Note the only attributes in these that are acutally supported is Flat  *)
(Set (Attributes Plus) (List Flat Listable NumericFunction OneIdentity Orderless Protected))
(Set (Attributes Times) (List Flat Listable NumericFunction OneIdentity Orderless Protected))
(Set (Attributes Join) (List Flat))
(Set (Attributes Or) (List Flat))
(Set (Attributes And) (List Flat))
(Set (Attributes Xor) (List Flat Orderless))

(Set (Attributes Function) (List HoldAll))
