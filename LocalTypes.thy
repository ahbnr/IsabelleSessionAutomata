theory LocalTypes
  imports Main
begin

(* The session automata forget about the caller. Is this still valid?
   (Probably because of type checking
*)

datatype Method = m1 | m2 | m3
datatype Future = f | f' | f''

datatype LocalType =
      InvocationRecv Future Method ("\<questiondown>_ _" [1000, 61] 61)
    | Reaction Future ("React(_)" 70)
    | Concat LocalType LocalType ("_;; _" [60, 61] 60)
    | Repeat LocalType ("_ *" 70)
    | Branching "LocalType list" ("\<Oplus> _" 70)

definition
  exampleType :: LocalType where
  "exampleType \<equiv> \<questiondown>f m1 ;; \<questiondown>f'' m3 ;; React(f)"

end