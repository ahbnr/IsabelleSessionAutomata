theory GraphVizPrinter
  imports Main SessionAutomata
begin

(* GraphViz generator *)

value "append ''lol'' ''nom''"

(* https://stackoverflow.com/a/23865253 *)
fun string_of_nat :: "nat \<Rightarrow> string"
where
  "string_of_nat n = (if n < 10 then [char_of (48 + n)] else 
     string_of_nat (n div 10) @ [char_of (48 + (n mod 10))])"

primrec stringifyState :: "State \<Rightarrow> string" where
  "stringifyState (q`n) = ''q'' @ (string_of_nat n)"

primrec stringifyRegister :: "Register \<Rightarrow> string" where
  "stringifyRegister (r`n) = ''r'' @ (string_of_nat n)"

fun stringifyStates :: "State list \<Rightarrow> string" where
    "stringifyStates (state#qs) =
         (stringifyState state) 
       @ '' ''
       @ (stringifyStates qs)
    "
  | "stringifyStates [] = '' ''"

primrec stringifyMethod :: "Method \<Rightarrow> string" where
    "stringifyMethod m1 = ''m1''"
  | "stringifyMethod m2 = ''m2''"
  | "stringifyMethod m3 = ''m3''"

primrec stringifyFuture :: "Future \<Rightarrow> string" where
    "stringifyFuture f = ''f''"
  | "stringifyFuture f' = ''f`''"
  | "stringifyFuture f'' = ''f``''"

primrec stringifyLabel :: "TransitionVerb \<Rightarrow> string" where
    "stringifyLabel (invocREv fut method register) =
        ''\"invocREv ''
      @ (stringifyFuture fut)
      @ '' ''
      @ (stringifyMethod method)
      @ '' ''
      @ (stringifyRegister register)
      @ ''\"''
    "
  | "stringifyLabel (reactEv fut register) =
        ''\"reactEv ''
      @ (stringifyFuture fut)
      @ '' ''
      @ (stringifyRegister register)
      @ ''\"''
    "
  | "stringifyLabel (\<epsilon>) =''empty''"

fun stringifyTransitions :: "Transition list \<Rightarrow> string" where
    "stringifyTransitions ((q1, label, q2)#ts) =
        (stringifyState q1)
      @ '' -> ''
      @ (stringifyState q2)
      @ '' [label = ''
      @ (stringifyLabel label)
      @ '' ];\<newline>''
      @ (stringifyTransitions ts)
    "
  | "stringifyTransitions [] = ''''"

fun genGraphViz :: "SessionAutomaton \<Rightarrow> string" where
  "genGraphViz (Q, q0, \<Phi>', F) =
      ''digraph finite_state_machine {\<newline>node [shape = doublecircle]; ''
    @ (stringifyStates F)
    @ ''\<newline>node [shape = circle];\<newline>''
    @ (stringifyTransitions \<Phi>')
    @ ''}''"

value "genGraphViz testAutomaton1"
value "genGraphViz testAutomaton2"

end