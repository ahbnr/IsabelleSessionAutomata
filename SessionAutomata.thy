theory SessionAutomata
  imports Main HOL.String
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

datatype State = q nat ("q`_")
datatype Register = Register nat ("r`_")
datatype TransitionVerb = invocREv Future Method Register | reactEv Future Register | \<epsilon>
type_synonym Transition = "State \<times> TransitionVerb \<times> State"

type_synonym SessionAutomaton = "State list \<times> State \<times> Transition list \<times> State list"

record Cache =
  nextFreeState :: State
  nextFreeRegister :: Register
  assignedRegisters :: "Future \<Rightarrow> Register option"

definition
  initialCache :: Cache where
  "initialCache \<equiv> \<lparr>nextFreeState=q`0, nextFreeRegister=r`0, assignedRegisters=\<lambda>x.(None)\<rparr>"

fun concatAutomata :: "SessionAutomaton \<Rightarrow> State list \<Rightarrow> SessionAutomaton \<Rightarrow> SessionAutomaton" where
  "concatAutomata (Q1, q01, \<Phi>1, F1) glueStates (Q2, q02, \<Phi>2, F2) =
      (
        List.union Q1 (List.remove1 q02 Q2), \<comment> \<open>we remove q02, the glue states of the first automaton will take its place\<close>
        q01,
        List.union
          (List.union \<Phi>1 (filter (\<lambda>(q1,verb,q2). q1 \<noteq> q02 \<and> q2 \<noteq> q02) \<Phi>2)) \<comment> \<open>Same goes for the transition relation\<close>
          [(qG, verb, qN). qG <- glueStates, (q02', verb, qN) <- \<Phi>2, q02' = q02],
        List.union F1 F2
      )"

fun genAutomaton :: "LocalType \<Rightarrow> Cache \<Rightarrow> (SessionAutomaton \<times> Cache)" where
    "genAutomaton (\<questiondown>fut method) \<lparr>nextFreeState=q`n, nextFreeRegister=r`nextReg, assignedRegisters=R\<rparr> = (
       let
         i = n + 1;
         ii = n + 2
       in (
         (
           [q`i, q`ii],
           q`i,
           [(q`i, invocREv fut method r`nextReg, q`ii)],
           [q`ii]
         ),
         \<lparr>nextFreeState=q`(n+3), nextFreeRegister=r`(nextReg+1), assignedRegisters=R(fut:=Some (r`nextReg))\<rparr>
       )
     )"
  | "genAutomaton (React(fut)) \<lparr>nextFreeState=q`n, nextFreeRegister=r`nextReg, assignedRegisters=R\<rparr> = (
      let
         i = n + 1;
         ii = n + 2;
         saveRegister =
           case R fut of
               Some register \<Rightarrow> register
             | _             \<Rightarrow> r`nextReg;
         updatedR = R(fut:=Some saveRegister);
         updatedFreeRegister =
           case R fut of
               Some _ \<Rightarrow> r`nextReg
             | _      \<Rightarrow> r`(nextReg+1)
      in (
        (
          [q`i, q`ii],
          q`i,
          [(q`i, reactEv fut saveRegister, q`ii)],
          [q`ii]
        ),
        \<lparr>nextFreeState=(q`(n+3)), nextFreeRegister=updatedFreeRegister, assignedRegisters=updatedR\<rparr>
      )
    )"
  | "genAutomaton (t1 ;; t2) c = (
      let
        ((Q1, q01, \<Phi>1, F1), c')  = genAutomaton t1 c;
        (a2, c'') = genAutomaton t2 c'
      in \<comment> \<open>(
        List.union Q1 (List.remove1 q02 Q2), \<comment> \<open>we remove q02, the final states of the first automaton will take its place\<close>
        q01,
        List.union
          (List.union \<Phi>1 (filter (\<lambda>(q1,verb,q2). q1 \<noteq> q02 \<and> q2 \<noteq> q02) \<Phi>2)) \<comment> \<open>Same goes for the transition relation\<close>
          [(f1, verb, qN). f1 <- F1, (q02', verb, qN) <- \<Phi>2, q02' = q02],
        F2                                           
      ), c'')\<close>
        (concatAutomata (Q1, q01, \<Phi>1, []) F1 a2, c'')
    )"
  | "genAutomaton (t*) c = (
      let
        ((Q, q0, \<Phi>', F), c') = genAutomaton t c
      in ((
        Q,
        q0,
        List.union \<Phi>' [(f1, verb, q1). (q0', verb, q1) <- \<Phi>', f1 <- F, q0' = q0],
        List.union [q0] F
      ), c')
    )"
  | "genAutomaton (\<Oplus> []) \<lparr>nextFreeState=q`n, nextFreeRegister=r`nextReg, assignedRegisters=R\<rparr> =
      (([q`n], q`n, [], []), \<lparr>nextFreeState=q`(n+1), nextFreeRegister=r`nextReg, assignedRegisters=R\<rparr>)
      \<comment> \<open>TODO: Discuss final state\<close>
    "
  | "genAutomaton (\<Oplus> (t#ts)) c = (
      let
        ((Q, q0, \<Phi>', F), c') = genAutomaton t c;
        (remainderAutomaton, c'') = genAutomaton (\<Oplus> ts) c'
      in
        (concatAutomata (Q, q0, \<Phi>', F) [q0] remainderAutomaton, c'')
    )"

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

definition
  testAutomaton1 :: SessionAutomaton where
  "testAutomaton1 \<equiv> fst (genAutomaton ((\<questiondown> f m1 ;; \<questiondown>f'' m3 ;; React(f))*) initialCache)"

definition
  testAutomaton2 :: SessionAutomaton where
  "testAutomaton2 \<equiv> fst (genAutomaton (\<Oplus>[((\<questiondown> f m1 ;; \<questiondown>f'' m3 ;; React(f))*), (\<questiondown> f' m2)]) initialCache)"

value "genGraphViz testAutomaton1"
value "genGraphViz testAutomaton2"

end