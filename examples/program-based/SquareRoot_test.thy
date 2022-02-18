chapter {* Proof of concept for a monadic symbolic execution calculus for WHILE programs *}

theory SquareRoot_test
imports "MonadicPrograms" 
        "~~/src/HOL/Eisbach/Eisbach"
begin


section{* Re-visiting the squareroot program example *}

text\<open>The state is just a record; and the global variables correspond to fields in this
     record. This corresponds to typed, structured, non-aliasing states.
     Note that the types in the state can be arbitrary HOL-types - want to have
     sets of functions in a ghost-field ? No problem !
    \<close>

text\<open> The state of the square-root program looks like this : \<close>
record state = 
   tm    :: int
   i     :: int
   sqsum :: int
   a     :: int


(* TODO: automate this *)
text\<open> Some lemmas to reason about memory\<close>

lemma tm_simp : "tm (\<sigma>\<lparr>tm := t\<rparr>) = t" by simp
lemma tm_simp1 : "tm (\<sigma>\<lparr>sqsum := s\<rparr>) = tm \<sigma>" by simp
lemma tm_simp2 : "tm (\<sigma>\<lparr>i := s\<rparr>) = tm \<sigma>" by simp
lemma tm_simp3 : "tm (\<sigma>\<lparr>a := s\<rparr>) = tm \<sigma>" by simp
lemma sqsum_simp : "sqsum (\<sigma>\<lparr>sqsum := s\<rparr>) = s" by simp
lemma sqsum_simp1 : "sqsum (\<sigma>\<lparr>tm := t\<rparr>) = sqsum \<sigma>" by simp
lemma sqsum_simp2 : "sqsum (\<sigma>\<lparr>i := t\<rparr>) = sqsum \<sigma>" by simp
lemma sqsum_simp3 : "sqsum (\<sigma>\<lparr>a := t\<rparr>) = sqsum \<sigma>" by simp
lemma i_simp : "i (\<sigma>\<lparr>i := i'\<rparr>) = i'" by simp
lemma i_simp1 : "i (\<sigma>\<lparr>tm := i'\<rparr>) = i \<sigma>" by simp
lemma i_simp2 : "i (\<sigma>\<lparr>sqsum := i'\<rparr>) = i \<sigma>" by simp
lemma i_simp3 : "i (\<sigma>\<lparr>a := i'\<rparr>) = i \<sigma>" by simp
lemma a_simp : "a (\<sigma>\<lparr>a := a'\<rparr>) = a'" by simp
lemma a_simp1 : "a (\<sigma>\<lparr>tm := a'\<rparr>) = a \<sigma>" by simp
lemma a_simp2 : "a (\<sigma>\<lparr>sqsum := a'\<rparr>) = a \<sigma>" by simp
lemma a_simp3 : "a (\<sigma>\<lparr>i := a'\<rparr>) = a \<sigma>" by simp

lemmas memory_theory =
  tm_simp tm_simp1 tm_simp2 tm_simp3
  sqsum_simp sqsum_simp1 sqsum_simp2 sqsum_simp3
  i_simp i_simp1 i_simp2 i_simp3
  a_simp a_simp1 a_simp2 a_simp3


text\<open> We provide syntactic sugar via cartouches \<close>

consts syntax_assign :: "('a state_scheme \<Rightarrow> int) \<Rightarrow> int \<Rightarrow> term" (infix ":=" 60)

ML \<open>
  local
    fun app_sigma db tm = case tm of
        Const("SquareRoot_test.state.tm",_) => @{term tm} $ (Bound db)
      | Const("SquareRoot_test.state.i",_) => @{term i} $ (Bound db)
      | Const("SquareRoot_test.state.sqsum",_) => @{term sqsum} $ (Bound db)
      | Const("SquareRoot_test.state.a",_) => @{term a} $ (Bound db)
      | Const _ => tm
      | Free _ => tm
      | Var _ => tm
      | Bound _ => tm
      | Abs (_, _, tm') => app_sigma db tm'
      | t1 $ t2 => (app_sigma db t1) $ (app_sigma db t2)
      
    fun mk_assign t1 = case t1 of
        (Const("_type_constraint_",_)) $ (Const ("SquareRoot_test.state.tm",_))    => @{term tm_update}
      | (Const("_type_constraint_",_)) $ (Const ("SquareRoot_test.state.i",_))     => @{term i_update}
      | (Const("_type_constraint_",_)) $ (Const ("SquareRoot_test.state.sqsum",_)) => @{term sqsum_update}
      | (Const("_type_constraint_",_)) $ (Const ("SquareRoot_test.state.a",_))     => @{term a_update}
      | _ => raise TERM ("mk_assign", [t1])

    fun transform_term tm = case tm of
        Const("SquareRoot_test.syntax_assign",_) $ t1 $ t2 =>
          @{term "assign::('a state_scheme \<Rightarrow> 'a state_scheme) \<Rightarrow> 'a state_scheme \<Rightarrow> (unit \<times> 'a state_scheme) option"} $ (Abs ("\<sigma>", @{typ "'a state_scheme"}, ((mk_assign t1) $ (absdummy @{typ int} (app_sigma 1 t2)) $ (Bound 0))))
      | _ => Abs ("\<sigma>", @{typ "'a state_scheme"}, app_sigma 0 tm)

  in
    fun string_tr ctxt (content:(string * Position.T) -> (string * Position.T) list) (args:term list) : term =
      let fun err () = raise TERM ("string_tr", args) in
        (case args of
          [(Const (@{syntax_const "_constrain"}, _)) $ (Free (s, _)) $ p] =>
            (case Term_Position.decode_position p of
              SOME (pos, _) =>
              let val txt = Symbol_Pos.implode(content (s,pos))
                  val tm = Syntax.parse_term ctxt txt
              in
                Syntax.check_term ctxt (transform_term tm)
              end
            | NONE => err ())
        | _ => err ())
      end
  end
\<close>

syntax "_cartouche_string" :: "cartouche_position \<Rightarrow> string"  ("_")

parse_translation \<open>
  [(@{syntax_const "_cartouche_string"},
    K (string_tr @{context} ((Symbol_Pos.cartouche_content : Symbol_Pos.T list -> Symbol_Pos.T list)
                 o (Symbol_Pos.explode : string * Position.T -> Symbol_Pos.T list))))]
\<close>


text\<open> Now we run a symbolic execution. We run match-tactics (rather that simplify which would
      do the trick as well) in order to demonstrate an efficient way for symbolic execution in 
      Isabelle. \<close>

thm SquareRoot_test.state.simps



lemma 
assumes annotated_program: 
         "\<sigma>\<^sub>0 \<Turnstile> assume\<^sub>S\<^sub>E \<open>0 \<le> a\<close> ;- 
               \<open>tm := 1\<close> ;-
               \<open>sqsum := 1\<close> ;-
               \<open>i := 0\<close> ;-
               (while\<^sub>S\<^sub>E \<open>sqsum <= a\<close> do 
                  \<open>i := i+1\<close> ;-
                  \<open>tm := tm + 2\<close> ;-
                  \<open>sqsum := tm + sqsum\<close>
               od) ;-
               assert\<^sub>S\<^sub>E(\<lambda>\<sigma>. \<sigma>=\<sigma>\<^sub>R)"
shows "\<sigma>\<^sub>R \<Turnstile>assert\<^sub>S\<^sub>E \<open>i * i \<le> a \<and> a < (i + 1) * (i + 1)\<close> "
apply(insert annotated_program)
apply(tactic "ematch_tac @{context} [@{thm \"assume_E'\"}] 1")
apply(tactic "dmatch_tac @{context} [@{thm \"exec_assignD'\"}] 1")+
apply(tactic "dmatch_tac @{context} [@{thm \"exec_whileD\"}] 1")
apply(tactic "ematch_tac @{context} [@{thm \"if_SE_execE''\"}] 1")
apply(simp_all only: memory_theory Monads.bind_assoc')
apply(tactic "dmatch_tac @{context} [@{thm \"exec_assignD'\"}] 1")+
apply(tactic "dmatch_tac @{context} [@{thm \"exec_whileD\"}] 1")
apply(tactic "ematch_tac @{context} [@{thm \"if_SE_execE''\"}] 1")
apply(simp_all only: memory_theory Monads.bind_assoc')
apply(tactic "dmatch_tac @{context} [@{thm \"exec_assignD'\"}] 1")+
apply(tactic "dmatch_tac @{context} [@{thm \"exec_whileD\"}] 1")
apply(tactic "ematch_tac @{context} [@{thm \"if_SE_execE''\"}] 1")
apply(simp_all only: memory_theory Monads.bind_assoc')
 apply(tactic "dmatch_tac @{context} [@{thm \"exec_assignD'\"}] 1")+
apply(simp_all)
text\<open>Here are the test-statements explicit. \<close>

txt\<open>push away the test-hyp: postcond is true for programs with more than
    three loop traversals (criterion: all-paths(k). This reveals explicitly
    the three test-cases for  @{term "k<3"}. \<close>   
defer 1 

txt\<open>Instead of testing, we @{emph \<open>prove\<close>} that the test cases satisfy the
    post-condition for all @{term "k<3"} loop traversals and @{emph \<open>all\<close>} 
    positive inputs @{term "a \<sigma>"}.\<close>     
apply(auto  simp: assert_simp)
oops

(* TODO Better Syntax *) 

(* TODO Integrate this SE calculus into Monads *) 

(* TODO Develop a Hoare-Calculus with WP *) 

(* TODO Re-Develop IMP for Program testing *) 




txt\<open> We use Eisbach to automate the process.
      Necessary prerequisite: turning ematch and dmatch into a proper Isar Method. \<close>

(* TODO : this code shoud go to TestGen Method setups *)
ML{*
val _ =
  Theory.setup
   (Method.setup @{binding ematch}
      (Attrib.thms >> (fn rules => fn ctxt => METHOD (HEADGOAL o (K(ematch_tac ctxt rules)) ))) 
      "fast elimination matching" #>
    Method.setup @{binding dmatch}
      (Attrib.thms >> (fn rules => fn ctxt => METHOD (HEADGOAL o (K(dmatch_tac ctxt rules)) ))) 
       "fast destruction matching" #>
    Method.setup @{binding match}
      (Attrib.thms >> (fn rules => fn ctxt => METHOD (HEADGOAL o (K(match_tac ctxt rules)) )))
       "resolution based on fast matching")
*}

definition while_k :: "nat \<Rightarrow> ['\<sigma> \<Rightarrow> bool, (unit, '\<sigma>)MON\<^sub>S\<^sub>E] \<Rightarrow> (unit, '\<sigma>)MON\<^sub>S\<^sub>E"
where     "while_k _ \<equiv> while_SE"

lemma while_k_SE : "while_SE = while_k k"
by (simp only: while_k_def)

method bound_while for n::nat = (simp only: while_k_SE [of n])

lemma exec_while_k : 
"(\<sigma> \<Turnstile> ((while_k (Suc k) b c) ;- M)) = 
 (\<sigma> \<Turnstile> ((if\<^sub>S\<^sub>E b then c ;- (while_k k b c) else unit\<^sub>S\<^sub>E ()fi) ;- M))"
by (simp add: exec_while while_k_def)

lemmas exec_while_kD = exec_while_k[THEN iffD1]

method memory_theory = (simp only: memory_theory Monads.bind_assoc')
method norm = (auto dest!: assert_D)

(* Remark: if instead of a recursive call, we use "+", this corresponds to recursing only on the
   first goal, and thus does not work with nested loops *)
method loop_coverage_steps methods simp_mid =
  ((ematch assume_E')
    | (ematch if_SE_execE'', simp_mid?)
    | (dmatch exec_while_kD)
    | (dmatch exec_assignD')
  ); (loop_coverage_steps simp_mid)?
method loop_coverage for n::nat methods simp_mid simp_end =
  (bound_while n)?, loop_coverage_steps simp_mid, simp_end?
  
method branch_and_loop_coverage for n::nat = loop_coverage n memory_theory simp_all
method mcdc_and_loop_coverage for n::nat = loop_coverage n auto auto
(* method mcdc_and_loop_coverage for n::nat = loop_coverage n norm norm *)


text\<open> We can now use these tactics \<close>

(* method mcdc_and_loop_coverage for n::nat = loop_coverage n norm norm *)


text\<open> We can now use these tactics \<close>



lemma 
assumes annotated_program: 
         "\<sigma>\<^sub>0 \<Turnstile> assume\<^sub>S\<^sub>E \<open>0 \<le> a\<close> ;- 
               \<open>tm := 1\<close> ;-
               \<open>sqsum := 1\<close> ;-
               \<open>i := 0\<close> ;-
               (while\<^sub>S\<^sub>E \<open>sqsum <= a\<close> do 
                  \<open>i := i+1\<close> ;-
                  \<open>tm := tm + 2\<close> ;-
                  \<open>sqsum := tm + sqsum\<close>
               od) ;-
               assert\<^sub>S\<^sub>E(\<lambda>\<sigma>. \<sigma>=\<sigma>\<^sub>R)"
shows "\<sigma>\<^sub>R \<Turnstile>assert\<^sub>S\<^sub>E \<open>i * i \<le> a \<and> a < (i + 1) * (i + 1)\<close> "
apply(insert annotated_program)

txt\<open>Automatically unrolls the loop 10 times using branch coverage criterion\<close>
apply (mcdc_and_loop_coverage "Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc 0)))))))))")
(* Takes 22s for 100 unrollings *)
(* apply (mcdc_and_loop_coverage "Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))") *)

text\<open>Here are the test-statements explicit. \<close>

txt\<open>push away the test-hyp: postcond is true for programs with more than
    10 loop traversals (criterion: all-paths(k). This reveals explicitly
    the ten test-cases for @{term "k<10"}. \<close>   
defer 1 

txt\<open>Instead of testing, we @{emph \<open>prove\<close>} that the test cases satisfy the
    post-condition for all @{term "k<10"} loop traversals and @{emph \<open>all\<close>} 
    positive inputs @{term "a \<sigma>"}.\<close>     
apply(auto simp: assert_simp)
oops


text\<open> Automatic unrolling also works for nested loops \<close>

lemma 
assumes annotated_program: 
         "\<sigma>\<^sub>0 \<Turnstile> assume\<^sub>S\<^sub>E\<open>0 \<le> tm\<close> ;- 
               \<open>sqsum := 0\<close> ;- 
               \<open>i := 1\<close> ;- 
              (while\<^sub>S\<^sub>E \<open>i \<le> tm\<close> do 
                   \<open>a := 1\<close> ;- 
                   (while\<^sub>S\<^sub>E \<open>a \<le> tm\<close> do 
                      \<open>sqsum := sqsum+1\<close> ;-
                      \<open>a := a+1\<close>
                   od) ;-
               \<open>i := i+1\<close>
               od) ;- 
              assert\<^sub>S\<^sub>E(\<lambda>\<sigma>. \<sigma>=\<sigma>\<^sub>R)"
shows "\<sigma>\<^sub>R \<Turnstile>assert\<^sub>S\<^sub>E \<open>sqsum = tm*tm\<close>"
apply(insert annotated_program)
(* This takes 19s with MC/DC *)
apply (branch_and_loop_coverage "Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc 0)))))))))")
(*apply (branch_and_loop_coverage "Suc (Suc (Suc 0))")*)

defer 1
(* Proves only the case where tm \<sigma> = 0 *)
apply(auto simp: assert_simp)
oops


text\<open> The same program as above, but with a single loop \<close>

lemma 
assumes annotated_program: 
         "\<sigma>\<^sub>0 \<Turnstile> assume\<^sub>S\<^sub>E\<open>0 \<le> tm\<close> ;- 
               \<open>sqsum := 0\<close> ;- 
               \<open>i := 1\<close> ;-
               \<open>a := 1\<close> ;-
              (while\<^sub>S\<^sub>E \<open>i \<le> tm\<close> do 
                 \<open>sqsum := sqsum+1\<close> ;-
                 (if\<^sub>S\<^sub>E \<open>a = tm\<close> then \<open>a := 1\<close> ;- \<open>i := i+1\<close> else \<open>a := a+1\<close> fi)
               od) ;-
              assert\<^sub>S\<^sub>E(\<lambda>\<sigma>. \<sigma>=\<sigma>\<^sub>R)"
shows "\<sigma>\<^sub>R \<Turnstile>assert\<^sub>S\<^sub>E \<open>sqsum = tm*tm\<close>"
apply(insert annotated_program)
(*apply (mcdc_and_loop_coverage "Suc (Suc (Suc 0))")*)
apply (mcdc_and_loop_coverage "Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc 0)))))))))")
(* The goals have a completely different shape *)
apply(auto simp: assert_simp)
oops


text\<open> Branch coverage vs MC/DC \<close>

lemma 
assumes annotated_program: 
         "\<sigma>\<^sub>0 \<Turnstile> (if\<^sub>S\<^sub>E \<open>(a \<le> i \<and> i \<le> tm) \<or> (tm \<le> i \<and> i \<le> a)\<close> then
                  \<open>sqsum := i\<close>
                else (if\<^sub>S\<^sub>E \<open>(i \<le> a \<and> a \<le> tm) \<or> (tm \<le> a \<and> a \<le> i)\<close> then
                  \<open>sqsum := a\<close>
                else
                  \<open>sqsum := tm\<close>
                fi) fi) ;-
               assert\<^sub>S\<^sub>E(\<lambda>\<sigma>. \<sigma>=\<sigma>\<^sub>R)"
shows "\<sigma>\<^sub>R \<Turnstile>assert\<^sub>S\<^sub>E \<open>sqsum = i \<or> sqsum = a \<or> sqsum = tm\<close> "
apply(insert annotated_program)
(* Simply branch coverage *)
(*apply (branch_and_loop_coverage 0)*)
(* MC/DC *)
apply (mcdc_and_loop_coverage 0)
apply(auto simp: assert_simp)
done

end
