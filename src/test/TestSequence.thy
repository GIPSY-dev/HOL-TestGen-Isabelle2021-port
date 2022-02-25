(*****************************************************************************
 * HOL-TestGen --- theorem-prover based test case generation
 *                 http://www.brucker.ch/projects/hol-testgen/
 *                                                                            
 * Monads.thy --- a base testing theory for sequential computations.
 * This file is part of HOL-TestGen.
 *
 * Copyright (c) 2005-2007, ETH Zurich, Switzerland
 *               2009 B. Wolff, Univ. Paris-Sud, France 
 *               2009, 2012 Achim D. Brucker, Germany
 *
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are
 * met:
 *
 *     * Redistributions of source code must retain the above copyright
 *       notice, this list of conditions and the following disclaimer.
 *
 *     * Redistributions in binary form must reproduce the above
 *       copyright notice, this list of conditions and the following
 *       disclaimer in the documentation and/or other materials provided
 *       with the distribution.
 *
 *     * Neither the name of the copyright holders nor the names of its
 *       contributors may be used to endorse or promote products derived
 *       from this software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
 * "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
 * LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
 * A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
 * OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
 * SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
 * LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
 * DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
 * THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
 * (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
 * OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 ******************************************************************************)
(* $Id:$ *)

chapter {* Basic Monad Theory for Sequential Computations *}

theory Monads imports Main
begin 


section{*General Framework for Monad-based Sequence-Test *}
text{* As such, Higher-order Logic as a purely functional specification
       formalism has no built-in mechanism for state and state-transitions.
       Forms of testing involving state require therefore explicit mechanisms 
       for their treatment inside the logic; a well-known technique to model
       states inside purely functional languages are \emph{monads} made popular
       by Wadler and Moggi and extensively used in Haskell. \HOL is powerful 
       enough to represent the most important standard monads; 
       however, it is not possible to represent monads as such due to well-known 
       limitations of the Hindley-Milner type-system. *}

text{* Here is a variant for state-exception monads, that models precisely
       transition functions with preconditions. Next, we declare the 
       state-backtrack-monad. In all of them, our concept of i/o stepping
       functions can be formulated; these are functions mapping input
       to a given monad. Later on, we will build the usual concepts of:
       \begin{enumerate}
       \item deterministic i/o automata,
       \item non-deterministic i/o automata, and
       \item labelled transition systems (LTS)
       \end{enumerate}
*}

subsection{* Standard State Exception Monads *}
type_synonym ('o, '\<sigma>) MON\<^sub>S\<^sub>E = "'\<sigma> \<rightharpoonup> ('o \<times> '\<sigma>)" (* = '\<sigma> \<Rightarrow> ('o \<times> '\<sigma>)option *) 
      
      
definition bind_SE :: "('o,'\<sigma>)MON\<^sub>S\<^sub>E \<Rightarrow> ('o \<Rightarrow> ('o','\<sigma>)MON\<^sub>S\<^sub>E) \<Rightarrow> ('o','\<sigma>)MON\<^sub>S\<^sub>E" 
where     "bind_SE f g = (\<lambda>\<sigma>. case f \<sigma> of None \<Rightarrow> None 
                                        | Some (out, \<sigma>') \<Rightarrow> g out \<sigma>')"

notation bind_SE ("bind\<^sub>S\<^sub>E")

syntax    (xsymbols)
          "_bind_SE" :: "[pttrn,('o,'\<sigma>)MON\<^sub>S\<^sub>E,('o','\<sigma>)MON\<^sub>S\<^sub>E] \<Rightarrow> ('o','\<sigma>)MON\<^sub>S\<^sub>E" 
          ("(2 _ \<leftarrow> _; _)" [5,8,8]8)
translations 
          "x \<leftarrow> f; g" == "CONST bind_SE f (% x . g)"
          

definition unit_SE :: "'o \<Rightarrow> ('o, '\<sigma>)MON\<^sub>S\<^sub>E"   ("(return _)" 8) 
where     "unit_SE e = (\<lambda>\<sigma>. Some(e,\<sigma>))"
notation   unit_SE ("unit\<^sub>S\<^sub>E")

definition fail_SE :: "('o, '\<sigma>)MON\<^sub>S\<^sub>E"
where     "fail_SE = (\<lambda>\<sigma>. None)"
notation   fail_SE ("fail\<^sub>S\<^sub>E")

definition assert_SE :: "('\<sigma> \<Rightarrow> bool) \<Rightarrow> (bool, '\<sigma>)MON\<^sub>S\<^sub>E"
where     "assert_SE P = (\<lambda>\<sigma>. if P \<sigma> then Some(True,\<sigma>) else None)"
notation   assert_SE ("assert\<^sub>S\<^sub>E")

definition assume_SE :: "('\<sigma> \<Rightarrow> bool) \<Rightarrow> (unit, '\<sigma>)MON\<^sub>S\<^sub>E"
where     "assume_SE P = (\<lambda>\<sigma>. if \<exists>\<sigma> . P \<sigma> then Some((), SOME \<sigma> . P \<sigma>) else None)"
notation   assume_SE ("assume\<^sub>S\<^sub>E")

text{* The standard monad theorems about unit and associativity: *}

lemma bind_left_unit [simp]: "(x \<leftarrow> return c; P x) = P c"
  by (simp add: unit_SE_def bind_SE_def)
  

lemma bind_left_fail_SE[simp] : "(x \<leftarrow> fail\<^sub>S\<^sub>E; P x) = fail\<^sub>S\<^sub>E"
  by (simp add: fail_SE_def bind_SE_def)


lemma bind_right_unit[simp]: "(x \<leftarrow> m; return x) = m"
  apply (simp add:  unit_SE_def bind_SE_def)
  apply (rule ext)
  apply (case_tac "m \<sigma>", simp_all)
  done

lemma bind_assoc[simp]: "(y \<leftarrow> (x \<leftarrow> m; k x); h y) = (x \<leftarrow> m; (y \<leftarrow> k x; h y))"
  apply (simp add: unit_SE_def bind_SE_def, rule ext)
  apply (case_tac "m \<sigma>", simp_all)
  apply (case_tac "a", simp_all)
  done

          
text{* The bind-operator in the state-exception monad yields already
       a semantics for the concept of an input sequence on the meta-level: *}
lemma     syntax_test: "(o1 \<leftarrow> f1 ; o2 \<leftarrow> f2; return (post o1 o2)) = X"
oops



subsection {* "Pipe-free" - variant of the bind. *}

definition seq_SE :: "[('\<alpha>, '\<sigma>)MON\<^sub>S\<^sub>E, ('\<beta>, '\<sigma>)MON\<^sub>S\<^sub>E] \<Rightarrow> ('\<beta>, '\<sigma>)MON\<^sub>S\<^sub>E" (infixl ";-" 65)
where     "f ;- g = (_ \<leftarrow> f ; g)"



subsection {* Monadic If *}
 
definition if_SE :: "['\<sigma> \<Rightarrow> bool, ('\<alpha>, '\<sigma>)MON\<^sub>S\<^sub>E, ('\<alpha>, '\<sigma>)MON\<^sub>S\<^sub>E] \<Rightarrow> ('\<alpha>, '\<sigma>)MON\<^sub>S\<^sub>E"
where     "if_SE c E F = (\<lambda>\<sigma>. if c \<sigma> then E \<sigma> else F \<sigma>)" 

syntax    (xsymbols)
          "_if_SE" :: "['\<sigma> \<Rightarrow> bool,('o,'\<sigma>)MON\<^sub>S\<^sub>E,('o','\<sigma>)MON\<^sub>S\<^sub>E] \<Rightarrow> ('o','\<sigma>)MON\<^sub>S\<^sub>E" 
          ("(if\<^sub>S\<^sub>E _ then _ else _fi)" [5,8,8]8)
translations 
          "(if\<^sub>S\<^sub>E cond then T1 else T2 fi)" == "CONST if_SE cond T1 T2"
   


subsubsection{* Theory of a Monadic While *}

text{* First Step : Establishing an embedding between partial functions and relations *} 
(* plongement *)
definition Mon2Rel :: "(unit, '\<sigma>)MON\<^sub>S\<^sub>E \<Rightarrow> ('\<sigma> \<times> '\<sigma>) set"
where "Mon2Rel f = {(x, y). (f x = Some((), y))}"
(* ressortir *)
definition Rel2Mon :: " ('\<sigma> \<times> '\<sigma>) set \<Rightarrow> (unit, '\<sigma>)MON\<^sub>S\<^sub>E "
where "Rel2Mon S = (\<lambda> \<sigma>. if \<exists>\<sigma>'. (\<sigma>, \<sigma>') \<in> S then Some((), SOME \<sigma>'. (\<sigma>, \<sigma>') \<in> S) else None)"

lemma Mon2Rel_Rel2Mon_id: assumes det:"single_valued R" shows "(Mon2Rel \<circ> Rel2Mon) R = R"
apply (simp add: comp_def Mon2Rel_def Rel2Mon_def,auto)
apply (case_tac "\<exists>\<sigma>'. (a, \<sigma>') \<in> R", auto)
apply (subst some_eq_ex) back
apply (insert det[simplified single_valued_def])
apply (auto)
done

lemma Rel2Mon_Id: "(Rel2Mon \<circ> Mon2Rel) x = x"
apply (rule ext)
apply (auto simp: comp_def Mon2Rel_def Rel2Mon_def)
apply (erule contrapos_pp, drule HOL.not_sym, simp)
done

lemma single_valued_Mon2Rel: "single_valued (Mon2Rel B)"
by (auto simp: single_valued_def Mon2Rel_def)

text{* Second Step : Proving an induction principle allowing to establish that lfp remains
       deterministic *} 


(* Due to Tobias Nipkow *)
definition chain :: "(nat => 'a set) => bool" 
where     "chain S = (\<forall>i. S i \<subseteq> S(Suc i))"

lemma chain_total: "chain S ==> S i \<le> S j \<or> S j \<le> S i"
by (metis chain_def le_cases lift_Suc_mono_le)

definition cont :: "('a set => 'b set) => bool" 
where     "cont f = (\<forall>S. chain S \<longrightarrow> f(UN n. S n) = (UN n. f(S n)))"

lemma mono_if_cont: fixes f :: "'a set => 'b set"
  assumes "cont f" shows "mono f"
proof
  fix a b :: "'a set" assume "a \<subseteq> b"
  let ?S = "\<lambda>n::nat. if n=0 then a else b"
  have "chain ?S" using `a \<subseteq> b` by(auto simp: chain_def)
  hence "f(UN n. ?S n) = (UN n. f(?S n))"
    using assms by(simp add: cont_def)
  moreover have "(UN n. ?S n) = b" using `a \<subseteq> b` by (auto split: if_splits)
  moreover have "(UN n. f(?S n)) = f a \<union> f b" by (auto split: if_splits)
  ultimately show "f a \<subseteq> f b" by (metis Un_upper1)
qed

lemma chain_iterates: fixes f :: "'a set => 'a set"
  assumes "mono f" shows "chain(\<lambda>n. (f^^n) {})"
proof-
  { fix n have "(f ^^ n) {} \<subseteq> (f ^^ Suc n) {}" using assms
    by(induction n) (auto simp: mono_def) }
  thus ?thesis by(auto simp: chain_def)
qed

theorem lfp_if_cont:
  assumes "cont f" shows "lfp f = (UN n. (f^^n) {})" (is "_ = ?U")
proof
  show "lfp f \<subseteq> ?U"
  proof (rule lfp_lowerbound)
    have "f ?U = (UN n. (f^^Suc n){})"
      using chain_iterates[OF mono_if_cont[OF assms]] assms
      by(simp add: cont_def)
    also have "\<dots> = (f^^0){} \<union> \<dots>" by simp
    also have "\<dots> = ?U"
      by(auto simp del: funpow.simps) (metis not0_implies_Suc)
    finally show "f ?U \<subseteq> ?U" by simp
  qed
next
  { fix n p assume "f p \<subseteq> p"
    have "(f^^n){} \<subseteq> p"
    proof(induction n)
      case 0 show ?case by simp
    next
      case Suc
      from monoD[OF mono_if_cont[OF assms] Suc] `f p \<subseteq> p`
      show ?case by simp
    qed
  }
  thus "?U \<subseteq> lfp f" by(auto simp: lfp_def)
qed


lemma single_valued_UN_chain:
  assumes "chain S" "(!!n. single_valued (S n))"
  shows "single_valued(UN n. S n)"
proof(auto simp: single_valued_def)
  fix m n x y z assume "(x, y) \<in> S m" "(x, z) \<in> S n"
  with chain_total[OF assms(1), of m n] assms(2)
  show "y = z" by (auto simp: single_valued_def)
qed

lemma single_valued_lfp: 
fixes f :: "('a \<times> 'a) set => ('a \<times> 'a) set"
assumes "cont f" "\<And>r. single_valued r \<Longrightarrow> single_valued (f r)"
shows "single_valued(lfp f)"
unfolding lfp_if_cont[OF assms(1)]
proof(rule single_valued_UN_chain[OF chain_iterates[OF mono_if_cont[OF assms(1)]]])
  fix n show "single_valued ((f ^^ n) {})"
  by(induction n)(auto simp: assms(2))
qed


text{* Third Step: Definition of the Monadic While *}
definition \<Gamma> :: "['\<sigma> \<Rightarrow> bool,('\<sigma> \<times> '\<sigma>) set] \<Rightarrow> (('\<sigma> \<times> '\<sigma>) set \<Rightarrow> ('\<sigma> \<times> '\<sigma>) set)" 
where     "\<Gamma> b cd = (\<lambda>cw. {(s,t). if b s then (s, t) \<in> cd O cw else s = t})"


definition while_SE :: "['\<sigma> \<Rightarrow> bool, (unit, '\<sigma>)MON\<^sub>S\<^sub>E] \<Rightarrow> (unit, '\<sigma>)MON\<^sub>S\<^sub>E"
where     "while_SE c B \<equiv> (Rel2Mon(lfp(\<Gamma> c (Mon2Rel B))))"

syntax    (xsymbols)
          "_while_SE" :: "['\<sigma> \<Rightarrow> bool, (unit, '\<sigma>)MON\<^sub>S\<^sub>E] \<Rightarrow> (unit, '\<sigma>)MON\<^sub>S\<^sub>E" 
          ("(while\<^sub>S\<^sub>E _ do _ od)" [8,8]8)
translations 
          "while\<^sub>S\<^sub>E c do b od" == "CONST while_SE c b"

lemma cont_\<Gamma>: "cont (\<Gamma> c b)"
by (auto simp: cont_def \<Gamma>_def)

text{* The fixpoint theory now allows us to establish that the lfp constructed over
       @{term Mon2Rel} remains deterministic *}

theorem single_valued_lfp_Mon2Rel: "single_valued (lfp(\<Gamma> c (Mon2Rel B)))"
apply(rule single_valued_lfp, simp_all add: cont_\<Gamma>)
apply(auto simp: \<Gamma>_def single_valued_def)
apply(metis single_valued_Mon2Rel[of "B"] single_valued_def)
done


lemma Rel2Mon_if:
  "Rel2Mon {(s, t). if b s then (s, t) \<in> Mon2Rel c O lfp (\<Gamma> b (Mon2Rel c)) else s = t} \<sigma> =
  (if b \<sigma> then Rel2Mon (Mon2Rel c O lfp (\<Gamma> b (Mon2Rel c))) \<sigma> else Some ((), \<sigma>))"
by (simp add: Rel2Mon_def)

lemma Rel2Mon_homomorphism:
  assumes determ_X: "single_valued X" and determ_Y: "single_valued Y"
  shows   "Rel2Mon (X O Y) = (Rel2Mon X) ;- (Rel2Mon Y)"
proof - 
    have  relational_partial_next_in_O: "!!x E F. (\<exists>y. (x, y) \<in> (E O F)) 
                                                  \<Longrightarrow> (\<exists>y. (x, y) \<in> E)" by (auto)
show ?thesis
apply (simp add: Rel2Mon_def seq_SE_def bind_SE_def)
apply (rule ext)
apply (case_tac " \<exists>\<sigma>'. (\<sigma>, \<sigma>') \<in> X O Y")
apply (simp only: HOL.if_True)
apply (frule relational_partial_next_in_O)
apply (auto)
apply (insert determ_X determ_Y)

defer 1

apply (rule_tac x=z in exI)
apply (rule someI2)
apply (assumption)+
apply (simp add: single_valued_def)
apply (metis)

apply (erule contrapos_pp)
apply (simp)
apply (rule_tac x=\<sigma>' in exI)
    apply (subgoal_tac "(SOME \<sigma>'. (\<sigma>, \<sigma>') \<in> X) = \<sigma>''")
    apply (auto)
  apply (auto simp: single_valued_def)
apply (fold single_valued_def)

    apply (subgoal_tac "(SOME \<sigma>'. (x, \<sigma>') \<in> X) = y")
    apply (simp)
          apply (subgoal_tac "(SOME \<sigma>'. (y, \<sigma>') \<in> Y) = z")
          apply (simp)
                apply (subgoal_tac "(SOME \<sigma>'. (x, \<sigma>') \<in> X O Y) = z")
                apply (simp)
           apply (auto simp: single_valued_def)
           (* TODO IMPORTANT *)

    apply (rule someI2)
    apply (assumption)
    apply (rule someI2)
    apply (auto)
oops
(* qed *)

text{* Putting everything together, the theory of embedding and the invariance of
       determinism of the while-body, gives us the usual unfold-theorem: *}
theorem "(while\<^sub>S\<^sub>E b do c od) = (if\<^sub>S\<^sub>E b then (c ;- (while\<^sub>S\<^sub>E b do c od)) else return () fi)"
apply (simp add: if_SE_def seq_SE_def while_SE_def unit_SE_def)
apply (subst lfp_unfold [OF mono_if_cont, OF cont_\<Gamma>])
apply (rule ext)
apply (subst \<Gamma>_def)
apply (auto simp: Rel2Mon_if Rel2Mon_homomorphism seq_SE_def Rel2Mon_Id [simplified comp_def] 
                  single_valued_Mon2Rel single_valued_lfp_Mon2Rel )
done



subsection{* Multi-binds *}

text{*  In order to express test-sequences also on the object-level and
to make our theory amenable to formal reasoning over test-sequences, 
we represent them as lists of input and generalize the bind-operator
of the state-exception monad accordingly. The approach is straightforward,
but comes with a price: we have to encapsulate all input and output data
into one type. Assume that we have a typed interface to a module with
the operations $op_1$, $op_2$, \ldots, $op_n$ with the inputs 
$\iota_1$, $\iota_2$, \ldots, $\iota_n$ (outputs are treated analogously).
Then we can encode for this interface the general input - type:
\begin{displaymath}
\texttt{datatype}\ \texttt{in}\ =\ op_1\ ::\ \iota_1\ |\ ...\ |\ \iota_n
\end{displaymath}
Obviously, we loose some type-safety in this approach; we have to express
that in traces only \emph{corresponding} input and output belonging to the 
same operation will occur; this form of side-conditions have to be expressed
inside \HOL. From the user perspective, this will not make much difference,
since junk-data resulting from too weak typing can be ruled out by adopted
front-ends. 
*}

text{* Note that the subsequent notion of a test-sequence allows the io stepping 
function (and the special case of a program under test) to stop execution 
\emph{within} the sequence; such premature terminations are characterized by an 
output list which is shorter than the input list. *}

fun    mbind :: "'\<iota> list  \<Rightarrow>  ('\<iota> \<Rightarrow> ('o,'\<sigma>) MON\<^sub>S\<^sub>E) \<Rightarrow> ('o list,'\<sigma>) MON\<^sub>S\<^sub>E"  
where "mbind [] iostep \<sigma> = Some([], \<sigma>)" |
      "mbind (a#H) iostep \<sigma> = 
                (case iostep a \<sigma> of 
                     None   \<Rightarrow> Some([], \<sigma>)
                  |  Some (out, \<sigma>') \<Rightarrow> (case mbind H iostep \<sigma>' of 
                                          None    \<Rightarrow> Some([out],\<sigma>') 
                                        | Some(outs,\<sigma>'') \<Rightarrow> Some(out#outs,\<sigma>'')))"

notation mbind ("mbind\<^sub>F\<^sub>a\<^sub>i\<^sub>l\<^sub>S\<^sub>a\<^sub>v\<^sub>e") (* future name: mbind\<^sub>F\<^sub>a\<^sub>i\<^sub>l\<^sub>S\<^sub>a\<^sub>v\<^sub>e *)

text{* This definition is fail-safe; in case of an exception, the current state is maintained,
       the computation as a whole is marked as success.
       Compare to the fail-strict variant @{text "mbind'"}: *}

lemma mbind_unit [simp]: 
     "mbind [] f = (return [])"
      by(rule ext, simp add: unit_SE_def)

text{* The characteristic property of @{term mbind} --- which distinguishes it from 
       @{text mbind'} defined in the sequel --- is that it never fails; it ``swallows'' internal
       errors occuring during the computation. *}    
lemma mbind_nofailure [simp]:
     "mbind S f \<sigma> \<noteq> None"
      apply(rule_tac x=\<sigma> in spec)
      apply(induct S, auto simp:unit_SE_def)
      apply(case_tac "f a x", auto)
      apply(erule_tac x="b" in allE)
      apply(erule exE, erule exE, simp)
      done


fun    mbind' :: "'\<iota> list  \<Rightarrow>  ('\<iota> \<Rightarrow> ('o,'\<sigma>) MON\<^sub>S\<^sub>E) \<Rightarrow> ('o list,'\<sigma>) MON\<^sub>S\<^sub>E"
where "mbind' [] iostep \<sigma> = Some([], \<sigma>)" |
      "mbind' (a#S) iostep \<sigma> = 
                (case iostep a \<sigma> of 
                     None   \<Rightarrow> None
                  |  Some (out, \<sigma>') \<Rightarrow> (case mbind' S iostep \<sigma>' of 
                                          None    \<Rightarrow> None   (*  fail-strict *) 
                                        | Some(outs,\<sigma>'') \<Rightarrow> Some(out#outs,\<sigma>'')))"
notation mbind' ("mbind\<^sub>F\<^sub>a\<^sub>i\<^sub>l\<^sub>S\<^sub>t\<^sub>o\<^sub>p") (* future name: mbind\<^sub>F\<^sub>a\<^sub>i\<^sub>l\<^sub>S\<^sub>t\<^sub>o\<^sub>p *)

lemma mbind'_unit [simp]: 
     "mbind' [] f = (return [])"
      by(rule ext, simp add: unit_SE_def)

lemma mbind'_bind [simp]: 
     "(x \<leftarrow> mbind' (a#S) F; M x) = (a \<leftarrow> (F a); (x \<leftarrow> mbind' S F; M (a # x)))"
      by(rule ext, rename_tac "z",simp add: bind_SE_def split: option.split)

declare mbind'.simps[simp del] (* use only more abstract definitions *)


fun    mbind'' :: "'\<iota> list  \<Rightarrow>  ('\<iota> \<Rightarrow> ('o,'\<sigma>) MON\<^sub>S\<^sub>E) \<Rightarrow> ('o list,'\<sigma>) MON\<^sub>S\<^sub>E"
where "mbind'' [] iostep \<sigma> = Some([], \<sigma>)" |
      "mbind'' (a#S) iostep \<sigma> = 
                (case iostep a \<sigma> of 
                     None           \<Rightarrow> mbind'' S iostep \<sigma>
                  |  Some (out, \<sigma>') \<Rightarrow> (case mbind'' S iostep \<sigma>' of 
                                          None    \<Rightarrow> None   (*  does not occur *) 
                                        | Some(outs,\<sigma>'') \<Rightarrow> Some(out#outs,\<sigma>'')))"

notation mbind'' ("mbind\<^sub>F\<^sub>a\<^sub>i\<^sub>l\<^sub>P\<^sub>u\<^sub>r\<^sub>g\<^sub>e") (* future name: mbind\<^sub>P\<^sub>u\<^sub>r\<^sub>g\<^sub>e\<^sub>F\<^sub>a\<^sub>i\<^sub>l *)
declare  mbind''.simps[simp del] (* use only more abstract definitions *)


text{* mbind' as failure strict operator can be seen as a foldr on bind -
       if the types would match \ldots *}

definition try_SE :: "('o,'\<sigma>) MON\<^sub>S\<^sub>E \<Rightarrow> ('o option,'\<sigma>) MON\<^sub>S\<^sub>E" ("try\<^sub>S\<^sub>E")
where     "try\<^sub>S\<^sub>E ioprog = (\<lambda>\<sigma>. case ioprog \<sigma> of
                                      None \<Rightarrow> Some(None, \<sigma>)
                                    | Some(outs, \<sigma>') \<Rightarrow> Some(Some outs, \<sigma>'))" 
text{* In contrast, mbind as a failure safe operator can roughly be seen 
       as a foldr on bind - try:
       m1 ; try m2 ; try m3; ... Note, that the rough equivalence only holds for
       certain predicates in the sequence - length equivalence modulo None,
       for example. However, if a conditional is added, the equivalence
       can be made precise: *}

lemma mbind_try: 
  "(x \<leftarrow> mbind (a#S) F; M x) = 
   (a' \<leftarrow> try\<^sub>S\<^sub>E(F a); 
      if a' = None 
      then (M [])
      else (x \<leftarrow> mbind S F; M (the a' # x)))"
apply(rule ext)
apply(simp add: bind_SE_def try_SE_def)
apply(case_tac "F a x", auto)
apply(simp add: bind_SE_def try_SE_def)
apply(case_tac "mbind S F b", auto)
done

text{* On this basis, a symbolic evaluation scheme can be established
  that reduces mbind-code to try\_SE\_code and ite-cascades. *}

definition alt_SE :: "[('o, '\<sigma>)MON\<^sub>S\<^sub>E, ('o, '\<sigma>)MON\<^sub>S\<^sub>E] \<Rightarrow> ('o, '\<sigma>)MON\<^sub>S\<^sub>E"   (infixl "\<sqinter>\<^sub>S\<^sub>E" 10)
where     "(f \<sqinter>\<^sub>S\<^sub>E g) = (\<lambda> \<sigma>. case f \<sigma> of None \<Rightarrow> g \<sigma>
                                      | Some H \<Rightarrow> Some H)"

definition malt_SE :: "('o, '\<sigma>)MON\<^sub>S\<^sub>E list \<Rightarrow> ('o, '\<sigma>)MON\<^sub>S\<^sub>E"
where     "malt_SE S = foldr alt_SE S fail\<^sub>S\<^sub>E"
notation   malt_SE ("\<Sqinter>\<^sub>S\<^sub>E")

lemma malt_SE_mt [simp]: "\<Sqinter>\<^sub>S\<^sub>E [] = fail\<^sub>S\<^sub>E"
by(simp add: malt_SE_def)

lemma malt_SE_cons [simp]: "\<Sqinter>\<^sub>S\<^sub>E (a # S) = (a \<sqinter>\<^sub>S\<^sub>E (\<Sqinter>\<^sub>S\<^sub>E S))"
by(simp add: malt_SE_def)


subsection{* State Backtrack Monads *}
text{*This subsection is still rudimentary and as such an interesting
formal analogue to the previous monad definitions. It is doubtful that it is
interesting for testing and as a cmputational stucture at all. 
Clearly more relevant is ``sequence'' instead of ``set,'' which would
rephrase Isabelle's internal tactic concept. *}

type_synonym ('o, '\<sigma>) MON\<^sub>S\<^sub>B = "'\<sigma> \<Rightarrow> ('o \<times> '\<sigma>) set"

definition bind_SB :: "('o, '\<sigma>)MON\<^sub>S\<^sub>B \<Rightarrow> ('o \<Rightarrow>  ('o', '\<sigma>)MON\<^sub>S\<^sub>B) \<Rightarrow> ('o', '\<sigma>)MON\<^sub>S\<^sub>B"
where     "bind_SB f g \<sigma> = \<Union> ((\<lambda>(out, \<sigma>). (g out \<sigma>)) ` (f \<sigma>))"
notation   bind_SB ("bind\<^sub>S\<^sub>B")

definition unit_SB :: "'o \<Rightarrow> ('o, '\<sigma>)MON\<^sub>S\<^sub>B" ("(returns _)" 8) 
where     "unit_SB e = (\<lambda>\<sigma>. {(e,\<sigma>)})"
notation   unit_SB ("unit\<^sub>S\<^sub>B")

syntax    (xsymbols)
          "_bind_SB" :: "[pttrn,('o,'\<sigma>)MON\<^sub>S\<^sub>B,('o','\<sigma>)MON\<^sub>S\<^sub>B] \<Rightarrow> ('o','\<sigma>)MON\<^sub>S\<^sub>B" 
          ("(2 _ := _; _)" [5,8,8]8)
translations 
          "x := f; g" == "CONST bind_SB f (% x . g)"



lemma bind_left_unit_SB : "(x := returns a; m x) = m a"
  by (rule ext,simp add: unit_SB_def bind_SB_def)

lemma bind_right_unit_SB: "(x := m; returns x) = m"
  by (rule ext, simp add: unit_SB_def bind_SB_def)


lemma bind_assoc_SB: "(y := (x := m; k x); h y) = (x := m; (y := k x; h y))"
  by (rule ext, simp add: unit_SB_def bind_SB_def split_def)
  

subsection{* State Backtrack Exception Monad (vulgo: Boogie-PL) *}
text{* The following combination of the previous two Monad-Constructions
allows for the semantic foundation of a simple generic assertion language 
in the style of Schirmers Simpl-Language or Rustan Leino's Boogie-PL language.
The key is to use the exceptional element None for violations of
the assert-statement. *}
type_synonym  ('o, '\<sigma>) MON\<^sub>S\<^sub>B\<^sub>E = "'\<sigma> \<Rightarrow> (('o \<times> '\<sigma>) set) option"

      
definition bind_SBE :: "('o,'\<sigma>)MON\<^sub>S\<^sub>B\<^sub>E \<Rightarrow> ('o \<Rightarrow> ('o','\<sigma>)MON\<^sub>S\<^sub>B\<^sub>E) \<Rightarrow> ('o','\<sigma>)MON\<^sub>S\<^sub>B\<^sub>E" 
where     "bind_SBE f g = (\<lambda>\<sigma>. case f \<sigma> of None \<Rightarrow> None 
                                         | Some S \<Rightarrow> (let S' = (\<lambda>(out, \<sigma>'). g out \<sigma>') ` S
                                                      in  if None \<in> S' then None
                                                          else Some(\<Union> (the ` S'))))"

syntax    (xsymbols)
          "_bind_SBE" :: "[pttrn,('o,'\<sigma>)MON\<^sub>S\<^sub>B\<^sub>E,('o','\<sigma>)MON\<^sub>S\<^sub>B\<^sub>E] \<Rightarrow> ('o','\<sigma>)MON\<^sub>S\<^sub>B\<^sub>E" 
          ("(2 _ :\<equiv> _; _)" [5,8,8]8)
translations 
          "x :\<equiv> f; g" == "CONST bind_SBE f (% x . g)"

definition unit_SBE :: "'o \<Rightarrow> ('o, '\<sigma>)MON\<^sub>S\<^sub>B\<^sub>E"   ("(returning _)" 8) 
where     "unit_SBE e = (\<lambda>\<sigma>. Some({(e,\<sigma>)}))"

definition assert_SBE :: "('\<sigma> \<Rightarrow> bool) \<Rightarrow> (unit, '\<sigma>)MON\<^sub>S\<^sub>B\<^sub>E"
where     "assert_SBE e = (\<lambda>\<sigma>. if e \<sigma> then Some({((),\<sigma>)})
                               else None)"
notation   assert_SBE ("assert\<^sub>S\<^sub>B\<^sub>E")

definition assume_SBE :: "('\<sigma> \<Rightarrow> bool) \<Rightarrow> (unit, '\<sigma>)MON\<^sub>S\<^sub>B\<^sub>E"
where     "assume_SBE e = (\<lambda>\<sigma>. if e \<sigma> then Some({((),\<sigma>)})
                               else Some {})"
notation   assume_SBE ("assume\<^sub>S\<^sub>B\<^sub>E")


definition havoc_SBE :: " (unit, '\<sigma>)MON\<^sub>S\<^sub>B\<^sub>E"
where     "havoc_SBE = (\<lambda>\<sigma>.  Some({x. True}))"
notation   havoc_SBE ("havoc\<^sub>S\<^sub>B\<^sub>E")


lemma bind_left_unit_SBE : "(x :\<equiv> returning a; m x) = m a"
  apply (rule ext,simp add: unit_SBE_def bind_SBE_def)
  apply (case_tac "m a x",auto)
  done

lemma bind_right_unit_SBE: "(x :\<equiv> m; returning x) = m"
  apply (rule ext, simp add: unit_SBE_def bind_SBE_def)
  apply (case_tac "m x", simp_all add:Let_def)
  apply (rule HOL.ccontr, simp add: Set.image_iff)
  done
   

lemmas aux = trans[OF HOL.neq_commute,OF Option.not_None_eq]

lemma bind_assoc_SBE: "(y :\<equiv> (x :\<equiv> m; k); h y) = (x :\<equiv> m; (y :\<equiv> k; h y))"
proof (rule ext, rename_tac z, simp add: unit_SBE_def bind_SBE_def,
       case_tac "m z", simp_all add: Let_def Set.image_iff, safe)
  case goal1 then show ?case
       by(rule_tac x="(a, b)" in bexI, simp_all)
next
  case goal2 then show ?case
       apply(rule_tac  x="(aa,b)" in bexI, simp_all add:split_def)
       apply(erule_tac x="(aa,b)" in ballE)
       apply(auto simp: aux image_def split_def intro!: rev_bexI)
       done
next
  case goal3 then show ?case
       by(rule_tac x="(a, b)" in bexI, simp_all)
next
  case goal4 then show ?case    
       apply(erule_tac Q="None = ?X" in contrapos_pp)
       apply(erule_tac x="(aa,b)" and P="\<lambda> x. None \<noteq> split (\<lambda>out. k) x" in ballE)
       apply(auto simp: aux Option.not_None_eq image_def split_def intro!: rev_bexI)
       done
next 
  case goal5 then show ?case 
       apply simp apply((erule_tac x="(ab,ba)" in ballE)+)
       apply(simp_all add: aux Option.not_None_eq, (erule exE)+, simp add:split_def)
       apply(erule rev_bexI,case_tac "None\<in>(\<lambda>p. h (fst p) (snd p))`y",auto simp:split_def)
       done
 
next
  case goal6 then show ?case
       apply simp apply((erule_tac x="(a,b)" in ballE)+)
       apply(simp_all add: aux Option.not_None_eq, (erule exE)+, simp add:split_def)
       apply(erule rev_bexI, case_tac "None\<in>(\<lambda>p. h(fst p)(snd p))`y",auto simp:split_def)
       done
qed



(* TODO: IF THEN ELSE and WHILE + Monadic Laws + Operational Rules. *)



section{* Valid Execution Sequences in the State Exception Monad *}
text{* This is still an unstructured merge of executable monad concepts
and specification oriented high-level properties initiating test procedures. *}

definition valid_SE :: "'\<sigma> \<Rightarrow> (bool,'\<sigma>) MON\<^sub>S\<^sub>E \<Rightarrow> bool" (infix "\<Turnstile>" 15)
where "(\<sigma> \<Turnstile> m) = (m \<sigma> \<noteq> None \<and> fst(the (m \<sigma>)))"
text{* This notation consideres failures as valid -- a definition
inspired by I/O conformance. BUG: It is not possible to define
this concept once and for all in a Hindley-Milner type-system.
For the moment, we present it only for the state-exception
monad, although for the same definition, this notion is applicable 
to other monads as well.  *}


lemma exec_unit_SE [simp]: "(\<sigma> \<Turnstile> (return P)) = (P)"
by(auto simp: valid_SE_def unit_SE_def)

lemma exec_unit_SE' [simp]: "(\<sigma>\<^sub>0 \<Turnstile> (\<lambda>\<sigma>. Some (f \<sigma>, \<sigma>))) = (f \<sigma>\<^sub>0)"
by(simp add: valid_SE_def )

lemma exec_fail_SE [simp]: "(\<sigma> \<Turnstile> fail\<^sub>S\<^sub>E) = False"
by(auto simp: valid_SE_def fail_SE_def)


lemma exec_fail_SE'[simp]: "\<not>(\<sigma>\<^sub>0 \<Turnstile> (\<lambda>\<sigma>. None))"
by(simp add: valid_SE_def )

lemma  exec_bind_SE_failure:
"A \<sigma> = None \<Longrightarrow> \<not>(\<sigma> \<Turnstile> ((s \<leftarrow> A ; M s)))"
by(simp add: valid_SE_def unit_SE_def bind_SE_def)

lemma exec_bind_SE_success: 
"A \<sigma> = Some(b,\<sigma>') \<Longrightarrow> (\<sigma> \<Turnstile> ((s \<leftarrow> A ; M s))) = (\<sigma>' \<Turnstile> (M b))"
by(simp add: valid_SE_def unit_SE_def bind_SE_def )

lemma exec_bind_SE_success': (* atomic boolean Monad "Query Functions" *) 
"M \<sigma> = Some(f \<sigma>,\<sigma>) \<Longrightarrow>  (\<sigma> \<Turnstile> M) = f \<sigma>"
by(simp add: valid_SE_def unit_SE_def bind_SE_def )



lemma exec_bind_SE_success'':
"\<sigma> \<Turnstile> ((s \<leftarrow> A ; M s)) \<Longrightarrow>  \<exists> v \<sigma>'. the(A \<sigma>) = (v,\<sigma>') \<and> \<sigma>' \<Turnstile> (M v)"
apply(auto simp: valid_SE_def unit_SE_def bind_SE_def)
apply(cases "A \<sigma>", simp_all)
apply(simp add: Product_Type.prod_case_unfold)
apply(drule_tac x="A \<sigma>" and f=the in arg_cong, simp)
apply(rule_tac x="fst aa" in exI)
apply(rule_tac x="snd aa" in exI, auto)
done


lemma exec_bind_SE_success''':
"\<sigma> \<Turnstile> ((s \<leftarrow> A ; M s)) \<Longrightarrow>  \<exists> a. (A \<sigma>) = Some a \<and> (snd a) \<Turnstile> (M (fst a))"
apply(auto simp: valid_SE_def unit_SE_def bind_SE_def)
apply(cases "A \<sigma>", simp_all)
apply(simp_all add: Product_Type.prod_case_unfold
           split: prod.splits)
apply(drule_tac x="A \<sigma>" and f=the in arg_cong, simp)
apply(rule_tac x="fst aa" in exI)
apply(rule_tac x="snd aa" in exI, auto)
done


lemma  exec_bind_SE_success'''' :
"\<sigma> \<Turnstile> ((s \<leftarrow> A ; M s)) \<Longrightarrow>  \<exists> v \<sigma>'. A \<sigma> = Some(v,\<sigma>') \<and> \<sigma>' \<Turnstile> (M v)"
apply(auto simp: valid_SE_def unit_SE_def bind_SE_def)
apply(cases "A \<sigma>", simp_all)
apply(simp add: Product_Type.prod_case_unfold)
apply(drule_tac x="A \<sigma>" and f=the in arg_cong, simp)
apply(rule_tac x="fst aa" in exI)
apply(rule_tac x="snd aa" in exI, auto)
done


text{* Recall \verb+mbind_unit+ for the base case. *}

lemma exec_mbindFSave_failure: 
"ioprog a \<sigma> = None \<Longrightarrow> 
   (\<sigma> \<Turnstile> (s \<leftarrow> mbind\<^sub>F\<^sub>a\<^sub>i\<^sub>l\<^sub>S\<^sub>a\<^sub>v\<^sub>e (a#S) ioprog ; M s)) =  (\<sigma> \<Turnstile> (M []))"
by(simp add: valid_SE_def unit_SE_def bind_SE_def)

lemma exec_mbindFStop_failure: 
"ioprog a \<sigma> = None \<Longrightarrow> 
   (\<sigma> \<Turnstile> (s \<leftarrow> mbind\<^sub>F\<^sub>a\<^sub>i\<^sub>l\<^sub>S\<^sub>t\<^sub>o\<^sub>p (a#S) ioprog ; M s)) =  (False)"
by(simp add: exec_bind_SE_failure)

lemma exec_mbindFPurge_failure: 
"ioprog a \<sigma> = None \<Longrightarrow> 
   (\<sigma> \<Turnstile> (s \<leftarrow> mbind\<^sub>F\<^sub>a\<^sub>i\<^sub>l\<^sub>P\<^sub>u\<^sub>r\<^sub>g\<^sub>e (a#S) ioprog ; M s)) = (\<sigma> \<Turnstile> (s \<leftarrow> mbind\<^sub>F\<^sub>a\<^sub>i\<^sub>l\<^sub>P\<^sub>u\<^sub>r\<^sub>g\<^sub>e (S) ioprog ; M s))" 
by(simp add: valid_SE_def unit_SE_def bind_SE_def mbind''.simps)


lemma exec_mbindFSave_success : 
"ioprog a \<sigma> = Some(b,\<sigma>') \<Longrightarrow> 
   (\<sigma>  \<Turnstile> (s \<leftarrow> mbind\<^sub>F\<^sub>a\<^sub>i\<^sub>l\<^sub>S\<^sub>a\<^sub>v\<^sub>e (a#S) ioprog ; M s)) = 
   (\<sigma>' \<Turnstile> (s \<leftarrow> mbind\<^sub>F\<^sub>a\<^sub>i\<^sub>l\<^sub>S\<^sub>a\<^sub>v\<^sub>e S ioprog ; M (b#s)))"
unfolding valid_SE_def unit_SE_def bind_SE_def 
by(cases "mbind\<^sub>F\<^sub>a\<^sub>i\<^sub>l\<^sub>S\<^sub>a\<^sub>v\<^sub>e S ioprog \<sigma>'", auto)

lemma exec_mbindFStop_success : 
"ioprog a \<sigma> = Some(b,\<sigma>') \<Longrightarrow> 
   (\<sigma>  \<Turnstile> (s \<leftarrow> mbind\<^sub>F\<^sub>a\<^sub>i\<^sub>l\<^sub>S\<^sub>t\<^sub>o\<^sub>p (a#S) ioprog ; M s)) = 
   (\<sigma>' \<Turnstile> (s \<leftarrow> mbind\<^sub>F\<^sub>a\<^sub>i\<^sub>l\<^sub>S\<^sub>t\<^sub>o\<^sub>p S ioprog ; M (b#s)))"
unfolding valid_SE_def unit_SE_def bind_SE_def 
by(cases "mbind\<^sub>F\<^sub>a\<^sub>i\<^sub>l\<^sub>S\<^sub>t\<^sub>o\<^sub>p S ioprog \<sigma>'", auto simp:  mbind'.simps)

lemma exec_mbindFPurge_success : 
"ioprog a \<sigma> = Some(b,\<sigma>') \<Longrightarrow> 
   (\<sigma>  \<Turnstile> (s \<leftarrow> mbind\<^sub>F\<^sub>a\<^sub>i\<^sub>l\<^sub>P\<^sub>u\<^sub>r\<^sub>g\<^sub>e (a#S) ioprog ; M s)) = 
   (\<sigma>' \<Turnstile> (s \<leftarrow> mbind\<^sub>F\<^sub>a\<^sub>i\<^sub>l\<^sub>P\<^sub>u\<^sub>r\<^sub>g\<^sub>e S ioprog ; M (b#s)))"
unfolding valid_SE_def unit_SE_def bind_SE_def 
by(cases "mbind\<^sub>F\<^sub>a\<^sub>i\<^sub>l\<^sub>P\<^sub>u\<^sub>r\<^sub>g\<^sub>e S ioprog \<sigma>'", auto simp:  mbind''.simps)

lemma exec_mbindFSave:
"(\<sigma> \<Turnstile> (s \<leftarrow> mbind (a#S) ioprog ; return (P s))) =
    (case ioprog a \<sigma> of
       None \<Rightarrow> (\<sigma>  \<Turnstile> (return (P [])))
     | Some(b,\<sigma>') \<Rightarrow> (\<sigma>'  \<Turnstile> (s \<leftarrow> mbind S ioprog ; return (P (b#s)))))"
apply(case_tac "ioprog a \<sigma>")
apply(auto simp: exec_mbindFSave_failure  exec_mbindFSave_success split: prod.splits)
apply(subst (asm) exec_mbindFSave_success,assumption,simp_all)
by(subst exec_mbindFSave_success,assumption,simp)+


text{* Universal splitting and symbolic execution rule *}
lemma exec_mbindFSave_E:
assumes seq : "(\<sigma> \<Turnstile> (s \<leftarrow> mbind\<^sub>F\<^sub>a\<^sub>i\<^sub>l\<^sub>S\<^sub>a\<^sub>v\<^sub>e (a#S) ioprog ;  (P s)))"
  and   none: "ioprog a \<sigma> = None \<Longrightarrow> (\<sigma> \<Turnstile> (P [])) \<Longrightarrow> Q"
  and   some: "\<And> b \<sigma>'. ioprog a \<sigma> = Some(b,\<sigma>') \<Longrightarrow> (\<sigma>' \<Turnstile> (s \<leftarrow> mbind\<^sub>F\<^sub>a\<^sub>i\<^sub>l\<^sub>S\<^sub>a\<^sub>v\<^sub>e S ioprog;(P (b#s)))) \<Longrightarrow> Q "
shows   "Q"
using seq
proof(cases "ioprog a \<sigma>")  
   case None  assume ass:"ioprog a \<sigma> = None" show "Q" 
        apply(rule none[OF ass])
        apply(insert ass, erule_tac ioprog1=ioprog in exec_mbindFSave_failure[THEN iffD1],rule seq)
        done
next
   case (Some aa) assume ass:"ioprog a \<sigma> = Some aa" show "Q" 
        apply(insert ass,cases "aa",simp, rename_tac "out" "\<sigma>'")
        apply(erule some)
        apply(insert ass,simp)
        apply(erule_tac ioprog1=ioprog in exec_mbindFSave_success[THEN iffD1],rule seq)
        done
qed

text{* The next rule reveals the particular interest in deduction;
       as an elimination rule, it allows for a linear conversion of a validity judgement
       @{term "mbind\<^sub>F\<^sub>a\<^sub>i\<^sub>l\<^sub>S\<^sub>t\<^sub>o\<^sub>p"} over an input list @{term "S"} into a constraint system; without any 
       branching ... Symbolic execution can even be stopped tactically whenever 
       @{term "ioprog a \<sigma> = Some(b,\<sigma>')"} comes to a contradiction. *}
lemma exec_mbindFStop_E:
assumes seq : "(\<sigma> \<Turnstile> (s \<leftarrow> mbind\<^sub>F\<^sub>a\<^sub>i\<^sub>l\<^sub>S\<^sub>t\<^sub>o\<^sub>p (a#S) ioprog ; (P s)))"
  and   some: "\<And>b \<sigma>'. ioprog a \<sigma> = Some(b,\<sigma>') \<Longrightarrow> (\<sigma>'\<Turnstile> (s \<leftarrow> mbind\<^sub>F\<^sub>a\<^sub>i\<^sub>l\<^sub>S\<^sub>t\<^sub>o\<^sub>p S ioprog;(P(b#s)))) \<Longrightarrow> Q"
shows   "Q"
using seq
proof(cases "ioprog a \<sigma>")  
   case None  assume ass:"ioprog a \<sigma> = None" show "Q" 
        apply(insert ass seq)
        apply(drule_tac \<sigma>=\<sigma> and S=S and M=P in exec_mbindFStop_failure, simp)
        done
next
   case (Some aa) assume ass:"ioprog a \<sigma> = Some aa" show "Q" 
        apply(insert ass,cases "aa",simp, rename_tac "out" "\<sigma>'")
        apply(erule some)
        apply(insert ass,simp)
        apply(erule_tac ioprog1=ioprog in exec_mbindFStop_success[THEN iffD1],rule seq)
        done
qed


lemma exec_mbindFPurge_E:
assumes seq : "(\<sigma> \<Turnstile> (s \<leftarrow> mbind\<^sub>F\<^sub>a\<^sub>i\<^sub>l\<^sub>P\<^sub>u\<^sub>r\<^sub>g\<^sub>e (a#S) ioprog ;  (P s)))"
  and   none: "ioprog a \<sigma> = None \<Longrightarrow> (\<sigma> \<Turnstile> (s \<leftarrow> mbind\<^sub>F\<^sub>a\<^sub>i\<^sub>l\<^sub>P\<^sub>u\<^sub>r\<^sub>g\<^sub>e S ioprog;(P (s)))) \<Longrightarrow> Q"
  and   some: "\<And> b \<sigma>'. ioprog a \<sigma> = Some(b,\<sigma>') \<Longrightarrow> (\<sigma>' \<Turnstile> (s \<leftarrow> mbind\<^sub>F\<^sub>a\<^sub>i\<^sub>l\<^sub>P\<^sub>u\<^sub>r\<^sub>g\<^sub>e S ioprog;(P (b#s)))) \<Longrightarrow> Q "
shows   "Q"
using seq
proof(cases "ioprog a \<sigma>")  
   case None  assume ass:"ioprog a \<sigma> = None" show "Q" 
        apply(rule none[OF ass])
        apply(insert ass, erule_tac ioprog1=ioprog in exec_mbindFPurge_failure[THEN iffD1],rule seq)
        done
next
   case (Some aa) assume ass:"ioprog a \<sigma> = Some aa" show "Q" 
        apply(insert ass,cases "aa",simp, rename_tac "out" "\<sigma>'")
        apply(erule some)
        apply(insert ass,simp)
        apply(erule_tac ioprog1=ioprog in exec_mbindFPurge_success[THEN iffD1],rule seq)
        done
qed


lemma assert_disch1 :" P \<sigma> \<Longrightarrow> (\<sigma> \<Turnstile> (x \<leftarrow> assert\<^sub>S\<^sub>E P; M x)) = (\<sigma> \<Turnstile> (M True))"
by(auto simp: bind_SE_def assert_SE_def valid_SE_def)

lemma assert_disch2 :" \<not> P \<sigma> \<Longrightarrow> \<not> (\<sigma> \<Turnstile> (x \<leftarrow> assert\<^sub>S\<^sub>E P ; M s))"
by(auto simp: bind_SE_def assert_SE_def valid_SE_def)

lemma assert_disch3 :" \<not> P \<sigma> \<Longrightarrow> \<not> (\<sigma> \<Turnstile> (assert\<^sub>S\<^sub>E P))"
by(auto simp: bind_SE_def assert_SE_def valid_SE_def)

lemma assert_D : "(\<sigma> \<Turnstile> (x \<leftarrow> assert\<^sub>S\<^sub>E P; M x)) \<Longrightarrow> P \<sigma> \<and> (\<sigma> \<Turnstile> (M True))"
by(auto simp: bind_SE_def assert_SE_def valid_SE_def split: HOL.split_if_asm)

lemma assume_D : "(\<sigma> \<Turnstile> (x \<leftarrow> assume\<^sub>S\<^sub>E P; M x)) \<Longrightarrow> \<exists> \<sigma>. (P \<sigma> \<and>  \<sigma> \<Turnstile> (M ()))"
apply(auto simp: bind_SE_def assume_SE_def valid_SE_def split: HOL.split_if_asm)
apply(rule_tac x="Eps P" in exI, auto)
apply(rule_tac x="True" in exI, rule_tac x="b" in exI)
apply(subst Hilbert_Choice.someI,assumption,simp)
apply(subst Hilbert_Choice.someI,assumption,simp)
done
text{* These two rule prove that the SE Monad in connection with the notion of valid sequence
is actually sufficient for a representation of a Boogie-like language. The SBE monad with explicit
sets of states --- to be shown below --- is strictly speaking not necessary (and will therefore
be discontinued in the development). *}

term "if\<^sub>S\<^sub>E P then B\<^sub>1 else B\<^sub>2 fi"

lemma if_SE_D1 : "P \<sigma> \<Longrightarrow> (\<sigma> \<Turnstile> (if\<^sub>S\<^sub>E P then B\<^sub>1 else B\<^sub>2 fi)) = (\<sigma> \<Turnstile> B\<^sub>1)"
by(auto simp: if_SE_def valid_SE_def)

lemma if_SE_D2 : "\<not> P \<sigma> \<Longrightarrow> (\<sigma> \<Turnstile> (if\<^sub>S\<^sub>E P then B\<^sub>1 else B\<^sub>2 fi)) = (\<sigma> \<Turnstile> B\<^sub>2)"
by(auto simp: if_SE_def valid_SE_def)

lemma if_SE_split_asm : " (\<sigma> \<Turnstile> (if\<^sub>S\<^sub>E P then B\<^sub>1 else B\<^sub>2 fi)) = ((P \<sigma> \<and> (\<sigma> \<Turnstile> B\<^sub>1)) \<or> (\<not> P \<sigma> \<and> (\<sigma> \<Turnstile> B\<^sub>2)))"
by(cases "P \<sigma>",auto simp: if_SE_D1 if_SE_D2)

lemma if_SE_split : " (\<sigma> \<Turnstile> (if\<^sub>S\<^sub>E P then B\<^sub>1 else B\<^sub>2 fi)) = ((P \<sigma> \<longrightarrow> (\<sigma> \<Turnstile> B\<^sub>1)) \<and> (\<not> P \<sigma> \<longrightarrow> (\<sigma> \<Turnstile> B\<^sub>2)))"
by(cases "P \<sigma>", auto simp: if_SE_D1 if_SE_D2)


lemma if_SE_execE:
  assumes A: "\<sigma> \<Turnstile> (if\<^sub>S\<^sub>E P then B\<^sub>1 else B\<^sub>2 fi)"
   and   B: "P \<sigma> \<Longrightarrow> \<sigma> \<Turnstile> B\<^sub>1 \<Longrightarrow> Q"
   and   C: "\<not> P \<sigma>\<Longrightarrow> \<sigma> \<Turnstile> B\<^sub>2 \<Longrightarrow> Q"
  shows  "Q"
by(insert A [simplified if_SE_split],cases  "P \<sigma>", simp_all, auto elim: B C)


lemma [code]:
  "(\<sigma> \<Turnstile> m) = (case (m \<sigma>) of None  \<Rightarrow> False | (Some (x,y))  \<Rightarrow> x)"
  apply(simp add: valid_SE_def)
  apply(cases "m \<sigma> = None", simp_all) 
  apply(insert not_None_eq, auto)
done


text{* Test-Refinements will be stated in terms of the failsave @{term mbind}, opting 
       more generality. The following lemma allows for an  optimization both in 
       test execution as well as in symbolic execution for an important special case of
       the post-codition: Whenever the latter has the constraint that the length of input and 
       output sequence equal each other (that is to say: no failure occured), failsave mbind
       can be reduced to failstop mbind ... *}
lemma mbindFSave_vs_mbindFStop : 
  "(\<sigma> \<Turnstile> (os \<leftarrow> (mbind\<^sub>F\<^sub>a\<^sub>i\<^sub>l\<^sub>S\<^sub>a\<^sub>v\<^sub>e \<iota>s ioprog); return(length \<iota>s = length os \<and> P \<iota>s os))) = 
   (\<sigma> \<Turnstile> (os \<leftarrow> (mbind\<^sub>F\<^sub>a\<^sub>i\<^sub>l\<^sub>S\<^sub>t\<^sub>o\<^sub>p \<iota>s ioprog); return(P \<iota>s os)))"
  apply(rule_tac x=P in spec)
  apply(rule_tac x=\<sigma> in spec)
  proof(induct "\<iota>s") 
     case Nil show ?case by(simp_all add: mbind_try try_SE_def del: Monads.mbind.simps)
     case (Cons a \<iota>s) show ?case
          apply(rule allI, rename_tac "\<sigma>",rule allI, rename_tac "P")
          apply(insert Cons.hyps)
          apply(case_tac "ioprog a \<sigma>")
          apply(simp only: exec_mbindFSave_failure exec_mbindFStop_failure, simp)
          apply(simp add:  split_paired_all del: Monads.mbind.simps )
          apply(rename_tac "\<sigma>'") 
          apply(subst exec_mbindFSave_success, assumption)
          apply(subst (2) exec_bind_SE_success, assumption)
          apply(erule_tac x="\<sigma>'" in allE)
          apply(erule_tac x="\<lambda>\<iota>s s. P (a # \<iota>s) (aa # s)" in allE) (* heureka ! *)
          apply(simp)
      done
  qed


lemma mbind\<^sub>F\<^sub>a\<^sub>i\<^sub>l\<^sub>S\<^sub>a\<^sub>v\<^sub>e_vs_mbind\<^sub>F\<^sub>a\<^sub>i\<^sub>l\<^sub>S\<^sub>t\<^sub>o\<^sub>p:
assumes A: "\<forall> \<iota> \<sigma>. ioprog \<iota> \<sigma> \<noteq> None"
shows      "(\<sigma> \<Turnstile> (os \<leftarrow> (mbind\<^sub>F\<^sub>a\<^sub>i\<^sub>l\<^sub>S\<^sub>a\<^sub>v\<^sub>e \<iota>s ioprog); P os)) = 
            (\<sigma> \<Turnstile> (os \<leftarrow> (mbind\<^sub>F\<^sub>a\<^sub>i\<^sub>l\<^sub>S\<^sub>t\<^sub>o\<^sub>p \<iota>s ioprog); P os))" 
proof(induct "\<iota>s") print_cases
  case Nil show ?case by simp
next 
  case (Cons a \<iota>s) 
       from Cons.hyps                           
       have B:"\<forall> S f \<sigma>. mbind\<^sub>F\<^sub>a\<^sub>i\<^sub>l\<^sub>S\<^sub>a\<^sub>v\<^sub>e S f \<sigma> \<noteq> None " by simp
       have C:"\<forall>\<sigma>. mbind\<^sub>F\<^sub>a\<^sub>i\<^sub>l\<^sub>S\<^sub>t\<^sub>o\<^sub>p \<iota>s ioprog \<sigma> = mbind\<^sub>F\<^sub>a\<^sub>i\<^sub>l\<^sub>S\<^sub>a\<^sub>v\<^sub>e \<iota>s ioprog \<sigma>" 
               apply(induct \<iota>s, simp)
               apply(rule allI,rename_tac "\<sigma>")
               apply(simp add: Monads.mbind'.simps(2))
               apply(insert A, erule_tac x="a" in allE)
               apply(erule_tac x="\<sigma>" and P="\<lambda>\<sigma> . ioprog a \<sigma> \<noteq> None" in allE)
               apply(auto split:option.split)
               done
       show ?case 
       apply(insert A,erule_tac x="a" in allE,erule_tac x="\<sigma>" in allE)
       apply(simp, elim exE)
       apply(rename_tac  "out" "\<sigma>'")
       apply(insert B, erule_tac x=\<iota>s in allE, erule_tac x=ioprog in allE, erule_tac x=\<sigma>' in allE)
       apply(subst(asm) not_None_eq, elim exE)
       apply(subst  Monads.exec_bind_SE_success)
       apply(simp   split: option.split, auto)
       apply(rule_tac s="(\<lambda> a b c. a # (fst c)) out \<sigma>' (aa, b)" in trans, simp,rule refl)
       apply(rule_tac s="(\<lambda> a b c. (snd c)) out \<sigma>' (aa, b)" in trans, simp,rule refl)
       apply(simp_all)
       apply(subst  Monads.exec_bind_SE_success, assumption)
       apply(subst  Monads.exec_bind_SE_success)
       apply(rule_tac s="Some (aa, b)" in  trans,simp_all add:C)
       apply(subst(asm)  Monads.exec_bind_SE_success, assumption)
       apply(subst(asm)  Monads.exec_bind_SE_success)
       apply(rule_tac s="Some (aa, b)" in  trans,simp_all add:C)
    done
qed

  
section{* Valid Test Sequences in the State Exception Backtrack Monad *}
text{* This is still an unstructured merge of executable monad concepts
and specification oriented high-level properties initiating test procedures. *}

definition valid_SBE :: "'\<sigma> \<Rightarrow> ('a,'\<sigma>) MON\<^sub>S\<^sub>B\<^sub>E \<Rightarrow> bool" (infix "\<Turnstile>\<^sub>S\<^sub>B\<^sub>E" 15)
where "\<sigma> \<Turnstile>\<^sub>S\<^sub>B\<^sub>E m \<equiv> (m \<sigma> \<noteq> None)"
text{* This notation consideres all non-failures as valid. *}


lemma assume_assert: "(\<sigma> \<Turnstile>\<^sub>S\<^sub>B\<^sub>E ( _ :\<equiv> assume\<^sub>S\<^sub>B\<^sub>E P ; assert\<^sub>S\<^sub>B\<^sub>E Q)) = (P \<sigma> \<longrightarrow> Q \<sigma>)" 
  by(simp add: valid_SBE_def assume_SBE_def assert_SBE_def bind_SBE_def)

lemma assert_intro: "Q \<sigma> \<Longrightarrow> \<sigma> \<Turnstile>\<^sub>S\<^sub>B\<^sub>E (assert\<^sub>S\<^sub>B\<^sub>E Q)"
  by(simp add: valid_SBE_def assume_SBE_def assert_SBE_def bind_SBE_def)

lemma assume_dest: 
  "\<lbrakk> \<sigma> \<Turnstile>\<^sub>S\<^sub>B\<^sub>E (x :\<equiv> assume\<^sub>S\<^sub>B\<^sub>E Q; M x); Q \<sigma>' \<rbrakk> \<Longrightarrow> \<sigma> \<Turnstile>\<^sub>S\<^sub>B\<^sub>E M ()"
  apply(auto simp: valid_SBE_def assume_SBE_def assert_SBE_def bind_SBE_def)
  apply(cases "Q \<sigma>",simp_all)
  oops

text{* This still needs work. What would be needed is a kind
       of wp - calculus that comes out of that. So far: nope. *}

subsection{* Legacy Bindings *}


lemma valid_true[simp]: (* legacy: special case *)
  "(\<sigma> \<Turnstile> (s \<leftarrow> return x ; return (P s))) = P x" by simp


(*
lemmas valid_both = exec_mbindFSave (* legacy *)
lemmas valid_success = exec_mbindFSave_success (* legacy *)
lemmas valid_success'' = exec_mbindFSave_success(* legacy *)
lemmas valid_success' = exec_bind_SE_success (* legacy *)
lemmas valid_failure = exec_mbindFSave_failure (* legacy : *)
lemmas valid_failure' = exec_bind_SE_failure (* legacy *)
lemmas valid_failure''=valid_failure (* legacy : *)
lemmas valid_failure''' = exec_mbindFStop_failure (* legacy : *)
lemmas valid_propagate_fail = exec_fail_SE (* legacy *)
lemmas valid_propagate_fail' = exec_fail_SE' (* legacy *)
lemmas valid_propoagate_3' = valid_propagate_fail' (* legacy *)
lemmas valid_propagate_2 = exec_bind_SE_success''(* legacy *)
lemmas valid_propagate_1 = exec_unit_SE (* legacy *)
lemmas valid_successElem = exec_bind_SE_success' (* legacy *)
lemmas valid_propagate_2' = exec_bind_SE_success'''(* legacy *)
lemmas valid_propagate_2'' = exec_bind_SE_success'''' (* legacy *)
lemmas valid_propoagate_3 = exec_unit_SE' (* legacy *)
  *)
(* legacy ?: 
lemma valid_success'':
"ioprog a \<sigma> = Some(b,\<sigma>') \<Longrightarrow>
   (\<sigma>  \<Turnstile> (s \<leftarrow> mbind (a#S) ioprog ; return (P s))) =
   (\<sigma>' \<Turnstile> (s \<leftarrow> mbind S ioprog ; return (P (b#s))))"
unfolding valid_SE_def unit_SE_def bind_SE_def 
by(cases "mbind S ioprog \<sigma>'", auto)
*) 

end
