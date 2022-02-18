(*****************************************************************************
* HOL-TestGen --- theorem-prover based test case generation
*                 http://www.brucker.ch/projects/hol-testgen/
*                                                                            
* RBT_seq_test.thy --- sequence testing red-black trees with hidden state
* This file is part of HOL-TestGen.
*
* Copyright (c) 2010      ETH Zurich, Switzerland
*               2010-2015 Achim D. Brucker, Germany
*               2016      The University of Sheffield, UK
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
(* $Id: RBT_test.thy 13155 2017-08-18 20:22:39Z brucker $ *)


chapter {* Testing Properties of Red-Black Trees *}


theory 
 RBT_test
imports 
 RBT_def
 Testing
 "~~/src/HOL/Library/Code_Target_Numeral"
begin

consts prog ::"int*int tree \<Rightarrow> int tree"

section{* Standard Unit-Testing of Red-Black-Trees*}

test_spec "(isord t \<and> isin (y::int) t \<and> 
            strong_redinv t \<and> blackinv t)
          \<longrightarrow> (blackinv(prog(y,t)))"
apply(gen_test_cases 5 1 "prog" simp: compare1 compare2 compare3)
mk_test_suite "red_and_black_inv"

section {* Test Data Generation *}
subsection {* Brute Force *}

text{* This fairly simple setup generates already 25 subgoals 
      containing 12 test cases, altogether with non-trivial 
      constraints. For achieving our test case, we 
      opt for a ``brute force'' attempt here: *}

(* declare [[testgen_iterations=200]] *)
declare [[testgen_iterations=0]]
gen_test_data "red_and_black_inv"

print_conc_tests "red_and_black_inv"

subsection {* Using Abstract Test Cases *}

test_spec "(isord t \<and> isin (y::int) t \<and> strong_redinv t \<and> blackinv t) \<longrightarrow> (blackinv(prog(y,t)))"
apply(gen_test_cases 3 1 "prog" simp: compare1 compare2 compare3)
mk_test_suite "red_and_black_inv2"

text{* By inspecting the constraints of the test theorem, one immediately 
 identifies predicates for which solutions are difficult to find
 by a random process (a measure for this difficulty could be the
 percentage of trees up to depth $k$ that make this predicate valid.
 One can easily convince oneself that this percentage is decreasing).

 Repeatedly, ground instances are needed for:
 \begin{enumerate}
 \item \verb+max_B_height ?X = 0+
 \item \verb+max_B_height ?Y = max_B_height ?Z+
 \item \verb+blackinv ?X+
 \item \verb+redinv ?X+
 \end{enumerate}
 *} 

text{* The point is that enumerating some examples of 
 ground instances for these predicates is fairly easy if
 one bears its informal definition in mind.
 For  \verb+max_B_height ?X+ this is: 
 "maximal number of black nodes on any path from root to leaf".
 So let's enumerate some trees who contain no black nodes:
 *}

lemma  maxB_0_1: "max_B_height (E:: int tree) = 0"
 by auto

lemma  maxB_0_2: "max_B_height (T R E (5::int) E) = 0"
 by auto

lemma  maxB_0_3: "max_B_height (T R (T R E 2 E) (5::int) E) = 0"
 by auto

lemma  maxB_0_4: "max_B_height (T R E (5::int) (T R E 7 E)) = 0"
 by auto

lemma  maxB_0_5: "max_B_height (T R (T R E 2 E) (5::int) (T R E 7 E)) = 0"
 by auto

text{* Note that these ground instances have already been produced
 with hindsight to the ordering constraints - ground instances must
 satisfy all the other constraints, otherwise they wouldn't help
 the solver at all. On the other hand, continuing with this
 enumeration doesn't help too much  since we start to enumerate
 trees that do not satisfy the red invariant. *}

(* weak red invariant: no red node has a red child *)  
 text{* A good overview over what is needed is given by the set of
 rules generated from the redinv-definition. We bring this into
 the form needed for a lemma *}

thm redinv.simps
lemma redinv_enumerate1: 
  "          ((x = E) 
              \<or> (\<exists> a y b. x = T B a y b \<and> redinv a \<and> redinv b)
              \<or> (\<exists> y. x = T R E y E)
              \<or> (\<exists> y am an ao. x = T R E y (T B am an ao) \<and> 
                               redinv (T B am an ao))
              \<or> (\<exists> ae af ag y. x = (T R (T B ae af ag) y E)  
                                   \<and>  redinv (T B ae af ag))
              \<or> (\<exists> ae af ag y bg bh bi. 
                               x = (T R (T B ae af ag) y (T B bg bh bi)) \<and> 
                               (redinv (T B ae af ag) \<and> 
                               redinv (T B bg bh bi)))) ==> redinv x"
 by(safe, simp_all)


lemma redinv_enumerate2: 
  "redinv x ==> ((x = E) 
              \<or> (\<exists> a y b. x = T B a y b \<and> redinv a \<and> redinv b)
              \<or> (\<exists> y. x = T R E y E)
              \<or> (\<exists> y am an ao. x = T R E y (T B am an ao) \<and> 
                               redinv (T B am an ao))
              \<or> (\<exists> ae af ag y. x = (T R (T B ae af ag) y E)  
                                   \<and>  redinv (T B ae af ag))
              \<or> (\<exists> ae af ag y bg bh bi. 
                               x = (T R (T B ae af ag) y (T B bg bh bi)) \<and> 
                               (redinv (T B ae af ag) \<and> 
                               redinv (T B bg bh bi))))"
  apply(induct x,simp,rule disjI2)
  apply(case_tac x1,simp_all)
  apply(case_tac x1a,simp_all)
  apply(case_tac x2,simp_all)
  apply(case_tac x21,simp_all)
  apply(case_tac x21,simp_all)
  apply(case_tac x2,simp_all)
  apply(case_tac x21a,simp_all)
  done 



lemma redinv_enumerate: 
  "redinv x =((x = E) 
              \<or> (\<exists> a y b. x = T B a y b \<and> redinv a \<and> redinv b)
              \<or> (\<exists> y. x = T R E y E)
              \<or> (\<exists> y am an ao. x = T R E y (T B am an ao) \<and> 
                               redinv (T B am an ao))
              \<or> (\<exists> ae af ag y. x = (T R (T B ae af ag) y E)  
                                   \<and>  redinv (T B ae af ag))
              \<or> (\<exists> ae af ag y bg bh bi. 
                               x = (T R (T B ae af ag) y (T B bg bh bi)) \<and> 
                               (redinv (T B ae af ag) \<and> 
                               redinv (T B bg bh bi))))"
apply(rule iffI)
apply(rule redinv_enumerate2, assumption)
apply(rule redinv_enumerate1, assumption)
done 
  

text{* *}
(*
redinv E = True
redinv (T B ?a ?y ?b) = (redinv ?a \<and> redinv ?b)
redinv (T R E ?x E) = True
redinv (T R E ?x (T B ?am ?an ?ao)) = redinv (T B ?am ?an ?ao)

(T R (T B ae af ag) y E)  \<and>  redinv (T B ae af ag)
(T R (T B ae af ag) y (T B bg bh bi)) \<and> 
   (redinv (T B ae af ag) \<and> redinv (T B bg bh bi))
*)

(* black invariant: number of black nodes equal on all paths from root 
  to leaf *)  


subsection {* An Alternative Approach with a little Theorem Proving *}

text{* This approach will suffice to generate the critical test data
      revealing the error in the sml/NJ library.

      Alternatively, one might:
      \begin{enumerate}
      \item use abstract test cases for the auxiliary predicates
            @{text redinv} and @{text blackinv},
      \item increase the depth of the test case generation and 
            introduce auxiliary lemmas, that allow for the elimination
            of unsatisfiable constraints,
      \item or applying more brute force.
      \end{enumerate}

   Of course, one might also apply a combination of these techniques
   in order to get a more systematic test than the one presented here.

   We will describe option 2 briefly in more detail: part of the 
   following lemmas require induction and real theorem proving, but
   help to refine constraints systematically.
  *}

lemma height_0: 
  "(max_B_height x = 0) = 
   (x = E \<or> (\<exists> a y b. x = T R a y b \<and> 
                      (max (max_B_height a) (max_B_height b)) = 0))"
 by(induct "x", simp_all,case_tac "x1",auto)


lemma max_B_height_dec:  "((max_B_height (T x t1 val t3)) = 0) \<Longrightarrow> (x = R) "
 by(case_tac "x",auto)


text{* This paves the way for the following testing scenario,
which separates the test generation phase from the introduction
of the uniformity hypothesis (and, thus, the introduction of
proof obligations). This way, we can manipulate the test theorem
before "freezing" it into the standard format amenable for
the test data generation phase. *}


test_spec "(isord t \<and> isin (y::int) t \<and> 
           strong_redinv t \<and> blackinv t)
          \<longrightarrow> (blackinv(prog(y,t)))"
txt{*... introduces locally into the proof-state
an option of \verb+gen_test_cases+ that omits constranit generation. *}
using[[testgen_no_finalize]]  
apply(gen_test_cases 3 1 "prog" simp: compare1 compare2 compare3
                                     max_B_height_dec)
txt{* ... intermediate steps ... *}
apply(simp_all only: height_0, simp_all add: max_0_0)
apply(simp_all only: height_0, simp_all add: max_0_0)
apply(safe,simp_all)
txt{* brings the test theorem back into the standard format. : *}
apply(tactic "TestGen.finalize_tac @{context} [\"prog\"]") 
mk_test_suite "red_and_black_inv3"

(* declare [[testgen_iterations=20]] *)
declare [[testgen_iterations=0]]
gen_test_data "red_and_black_inv3"

print_conc_tests "red_and_black_inv3"

(* TODO: Attribute setup / anti-quotation
text {* The inspection shows now a stream-lined, quite powerful test data
       set for our problem. Note that the "depth 3" parameter of the
       test case generation leads to "depth 2" trees, since the constructor
       \verb+E+ is counted. Nevertheless, this test case produces the
       error regularly (Warning: recall that randomization is involved; in 
       general, this makes the search faster (while requiring less
       control by the user) than brute force enumeration, 
       but has the prize that in rare cases the random solver does not find 
       the solution at all): 
       @{thm [display] "red_and_black_inv3.concrete_tests"} 
*}
*)
text {* When increasing the depth to 5, the test case generation is still
feasible - we had runs which took less than two minutes and resulted in 
348 test cases. *}

section {* Configuring the Code Generator *}

text{* We have to perform the usual setup of the internal Isabelle code
      generator, which involves providing suitable ground instances
      of generic functions (in current Isabelle) and the map of 
      the data structures to the data structures in the environment.

      Note that in this setup the mapping to the target program under
      test is done in the wrapper script, that also 
      maps our abstract trees to more concrete data structures 
      as used in the implementation. *}

declare [[testgen_setup_code="open IntRedBlackSet;",
          testgen_toString="wrapper.toString"]]

code_printing
 constant  prog => (SML) "(fn (v,t) => (wrapper.del (fn x =>  (Nat (IntInf.fromInt x)))  (IntInf.toInt o integer'_of'_nat))
                                      (( Nat (integer'_of'_int (v) ), wrapper.convT (fn x => Nat (integer'_of'_int x)) (t))))"

code_printing 
  type_constructor color => (SML) "color"

code_printing 
  type_constructor ml_order => (SML) "order"

code_printing 
  type_constructor tree => (SML) "_ wrapper.Tree "

code_printing 
  constant "compare" => (SML) "Key.compare (_,_)"

code_printing 
  constant "color.B" => (SML) "wrapper.B"

code_printing 
  constant "color.R" => (SML) "wrapper.R"

code_printing 
  constant "tree.E" => (SML) "wrapper.E"

code_printing 
   constant "tree.T" => (SML)  "(wrapper.T(_,_, _,_)) " 

text {* Now we can generate a test script (for both test data sets): *}
generate_test_script "red_and_black_inv"
thm "red_and_black_inv.test_script"
export_code  "red_and_black_inv.test_script" in SML
module_name TestScript file "impl/sml/red_and_black_inv_test_script.sml"

generate_test_script "red_and_black_inv3"
thm "red_and_black_inv3.test_script"
export_code  "red_and_black_inv3.test_script" in SML
module_name TestScript file "impl/sml/red_and_black_inv3_test_script.sml"



section {* Test Result Verification *}
text {*
 Running the test executable (either based on @{text "red_and_black_inv"}
 or on @{text "red_and_black_inv3"}) results in an output similar to 
{\small\begin{verbatim}
Test Results:
=============
Test  0 -     SUCCESS, result: E
Test  1 -     SUCCESS, result: T(R,E,67,E)
Test  2 -     SUCCESS, result: T(B,E,~88,E)
Test  3 - **  WARNING: pre-condition false (exception 
                                           during post_condition)
Test  4 - **  WARNING: pre-condition false (exception 
                                           during post_condition)
Test  5 -     SUCCESS, result: T(R,E,30,E)
Test  6 -     SUCCESS, result: T(B,E,73,E)
Test  7 - **  WARNING: pre-condition false (exception 
                                           during post_condition)
Test  8 - **  WARNING: pre-condition false (exception 
                                           during post_condition)
Test  9 - *** FAILURE: post-condition false, result: 
                      T(B,T(B,E,~92,E),~11,E)
Test 10 -     SUCCESS, result: T(B,E,19,T(R,E,98,E))
Test 11 -     SUCCESS, result: T(B,T(R,E,8,E),16,E)


Summary:
--------
Number successful tests cases: 7 of 12 (ca. 58%)
Number of warnings:            4 of 12 (ca. 33%)
Number of errors:              0 of 12 (ca. 0%)
Number of failures:            1 of 12 (ca. 8%)
Number of fatal errors:        0 of 12 (ca. 0%)

Overall result: failed 
===============
\end{verbatim}}
\begin{figure}
\centering
%\hfill
\subfigure[pre-state\label{fig:pre}]
 {\scalebox{0.3}{\includegraphics[keepaspectratio]{figures/avl_pre}}}
\hspace{.1cm}
\subfigure[correct result\label{fig:post}]
 {\hspace{.3cm}\scalebox{0.3}{\includegraphics[keepaspectratio]{figures/avl_post}}\hspace{.3cm}}
\hspace{.1cm}
\subfigure[result of sml/NJ\label{fig:smlpost}]
 {\hspace{.8cm}\scalebox{0.3}{\includegraphics[keepaspectratio]{figures/avl_post_sml}}\hspace{.8cm}}
%\hfill
\caption{Test Data for Deleting a Node in a Red-Black Tree\label{fig:red-black}}
\end{figure}
 The error that is typically found has the following property: Assuming the 
 red-black tree presented in Fig.~\ref{fig:pre}, deleting the node 
 with value $-42$ results in the tree presented in Fig.~\ref{fig:smlpost} 
 which obviously violates the black invariant (the expected result is 
 the balanced tree in Fig.~\ref{fig:post}). Increasing the depth to at least $4$ reveals 
 several test cases where unbalanced trees are returned from the SML implementation.
*}


subsection{* The "SMT" Approach *}
text{* Here, we use the SMT solver Z3 for the test data selection.
This requires a different set of additional lemmas for eliminating
the unbounded quantifiers in the test specification.  *}

text {* We will use the following definition in order to eliminate the unbounded quantifiers
occurring in the test specification. *}

fun tree_all_comp         :: "('a::LINORDER) tree \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> bool"
where
    tree_all_comp_empty :  "tree_all_comp E c y = True"
 |  tree_all_comp_branch : "tree_all_comp (T rb a x b) c y = ((c x y) \<and> (tree_all_comp a c y) \<and> (tree_all_comp b c y))"

text {* The following lemma states how the unbounded quantifier in the test specification
can be expressed using the function \verb+tree_all_comp+. *}

lemma all_eq: "(tree_all_comp a c y) = (\<forall> x. isin x a \<longrightarrow> c x y)"
apply(auto)
apply(erule rev_mp)+
apply(induct_tac a)
apply(auto)
apply(simp add: LINORDER_equal)
apply(erule rev_mp)+
apply(induct_tac a)
apply(auto)
apply(simp add: LINORDER_equal)
done

text {* In order to avoid lambda-expressions in the test specification that may be problematic
for SMT solvers, we define the following two specific tree comparison functions. *}

fun tree_all_less :: "('a::LINORDER) tree \<Rightarrow> 'a \<Rightarrow> bool"
where
    tree_all_less_d: "tree_all_less a y = (tree_all_comp a (\<lambda>u v .(compare u v) = LESS)) y"


fun tree_all_greater :: "('a::LINORDER) tree \<Rightarrow> 'a \<Rightarrow> bool"
where
    tree_all_greater_d: "tree_all_greater a y = (tree_all_comp a (\<lambda>u v.(compare u v) = GREATER)) y"

text {* Using these new functions, we are able to provide a new definition of isord that does
not rely on an unbounded quantifier. *}

fun isord'        :: "('a::LINORDER) tree \<Rightarrow> bool"
where
    isord_empty'  : "isord' E = True"
 |  isord_branch' : "isord' (T c a y b) = 
                    (isord' a \<and> isord' b 
                     \<and> (tree_all_less a y)
                     \<and> (tree_all_greater b y))"

lemma isord_subst: "isord t = isord' t"
apply(induct_tac t)
apply(auto)
apply(simp_all add: all_eq)
done

text {* We now instantiate the recursive definition of \verb+tree_all_comp+ in order to obtain
recursive definitions for \verb+tree_all_less+ and \verb+tree_all_greater+. *}

declare tree_all_less_d [simp del]
declare tree_all_greater_d [simp del]

lemmas tree_all_less_inv [simp] = tree_all_less_d[THEN sym]
lemmas tree_all_greater_inv [simp] = tree_all_greater_d[THEN sym]

declare tree_all_comp_branch [simp del]
lemmas tree_all_less_empty [simp] = tree_all_comp_empty[where c = "(\<lambda>x y.(compare x y) = LESS)",simplified]
lemmas tree_all_less_branch [simp] = tree_all_comp_branch [where c = "(\<lambda>x y.(compare x y) = LESS)", simplified]
lemmas tree_all_greater_empty [simp] = tree_all_comp_empty[where c = "(\<lambda>x y.(compare x y) = GREATER)", simplified]
lemmas tree_all_greater_branch [simp] = tree_all_comp_branch [where c = "(\<lambda>x y.(compare x y) = GREATER)", simplified]

declare isord_branch' [simp del]
lemmas isord_branch'' [simp] = isord_branch'[simplified]

declare [[testgen_no_finalize=false]]


test_spec "(isord t \<and> isin (y::int) t \<and>
           strong_redinv t \<and> blackinv t)
          \<longrightarrow> blackinv(prog(y,t))"
apply(simp add: isord_subst)
(* apply(tactic "simp_tac @{context}  1" )
ML_prf{* ALLGOALS *} *)
apply(gen_test_cases 5 1 "prog" simp: compare1 compare2 compare3)
mk_test_suite "red_and_black_inv_smt"

section {* Test Data Generation *}

(* turn on the SMT solver and shut off the random solver*)
declare [[testgen_SMT]]
declare [[testgen_iterations=0]]
declare [[smt_timeout = 300]]


(* We list the definitions that are used by the test theorem *)
declare tree.size(3) [testgen_smt_facts]
declare tree.size(4) [testgen_smt_facts]
declare color.size(3) [testgen_smt_facts]
declare color.size(4) [testgen_smt_facts]

declare isord_empty' [testgen_smt_facts]
declare isord_branch'' [testgen_smt_facts] 
declare tree_all_less_empty [testgen_smt_facts]
declare tree_all_less_branch [testgen_smt_facts]
declare tree_all_greater_empty [testgen_smt_facts]
declare tree_all_greater_branch [testgen_smt_facts]
declare isin.simps [testgen_smt_facts]
declare compare_int_def [testgen_smt_facts]
declare blackinv.simps [testgen_smt_facts]
declare max_B_height.simps [testgen_smt_facts]
declare strong_redinv.simps [testgen_smt_facts]
declare redinv.simps [testgen_smt_facts]

gen_test_data "red_and_black_inv_smt"

print_conc_tests "red_and_black_inv_smt"
print_upos "red_and_black_inv_smt"            (* They are unfeasible *)
thm "red_and_black_inv_smt.test_thm"
thm "red_and_black_inv_smt.test_thm_inst"

end
