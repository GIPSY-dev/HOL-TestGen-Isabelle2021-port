(*****************************************************************************
 * HOL-TestGen --- theorem-prover based test case generation
 *                 http://www.brucker.ch/projects/hol-testgen/
 *                                                                            
 * List_test.thy --- testing infinite data structures (lists)
 * This file is part of HOL-TestGen.
 *
 * Copyright (c) 2005-2007 ETH Zurich, Switzerland
 *               2015-2016 Université Paris-Sud, France
 *               2015      Achim D. Brucker, Germany
 *               2016      The University of Sheffield, UK
 * 
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
(* $Id: List_test.thy 6651 2007-07-02 05:17:53Z brucker $ *)

chapter {* Test vs.~Proofs of List Properties - a Study *} 

theory 
  List_Verified_test
imports 
  List
  Testing
begin

text {* We repeat our standard List example and \emph{verify} the
resulting test-hypothesis wrt.~to a implementation given \emph{after}
the black-box test-case generation.

The example sheds some light one the nature of test vs.~deductive 
verification methods. *}

subsection {* Writing the Test Specification *}
text {*
We start by specifying a primitive recursive predicate describing
sorted lists:
*}
fun is_sorted:: "('a::ord) list \<Rightarrow> bool"
where "is_sorted  []     = True"
    | "is_sorted  (x#xs) = ((case xs of [] \<Rightarrow> True 
                                      | y#ys \<Rightarrow> (x < y) \<or> (x = y))
                                                  \<and> is_sorted xs)"

subsection {* Generating test cases *} 
text {*
Now we can automatically generate \emph{test cases}. Using the default
setup, we just apply our @{text gen_test_cases} on the free variable
$PUT$ (for program under test):
*}
test_spec "is_sorted(PUT (l::('a list)))"
  apply(gen_test_cases PUT)
txt {* 
      which leads to the test partitioning one would expect:
      @{subgoals [display, goals_limit=50]}
      Now we bind the test theorem to a particular named
       \emph{test environment}.
      *}
mk_test_suite "test_sorting"

gen_test_data "test_sorting"



text {* Note that by the following statements, the test data, the test
        hypotheses and the test theorem can be inspected interactively. *}
print_conc_tests test_sorting
print_thyps test_sorting
thm test_sorting.test_thm

(* TODO Attribute
text{* In this example, we will have a closer look on the test-hypotheses:

@{thm [display] test_sorting.test_hyps}

*}

*)

subsection{*Linking Tests and Uniformity *}
text{* The uniformity hypotheses and the tests establish together the fact: *}
lemma uniformity_vs_separation:
assumes test_0: "is_sorted (PUT [])"
assumes test_1: "EX (x::('a::linorder)). is_sorted (PUT [x])"
assumes test_2: "EX (x::('a::linorder)) xa. is_sorted (PUT [xa, x])"
assumes test_3: "EX (x::('a::linorder)) xa xaa. is_sorted (PUT [xaa, xa, x])"
assumes thyp_uniform_1:"THYP ((EX (x::('a::linorder)). is_sorted (PUT [x])) \<longrightarrow> 
                              (ALL (x::('a::linorder)). is_sorted (PUT [x])))"
assumes thyp_uniform_2:"THYP ((EX (x::('a::linorder)) xa. is_sorted (PUT [xa, x])) \<longrightarrow> 
                              (ALL (x::('a::linorder)) xa. is_sorted (PUT [xa, x])))"
assumes thyp_uniform_3:"THYP ((EX (x::('a::linorder)) xa xaa. is_sorted (PUT [xaa, xa, x])) \<longrightarrow> 
                              (ALL (x::('a::linorder)) xa xaa. is_sorted (PUT [xaa, xa, x])))"
shows   "ALL (l::('a::linorder)list). length l \<le> 3 \<longrightarrow> is_sorted (PUT l)"
apply(insert thyp_uniform_1 thyp_uniform_2 thyp_uniform_3)
apply(simp only: test_1 test_2 test_3 THYP_def)
apply safe
apply(rule_tac y=l in list.exhaust,simp add: test_0)
apply(rule_tac y=x22 in list.exhaust,simp)
apply(rule_tac y=x22a in list.exhaust,simp)
apply(hypsubst,simp)
done
text{* This means that if the provided tests are successful and all uniformity
hypotheses hold, the test specification holds up to measure 3. Note that this is 
a universal fact independent from any implementation. *}
 


subsection {* Giving a Program and verifying the Test Hypotheses for it. *}
text{* In the following, we give an instance for PUT in form of the usual
       insertion sort algorithm. Thus, we turn the black-box scenario into
       a white-box scenario. *}

primrec ins :: "['a::linorder, 'a list] \<Rightarrow> 'a list "
where   "ins x [] = [x]" |
        "ins x (y#ys) = (if (x < y) then x#(ins y ys) else (y#(ins x ys)))"

primrec sort :: "('a::linorder) list \<Rightarrow> 'a list"
where "sort [] = []" |
      "sort (x#xs) = ins x (sort xs)"

print_thyps test_sorting

lemma uniform_1:
"THYP ((EX x. is_sorted (sort [x])) \<longrightarrow> (ALL x. is_sorted (sort [x])))"
by(auto simp:THYP_def)

lemma uniform_2:
"THYP ((EX x xa. is_sorted (sort [xa, x])) \<longrightarrow> (ALL x xa. is_sorted (sort [xa, x])))"
by(auto simp:THYP_def)

text{* A Proof in Slow-Motion: *}
lemma uniform_2_b:
"THYP ((EX x xa. is_sorted (sort [xa, x])) \<longrightarrow> (ALL x xa. is_sorted (sort [xa, x])))"
apply(simp only: THYP_def)
apply(rule impI, thin_tac "_")
apply(rule allI)+
txt{*We reduce the test-hypothesis to the core and get: 
     @{subgoals [display, goals_limit=50]}.
     Unfolding \verb+sort+ yields:*}
apply(simp only: sort.simps)
txt{*@{subgoals [display, goals_limit=50]}
     and after unfolding of \verb+ins+ we get:*}
apply(simp only: ins.simps)
txt{* @{subgoals [display, goals_limit=50]}
      Case-splitting results in: *}
apply(case_tac "xa < x", simp_all only: if_True if_False)
txt{* @{subgoals [display, goals_limit=50]}
      Evaluation of \verb+is_sorted+ yields: *}
apply(simp_all only: is_sorted.simps)
txt{*@{subgoals [display, goals_limit=50]}
     which can be reduced to:*}
apply(simp_all)
txt{*@{subgoals [display, goals_limit=50]}
     which results by arithmetic reasoning to True.*}
apply(auto) 
done

text{*The proof reveals that the test is in fact irrelevant for the proof - 
the core is the case-distinction over all possible orderings of lists of
length 2; what we check is that \verb+is_sorted+ exactly fits to \verb+sort+.*}

lemma uniform_3:
"THYP ((EX x xa xaa. is_sorted (sort [xaa, xa, x])) \<longrightarrow> 
       (ALL x xa xaa. is_sorted (sort [xaa, xa, x])))"
txt{* The standard automated approach:
      \begin{verbatim}
        apply(auto simp:THYP_def)
      \end{verbatim}
      does (probably) not terminate due to mini - scoping.
      Instead, the following tactical proof exploits the
      structure of the uniformity hypothesis directly and leads to easily automated
      verification. It should still work for substantially larger
      test specifications. *}
apply(simp only: THYP_def)
apply(rule impI,(erule exE)+,(rule allI)+)
apply auto
done


lemma is_sorted_invariant_ins[rule_format]:
"is_sorted l \<longrightarrow> is_sorted (ins a l)"
apply(induct l)
apply(auto)
apply(rule_tac y=l in list.exhaust, simp,auto)
apply(rule_tac y=l in list.exhaust, auto)
apply(rule_tac y=x22 in list.exhaust, auto)
apply(subgoal_tac "a < x21",simp)
apply(erule Orderings.xtrans(10),simp)
apply(rule_tac y=x22 in list.exhaust, auto)
apply(rule_tac y=l in list.exhaust, auto)
done


lemma  testspec_proven: "is_sorted (sort l)"
by(induct l,simp_all,erule is_sorted_invariant_ins)

text{* Well, that's not too exciting, having \verb+is_sorted_invariant_ins+. *}


text{*Now we establish the same facts over tests. *}

lemma test_1: "is_sorted (sort [])" by auto
lemma test_2: "is_sorted (sort [1::int])" by auto
lemma test_3: "is_sorted (sort [1::int, 7])" by auto
lemma test_4: "is_sorted (sort [6::int, 4, 9])" by auto

text{* Now we establish the data-separation for the concrete implementation sort:*}

lemma separation_for_sort:
"ALL l::int list. length l \<le> 3 \<longrightarrow> is_sorted (sort l)"
apply(rule uniformity_vs_separation)
apply(rule test_1)
apply((rule exI)+,((rule test_2) | (rule test_3) | (rule test_4)))+
apply(rule uniform_1, rule uniform_2, rule uniform_3)
done

lemma regularity_over_local_test:
"THYP (3 < length (l::int list) \<longrightarrow> is_sorted (sort l))"

proof -
  have anchor : "\<And>a l. length (l:: int list) = 3 \<Longrightarrow> is_sorted (ins a (sort l))"
                apply(auto intro!: separation_for_sort[THEN spec,THEN mp] is_sorted_invariant_ins)
                done
  have step   : "\<And>a l. is_sorted (sort (l:: int list)) \<Longrightarrow> is_sorted (ins a (sort l))"
                apply(erule is_sorted_invariant_ins)
                done
  show ?thesis
  apply(simp only: THYP_def)
  txt{*@{subgoals [display, goals_limit=50]} *}
  apply(induct l, auto)
  txt{*@{subgoals [display, goals_limit=50]} *}
  apply(subgoal_tac "length l = 3")
  apply(auto elim!: anchor step)
  done
qed

text{* So -- tests and uniformity establish the induction hypothesis,
       and the rest is the induction step. In our case, this is
       exactly the invariant \verb+is_sorted_invariant_ins+. *}

text{* To sum up : Tests do not simplify proofs. They are too weak to be used inside
       the uniformity proofs. At least, \emph{some} of the uniformity results 
       establish the induction steps. While 
       \verb+separation_for_sort lemma+ might be generated automatically 
       from the test data, and while some interfacing inside the proof
       might also be generated, the theorem follows more or less ---
       disguised by a generic infra-structure --- proof of
       \verb+testspec_proven+, that is, standard induction. *}

end
