(*****************************************************************************
 * HOL-TestGen --- theorem-prover based test case generation
 *                 http://www.brucker.ch/projects/hol-testgen/
 *                                                                            
 * AVL_def.thy --- testing AVL trees
 * This file is part of HOL-TestGen.
 *
 * Copyright (c) 2005-2007 ETH Zurich, Switzerland
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
(* $Id: AVL_test.thy 13156 2017-08-18 20:29:44Z brucker $ *)

chapter {* Testing AVL Properties *}

theory 
  AVL_test
imports 
  AVL_def
begin

subsection{* The "Interactive" Approach *}
text{* In this example, we demonstrate test-case generation whereby
the process is supported by a small number of inserted derived lemmas. 
The "backend", i.e. the test data selection phase, is realized by random solving.*}

declare [[testgen_profiling]]

text {* This test plan of the theory is more or less
        standard. However, we insert some minor theorems
        into the test theorem generation in order to
        ease the task of solving; this both improves speed
        of the generation and quality of the test.  *}

declare insert_base insert_rec [simp del]

lemma size_0[simp]: "(size x = 0) = (x = ET)"
  by(induct "x",auto)

lemma height_0[simp]: "(height x = 0) = (x = ET)"
  by(induct "x",auto) 

lemma max1 [simp]: "(max (Suc a) b) ~= 0"
  by(auto simp: max_def)

lemma max2 [simp]: "(max b (Suc a) ) ~= 0"
  by(auto simp: max_def)

text {* We adjust the random generator to a fairly restricted
        level and go for the solving phase. *}

declare [[testgen_iterations=0]]
(* declare [[testgen_iterations=200]] *)

test_spec "(is_bal t) \<longrightarrow> (is_bal (insert  x t))"
  apply(gen_test_cases "insert")
  mk_test_suite "foo"
  gen_test_data "foo"


print_conc_tests foo
thm foo.test_thm_inst

subsection{* The "SMT" Approach *}
text{* Here, we use the SMT solver Z3 for the test data selection.
This does require the insertion of additional lemmas.  *}

declare size_0 height_0 max1 max2 [simp del]

(* turn on the SMT solver and shut off the random solver*)
declare [[testgen_SMT]]
declare [[testgen_iterations=0]]

test_spec "(is_bal t) \<longrightarrow> (is_bal (insert  x t))"
  apply(gen_test_cases "insert")
  mk_test_suite "foo_smt"

(* We list the definitions that are used by the test theorem *)
declare is_bal.simps [testgen_smt_facts]
declare height.simps [testgen_smt_facts]
declare tree.size(3) [testgen_smt_facts]
declare tree.size(4) [testgen_smt_facts]

thm foo_smt.test_thm

gen_test_data "foo_smt"

print_conc_tests foo_smt
thm foo_smt.test_thm_inst

end
