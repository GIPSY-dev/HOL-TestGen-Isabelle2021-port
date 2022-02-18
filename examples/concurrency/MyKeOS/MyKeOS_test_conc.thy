(*****************************************************************************
 * HOL-TestGen --- theorem-prover based test case generation
 *                 http://www.brucker.ch/projects/hol-testgen/
 *
 * Bank.thy --- an BirthdayBook inspired, elementary
 *              example for sequence testing based on a 
 *              deterministic specification.
 *
 * This file is part of HOL-TestGen.
 *
 * Copyright (c) 2009-15 Univ. Paris-Sud, France
 *               2009-15 Achim D. Brucker, Germany
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

theory  MyKeOS_test_conc
imports MyKeOS (* includes Testing *) 
        "~~/src/HOL/Library/Code_Target_Numeral"
        "Code_gdb_script"
begin

declare [[testgen_profiling]]

section{* Interleaving *}
text{* The purpose of this example is to model system calls that consists of a number of
   (internal) atomic actions; the global behavior is presented by the interleaving of 
   the actions actions *}

definition "SEND tid tid' m = [send tid tid' m, status tid]"

definition "REC tid tid' m = [rec tid tid' m, status tid]"

value "interleave (SEND 5 0 m) (REC 0 5 m )"

text{* In the following, we do a predicate abstraction on the interleave language, leading to
an automaton represented as a set of rewrites ... *}
fun Interleave :: "in_c list \<Rightarrow> nat \<times> nat \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" (infixl "\<bowtie>"100)
where    "S \<bowtie> (a, b) = (\<lambda> tid m m' . (S \<in> interleave (drop a (SEND tid 5 m))
                                                      (drop b (REC 5 tid m'))))"
lemma init_Interleave : "(S \<bowtie> (0, 0)) tid m m' =  (S \<in> interleave (SEND tid 5 m) (REC 5 tid m'))"
by simp

value "interleave (SEND 0 5 m) (REC 5 0 m')"

find_theorems name:"Interleave"
(* refusals *)
lemma ref_mt [simp]: "\<not>([] \<bowtie> (0, 0)) tid m m'"
by (simp add:REC_def SEND_def)

lemma ref_0_0 [simp]: " \<not>(((status a) # R) \<bowtie> (0, 0)) tid m m' "
by (simp add:REC_def SEND_def)


lemma ref_1_0 [simp]: "a \<noteq> tid \<Longrightarrow>\<not>(((status a) # R) \<bowtie> (1, 0)) tid m m' "
by (simp add:REC_def SEND_def)


lemma ref_0_1 [simp]: "a \<noteq> 5 \<Longrightarrow> \<not>(((status a) # R) \<bowtie> (0, 1)) tid m m' "
by (simp add:REC_def SEND_def)

lemma ref_1_1 [simp]: "a \<noteq> 5 \<Longrightarrow> a \<noteq> tid \<Longrightarrow>  \<not>(((status a) # R) \<bowtie> (1, 1)) tid m m' "
by (simp add:REC_def SEND_def)

lemma ref_3_1 [simp]: "a \<noteq> 5 \<Longrightarrow> \<not>(((status a) # R) \<bowtie> (3, 1)) tid m m' "
by (simp add:REC_def SEND_def)

lemma ref_1_3 [simp]: "a \<noteq> tid \<Longrightarrow> \<not>(((status a) # R) \<bowtie> (1, 3)) tid m m' "
by (simp add:REC_def SEND_def)


(* transducer rules -- helps nothing for the moment. Is an experiment to
   be re-conciled with gen_test_cases. *)

value "(((a # R) \<bowtie> (0, 0)) tid m m' )"
lemma trans_0_0 [simp]: "(((a # R) \<bowtie> (0, 0)) tid m m' ) = 
                     ((a = send tid 5 m \<and> (R \<bowtie> (1, 0)) tid m m' ) \<or>
                      (a = rec 5 tid m' \<and> (R \<bowtie> (0, 1)) tid m m' ))"
apply (simp add: SEND_def REC_def) 
by auto

lemma trans_1_0 [simp]: "(((a # R) \<bowtie> (1, 0)) tid m m') = 
                     ((a = rec 5 tid m' \<and> (R \<bowtie> (1, 1)) tid m m') \<or>
                      (a = status tid \<and> (R \<bowtie> (2, 0)) tid m m'))"
apply (simp add:SEND_def REC_def)
by auto

lemma trans_2_0 [simp]: "(((a # R) \<bowtie> (2, 0)) tid m m') = 
                        ( (a = rec 5 tid m' \<and> R = [status 5]))"
by (simp add: SEND_def REC_def)

lemma trans_2_1 [simp]: "(((a # R) \<bowtie> (2, 1)) tid m m') = (a = status 5 \<and> R = [])"
by (simp add: SEND_def REC_def)


value "interleave (drop 0 (SEND tid  m m'))(drop 0 (REC tid m'' m'''))"

text{* TestData Hack:*} 

lemma PO_norm0 [simp]: "PO True" by(simp add: PO_def)


text{* The following scenario is meant to describe the symbolic execution step by step. *}

declare Monads.mbind'_bind [simp del]  (* stop eliminating elimination of @{term "mbind\<^sub>F\<^sub>a\<^sub>i\<^sub>l\<^sub>S\<^sub>t\<^sub>o\<^sub>p"} *)

find_theorems "mbind\<^sub>F\<^sub>a\<^sub>i\<^sub>l\<^sub>S\<^sub>t\<^sub>o\<^sub>p []"

lemma example_symbolic_execution_simulation :
   assumes H:  "S = [send tid 1 m, rec tid 0 m', rec tid 1 m''', status tid ]"
   assumes SE: "\<sigma>\<^sub>0 \<Turnstile> (s \<leftarrow> mbind\<^sub>F\<^sub>a\<^sub>i\<^sub>l\<^sub>S\<^sub>t\<^sub>o\<^sub>p S SYS; return (x = s))"
   shows       "P"
apply(insert SE H)
apply(hypsubst)
apply(tactic "ematch_tac @{context} [@{thm status.exec_mbindFStop_E}, 
                                     @{thm receive.exec_mbindFStop_E},
                                     @{thm send.exec_mbindFStop_E}] 1")
apply(tactic "ematch_tac @{context} [@{thm status.exec_mbindFStop_E}, 
                                     @{thm receive.exec_mbindFStop_E},
                                     @{thm send.exec_mbindFStop_E}] 1")
apply(tactic "ematch_tac @{context} [@{thm status.exec_mbindFStop_E}, 
                                     @{thm receive.exec_mbindFStop_E},
                                     @{thm send.exec_mbindFStop_E}] 1")
apply(tactic "ematch_tac @{context} [@{thm status.exec_mbindFStop_E}, 
                                     @{thm receive.exec_mbindFStop_E},
                                     @{thm send.exec_mbindFStop_E}] 1")
apply(tactic "ematch_tac @{context} [@{thm status.exec_mbindFStop_E}, 
                                     @{thm receive.exec_mbindFStop_E},
                                     @{thm send.exec_mbindFStop_E},  
                                     @{thm valid_mbind'_mtE} ] 1")
apply simp 
oops

end
