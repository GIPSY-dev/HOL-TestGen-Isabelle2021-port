(*****************************************************************************
 * HOL-TestGen --- theorem-prover based test case generation
 *                 http://www.brucker.ch/projects/hol-testgen/
 *
 * UPF
 * This file is part of HOL-TestGen.
 *
 * Copyright (c) 2010-2012 ETH Zurich, Switzerland
 *               2010-2012 Achim D. Brucker, Germany
 *               2010-2012 Université Paris-Sud, France
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
(* $Id: TestSpecification.thy 13165 2017-08-19 07:28:10Z brucker $ *)


theory TestSpecification
imports 
  CodeGeneratorSetup 
  Testing
begin

lemmas p_pimps = p_simps PO_def

lemma PO_add: "PO P \<Longrightarrow> P"
by (simp add: PO_def)


datatype states = S0 | S1 | S2 | S3 | S4 | S5



fun is_trace1 where
 "is_trace1 S0  p i (x#InL)= (\<exists>r u. (x= createSCR u r p \<and> correct_role x \<and>
                                     is_trace1 S1  p i InL))"

|"is_trace1 S1  p i (x#InL)= (\<exists> r y z u. x = (addLR u r p y z) \<and> z =  {alice,bob,charlie} \<and> 
  correct_role x \<and> y > 0 \<and>
                                   is_trace1 S2  p i InL)"

|"is_trace1 S2 p i (x#InL) = (\<exists> r e u. x = appendEntry u r p i e \<and> correct_role x \<and> fst (snd e) > 0 
                                     \<and> is_trace1 S3  p i InL)"     
                     
|"is_trace1 S3  p i (x#InL)= (((\<exists> r u. x = (readSCR u r p) \<and> correct_role x \<and> is_trace1 S4  p i InL)
                         \<or> (\<exists> r u. x = (readEntry u r p i) \<and> correct_role x \<and> is_trace1 S4  p i InL)))"

|"is_trace1 S  p i x = (S = S4 \<and> x = [])"



definition 
  NB_trace1 :: "patient => entry_id \<Rightarrow> (Operation list) set" where
  "NB_trace1 p i = {x. (is_trace1 S0 p i x)}"


definition "accept_trace1" ::  "(Operation list) \<Rightarrow> bool" where
          "accept_trace1 t = 
  (t \<in> NB_trace1 14 3)"

definition "Smith = 14"
declare [[testgen_depth=5]]


lemma setCode[]: "{1,2,3} = set [1,2::user,3]"
apply auto
done



declare allow_simp[simp del]
declare deny_simp[simp del]


test_spec "\<lbrakk>length t = length X; accept_trace1  t\<rbrakk> \<Longrightarrow>
 ((\<emptyset>,\<emptyset>,UC0) \<Turnstile> (os \<leftarrow> mbind t PolMon; return (os=X))) \<longrightarrow>
  PUT t = X"
apply(simp add: accept_trace1_def)
apply (rule impI)+
apply (unfold  NB_trace1_def)
apply (simp)
apply (gen_test_cases PUT simp: bob_def charlie_def alice_def)
apply (tactic  
 "ALLGOALS(TestGen.ONLY_POS(
      (full_simp_tac (simpset_of @{context}addsimps @{thms p_simps PO_def 
            PolMon_def mon_prog}))
      THEN_ALL_NEW ( (rtac @{thm PO_add}))))")
apply(simp_all only:allow_simp deny_simp setCode)

store_test_thm "trace_test1"

declare [[testgen_SMT=true]]

declare [[testgen_iterations=50]]

gen_test_data "trace_test1"

thm trace_test1.pos

export_test_data "test_data_talk.xml" trace_test1


prepare_ts_code trace_test1
export_code trace_test1_test_script in Fsharp module_name TraceTest1 file "TraceTest1.fs"
thm trace_test1.test_data




(**************************************************************************************************)




fun is_trace2 where
 "is_trace2 S0  p i (x#InL)= (\<exists>r u. (x= createSCR u r p \<and> correct_role x \<and>
                                     is_trace2 S1  p i InL))"

|"is_trace2 S1  p i (x#InL)= (\<exists> r y z u. x = (addLR u r p y z) \<and> z =  {p} \<and> correct_role x \<and> y > 0 \<and>
                                   is_trace2 S2  p i InL)"

|"is_trace2 S2 p i (x#InL) = (\<exists> r e u i1. x = appendEntry u r p i1 e \<and> 
                                  i1\<in>i \<and> correct_role x \<and> fst (snd e) > 0 
                                     \<and> (is_trace2 S3  p i InL \<or> is_trace2 S2 p i InL))"     
                     
|"is_trace2 S3  p i (x#InL)= (((\<exists> r u. x = (readSCR u r p) \<and> correct_role x \<and> is_trace2 S4  p i InL)
                         \<or> (\<exists> r u i1. x = (readEntry u r p i1) \<and> i1\<in>i \<and>correct_role x \<and> 
                  is_trace2 S4  p i InL)))"

|"is_trace2 S  p i x = (S = S4 \<and> x = [])"



definition 
  NB_trace2 :: "patient => entry_id set\<Rightarrow> (Operation list) set" where
  "NB_trace2 p i = {x. (is_trace2 S0 p i x)}"


definition "accept_trace2" ::  "(Operation list) \<Rightarrow> bool" where
          "accept_trace2 t = 
  (t \<in> NB_trace2 2 {1,2,3})"


declare [[testgen_depth=5]]

test_spec "\<lbrakk>length t = length X; accept_trace2  t\<rbrakk> \<Longrightarrow>
 ((\<emptyset>,\<emptyset>,UC0) \<Turnstile> (os \<leftarrow> mbind t PolMon; return (os=X))) \<longrightarrow>
  PUT t = X"
apply(simp add: accept_trace2_def)
apply (rule impI)+
apply (unfold  NB_trace2_def)
apply (simp)
apply (gen_test_cases PUT simp: bob_def charlie_def alice_def)
apply (tactic  
 "ALLGOALS(TestGen.ONLY_POS(
      (full_simp_tac (simpset_of @{context}addsimps @{thms p_simps PO_def 
            PolMon_def mon_prog}))
      THEN_ALL_NEW ( (rtac @{thm PO_add}))))")
apply(simp_all only: setCode)
store_test_thm "trace_test2"

declare [[testgen_SMT=false]]

declare [[testgen_iterations=50]]

gen_test_data "trace_test2"

thm trace_test1.test_data

code_const set (Fsharp "Set.ofList")


prepare_ts_code trace_test2
export_code trace_test2_test_script in Fsharp module_name TraceTest2 file "TraceTest2.fs"
thm trace_test2.pos

end
