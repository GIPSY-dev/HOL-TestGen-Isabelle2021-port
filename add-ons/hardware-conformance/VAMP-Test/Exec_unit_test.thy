(*****************************************************************************
 * HOL-TestGen --- theorem-prover based test case generation
 *                 http://www.brucker.ch/projects/hol-testgen/
 *
 * Testing.thy --- wiring everything together.
 * This file is part of HOL-TestGen.
 *
 * Copyright (c) 2013-2017 Université Paris-Sud, France
 *               2016-2017 Virgina Tech, USA
 *               2016-2017 The University of Sheffield, UK
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

theory Exec_unit_test
imports Setup_test
          (*"~~/src/HOL/Library/Efficient_Nat"*)
begin

(*thm logic_instr_seq.test_thm*)

subsection{* Control-flow operations *}

test_spec "list_all is_jump_branch \<iota>s \<Longrightarrow> 
           (\<sigma>\<^sub>0 \<Turnstile> (s \<leftarrow> mbind (\<iota>s::instr list) exec\<^sub>V\<^sub>A\<^sub>M\<^sub>P;  assert\<^sub>S\<^sub>E (\<lambda>\<sigma>. \<sigma> .=. VAMP_MACHINE \<sigma>\<^sub>0 \<iota>s)))"
apply (gen_test_cases "VAMP_MACHINE" simp: is_logic_def)
mk_test_suite "branch_instr_seq"
declare [[testgen_iterations=50]]
gen_test_data "branch_instr_seq"

print_conc_tests branch_instr_seq

section {*Unit test schemes*}
subsection{* Control-flow operations *}
lemma is_jump_branch_eq: 
   "is_jump_branch i = (\<exists> nat int. i \<in> {(Ibeqz nat int), (Ibnez nat int), (Ijal int), 
                                   (Ijalr nat), (Ij int), (Ijr nat)})"
by (induct i, auto)
consts SUT:: "ASMcore_t \<Rightarrow> instr \<Rightarrow> ASMcore_t"

test_spec "is_jump_branch i \<Longrightarrow> \<sigma> = exec_instr \<sigma>\<^sub>0 i \<Longrightarrow> SUT \<sigma>\<^sub>0 i .=. \<sigma>"
apply (auto simp: is_jump_branch_eq)
 apply (gen_test_cases 1 0 "SUT" simp: reg_def \<sigma>\<^sub>0_def)
mk_test_suite "branch_instr"
declare [[testgen_iterations=50]]
gen_test_data "branch_instr"

thm branch_instr.test_thm_inst

subsection{* Logical operations *}

test_spec "is_logic i \<Longrightarrow> \<sigma> = exec_instr \<sigma>\<^sub>0 i \<Longrightarrow> SUT \<sigma>\<^sub>0 i .=. \<sigma>"
apply (auto simp: is_logic_def)
 apply (gen_test_cases 1 0 "SUT")
mk_test_suite "logic_instr"
declare [[testgen_iterations=50]]
gen_test_data "logic_instr"

thm logic_instr.test_thm

subsection{* Arithmetic operations *}

test_spec "is_arith i \<Longrightarrow> \<sigma> = exec_instr \<sigma>\<^sub>0 i \<Longrightarrow> SUT \<sigma>\<^sub>0 i .=. \<sigma>"
apply (auto simp: is_arith_def)
 apply (gen_test_cases 1 0 "SUT")
mk_test_suite "arith_instr"
declare [[testgen_iterations=50]]
gen_test_data "arith_instr"

thm arith_instr.test_thm
thm arith_instr.test_thm_inst

subsection{* Load store *}
test_spec "is_load_store' i \<Longrightarrow> \<sigma> = exec_instr \<sigma>\<^sub>0 i \<Longrightarrow> SUT \<sigma>\<^sub>0 i .=. \<sigma>"
 apply (auto simp: is_load_store'_def load_exec''_def Let_def \<sigma>\<^sub>0_def inc_pcs_st_def load_from_mem''_def
                   inc_pcp_by_def wlen_byte_def)
 apply (gen_test_cases 1 0 "SUT")
mk_test_suite "load_store_instr"
declare [[testgen_iterations=50]]
gen_test_data "load_store_instr"

thm load_store_instr.test_thm_inst


section{* Test-script generation *}

code_printing
  constant VAMP_MACHINE => (SML) "VAMP.execInstrs"

code_printing
  constant \<sigma>\<^sub>0 => (SML) "VAMP.sigma'_0"
code_printing
  type_constructor ASMcore_t_ext  \<rightharpoonup> (SML) "_ VAMP.aSMcore'_t'_ext"
| constant ASMcore_t_ext  \<rightharpoonup> (SML) "_ VAMP.aSMcore'_t'_ext"
| constant ASMcore_t.mm \<rightharpoonup> (SML) "VAMP.mm"
| constant ASMcore_t.gprs \<rightharpoonup> (SML)  "VAMP.gprs"
| constant ASMcore_t.sprs \<rightharpoonup> (SML) "VAMP.sprs"
| constant ASMcore_t.dpc \<rightharpoonup> (SML)"VAMP.dpc"
| constant ASMcore_t.pcp \<rightharpoonup>(SML) "VAMP.pcp"
| constant ASMcore_t.mm_update \<rightharpoonup> (SML) "VAMP.mm'_update"
| constant ASMcore_t.gprs_update \<rightharpoonup>(SML) "VAMP.gprs'_update"
| constant ASMcore_t.sprs_update \<rightharpoonup>(SML) "VAMP.sprs'_update"
| constant ASMcore_t.dpc_update \<rightharpoonup>(SML) "VAMP.dpc'_update"
| constant ASMcore_t.pcp_update \<rightharpoonup> (SML) "VAMP.pcp'_update"

code_printing
  type_constructor instr \<rightharpoonup> (SML) "VAMP.instr"
|constant Ilb \<rightharpoonup> (SML) "VAMP.Ilb (_, _, _)"
|constant Ilh \<rightharpoonup> (SML) "VAMP.Ilh (_, _, _)"
|constant Ilw \<rightharpoonup> (SML) "VAMP.Ilw (_, _, _)"
|constant Ilbu \<rightharpoonup>(SML) "VAMP.Ilbu (_, _, _)"
|constant Ilhu \<rightharpoonup>(SML) "VAMP.Ilhu (_, _, _)"
|constant Isb \<rightharpoonup>(SML) "VAMP.Isb (_, _, _)"
|constant Ish \<rightharpoonup>(SML) "VAMP.Ish (_, _, _)"
|constant Isw \<rightharpoonup> (SML) "VAMP.Isw (_, _, _)"
|constant Ilhgi \<rightharpoonup>(SML) "VAMP.Ilhgi (_, _)"
|constant Ilhg \<rightharpoonup> (SML) "VAMP.Ilhg (_, _)"
|constant Imovs2i \<rightharpoonup> (SML) "VAMP.Imovs2i (_, _)"
|constant Imovi2s \<rightharpoonup>(SML) "VAMP.Imovi2s (_, _)"
|constant Iaddio \<rightharpoonup>(SML) "VAMP.Iaddio (_, _, _)"
|constant Iaddi \<rightharpoonup>(SML) "VAMP.Iaddi (_, _, _)"
|constant Isubio \<rightharpoonup> (SML) "VAMP.Isubio (_, _, _)"
|constant Isubi \<rightharpoonup>(SML) "VAMP.Isubi (_, _, _)"
|constant Iandi \<rightharpoonup>(SML) "VAMP.Iandi (_, _, _)"
|constant Iori \<rightharpoonup>(SML)"VAMP.Iori (_, _, _)"
|constant Ixori \<rightharpoonup> (SML) "VAMP.Ixori (_, _, _)"
|constant Iaddo \<rightharpoonup>(SML) "VAMP.Iaddo (_, _, _)"
|constant Iadd \<rightharpoonup>(SML) "VAMP.Iadd (_, _, _)"
|constant Isubo \<rightharpoonup>(SML) "VAMP.Isubo (_, _, _)"
|constant Isub \<rightharpoonup>(SML) "VAMP.Isub (_, _, _)"
|constant Iand \<rightharpoonup>(SML) "VAMP.Iand (_, _, _)"
|constant Ior \<rightharpoonup>(SML) "VAMP.Ior (_, _, _)"
|constant Ixor \<rightharpoonup>(SML)"VAMP.Ixor (_, _, _)"
|constant Iclri \<rightharpoonup>(SML) "VAMP.Iclri (_)"
|constant Isgri \<rightharpoonup>(SML) "VAMP.Isgri (_, _, _)"
|constant Iseqi \<rightharpoonup>(SML) "VAMP.Iseqi (_, _, _)"
|constant Isgei \<rightharpoonup>(SML) "VAMP.Isgei (_, _, _)"
|constant Islsi \<rightharpoonup>(SML) "VAMP.Islsi (_, _, _)"
|constant Isnei \<rightharpoonup>(SML) "VAMP.Isnei (_, _, _)"
|constant Islei \<rightharpoonup>(SML) "VAMP.Islei (_, _, _)"
|constant Iseti \<rightharpoonup>(SML) "VAMP.Iseti (_)"
|constant Iclr \<rightharpoonup>(SML) "VAMP.Iclr (_)"
|constant Isgr \<rightharpoonup>(SML) "VAMP.Isgr (_, _, _)"
|constant Iseq \<rightharpoonup>(SML) "VAMP.Iseq (_, _, _)"
|constant Isge \<rightharpoonup>(SML) "VAMP.Isge (_, _, _)"
|constant Isls \<rightharpoonup>(SML) "VAMP.Isls (_, _, _)"
|constant Isne \<rightharpoonup>(SML) "VAMP.Isne (_, _, _)"
|constant Isle \<rightharpoonup>(SML) "VAMP.Isle (_, _, _)"
|constant Iset \<rightharpoonup>(SML) "VAMP.Iset (_)"
|constant Islli \<rightharpoonup>(SML) "VAMP.Islli (_, _, _)"
|constant Isrli \<rightharpoonup>(SML) "VAMP.Isrli (_, _, _)"
|constant Israi \<rightharpoonup>(SML) "VAMP.Israi (_, _, _)"
|constant Isll \<rightharpoonup>(SML) "VAMP.Isll (_, _, _)"
|constant Isrl \<rightharpoonup>(SML) "VAMP.Isrl (_, _, _)"
|constant Isra \<rightharpoonup>(SML) "VAMP.Isra (_, _, _)"
|constant Ibeqz \<rightharpoonup>(SML) "VAMP.Ibeqz (_, _)"
|constant Ibnez \<rightharpoonup>(SML) "VAMP.Ibnez (_, _)"
|constant Ijal \<rightharpoonup>(SML) "VAMP.Ijal (_)"
|constant Ijalr \<rightharpoonup>(SML) "VAMP.Ijalr (_)"
|constant Ij \<rightharpoonup>(SML) "VAMP.Ij (_)"
|constant Ijr \<rightharpoonup>(SML) "VAMP.Ijr (_)"
|constant Itrap \<rightharpoonup>(SML) "VAMP.Itrap (_)"
|constant Irfe \<rightharpoonup> (SML) "VAMP.Irfe"

section {*experiments*}

test_spec "(\<sigma>\<^sub>0 \<Turnstile> (s \<leftarrow> mbind (il::instr list) exec\<^sub>V\<^sub>A\<^sub>M\<^sub>P ;  return (PUT s)))"
 apply (gen_test_cases  "PUT" split: instr.split instr.split_asm)
txt{* "Tracing on" thows that "HEY" appears - the code above has thus really the effect 
to update the pre- normalization. Remaining Bugs must therefore be related to 
context-transfer-issues and tactic failures.*}
  
mk_test_suite "example1"
declare [[testgen_iterations=50]]


test_spec "(\<sigma>\<^sub>0 \<Turnstile> (s \<leftarrow> mbind (\<iota>s::instr list) exec\<^sub>V\<^sub>A\<^sub>M\<^sub>P; 
                  assert\<^sub>S\<^sub>E (\<lambda>\<sigma>. c2c' \<sigma> = PUT \<sigma>\<^sub>0 \<iota>s)))"
     apply (gen_test_cases "PUT")
     mk_test_suite "example2"




test_spec "\<sigma>\<^sub>0 \<Turnstile> ( s \<leftarrow> mbind [ a ] exec\<^sub>V\<^sub>A\<^sub>M\<^sub>P; assert\<^sub>S\<^sub>E (\<lambda>\<sigma>. c2c' \<sigma> = PUT \<sigma>\<^sub>0 [a]))"
(* apply(simp split: instr.split instr.split_asm) *)
 apply (gen_test_cases 0 1 "PUT")
mk_test_suite "example"
declare [[testgen_iterations=50]]
gen_test_data "example" 
thm example.test_thm
thm example.test_thm_inst

value "3 = 3"
value "(5 AND 4::32 word)"  (* the beauty of the NICTA Word library *)
value "(5 \<and>\<^sub>s 4)"  (* !!! *)

value "0 AND 1::bit"
end
