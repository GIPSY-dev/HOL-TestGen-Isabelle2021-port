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

theory Setup_test
imports 
  "../VAMP-Machine-Model/Exec"
  "../VAMP-Machine-Model/Exec_properties" 
  "../VAMP-Machine-Model/VAMPasm_codegen_executable"
  "../../../src/Testing" 
          (*"~~/src/HOL/Library/Efficient_Nat"*)
begin

section{*backend configuration *}
declare [[testgen_iterations=0]]
declare [[testgen_iterations=0]] (* switch off random-solver *)
declare [[testgen_SMT]]          (* switch on Z3 *)


section{* Executable notions of configurations. *}

text{* An initial configuration of the VAMP machine can be defined
as follows: *}

definition \<sigma>\<^sub>0::"ASMcore_t" 
where "\<sigma>\<^sub>0 = (\<lparr>dpc =(0::nat),pcp = 1,
              gprs = (replicate 32 1), sprs = (replicate 32 0),
              mm = (\<lambda>_. 0) \<rparr>)" 

text{* Unfortunately, the modelization of configurations involves elements
that make them not computable in some sense - for example, since the linear 
memory  @{term mm} is modeled as function, the question if two states are
equal is not computable. Thus: *}

(*value "\<sigma>\<^sub>0 = \<sigma>\<^sub>0"  does not work for this reason ... *)

text{* Only comparisons to  *}

value "gprs \<sigma>\<^sub>0 = sprs \<sigma>\<^sub>0" 

text{* ... becomes an erroneous statement. In order to overcome this problem,
we define a finitized configuration and a conversion function:*}


(* is_ASMcore *)
record ASMcore_t' =
  dpc'   :: nat         (* delayed pc *)
  pcp'   :: nat         (* program counter *)
  gprs'  :: registers   (* general purpose registers  (32) *)
  sprs'  :: registers   (* special purpose registers  (32) *)
  mm'   :: "mem_cell_t list"

definition c2c' :: "ASMcore_t \<Rightarrow> ASMcore_t'"
where "c2c' \<sigma> = \<lparr>dpc' = dpc \<sigma>, pcp' = pcp \<sigma>, gprs' = gprs \<sigma>, 
                 sprs' = sprs \<sigma>,mm' = map (\<lambda>x. mm \<sigma> (nat x)) [0 .. 100] \<rparr> "


definition exec\<^sub>V\<^sub>A\<^sub>M\<^sub>P  
where     "exec\<^sub>V\<^sub>A\<^sub>M\<^sub>P \<equiv> (\<lambda> i st. Some ((), exec_instr st i))"

definition eq\<^sub>V\<^sub>A\<^sub>M\<^sub>P :: "ASMcore_t \<Rightarrow> ASMcore_t \<Rightarrow> bool"  (infixl ".=." 60 )
where     "eq\<^sub>V\<^sub>A\<^sub>M\<^sub>P \<equiv> (\<lambda> s s'. c2c' s = c2c' s')"

value " \<sigma>\<^sub>0 .=. \<sigma>\<^sub>0" (* That's why we need this conversion .... *)


lemma two_power_wlen_bit [code_unfold, simp]: "((2::nat) ^ wlen_bit) = 4294967296"
by (auto simp: wlen_bit_def)

lemma two_power_wlen_bit' [code_unfold, simp]: "((2::int) ^ wlen_bit) = 4294967296"
by (auto simp: wlen_bit_def)

lemma two_power_wlen_bit1' [code_unfold, simp]: "((2::int) ^ (wlen_bit - 1)) = 2147483648"
by (auto simp: wlen_bit_def)

lemma two_power_wlen_bit1 [code_unfold, simp]: "((2::nat) ^ (wlen_bit - 1)) = 2147483648"
by (auto simp: wlen_bit_def)

 
lemma "is_ASMcore \<sigma>\<^sub>0"
apply (auto simp: is_ASMcore_def \<sigma>\<^sub>0_def asm_nat_def asm_int_def)
apply (auto simp: wlen_bit_def data_mem_read_def cell2data_def sreg_def)
apply (case_tac ind, auto)
apply (rename_tac n, case_tac n, auto)+
done

text{* With these prereequisites, we can now execute the elementary
step function of the VAMP processor: *}


text {* ... and even generate executable stand-alone code: *}


definition  "execInstrs = foldl exec_instr"

text{* In particular, the executable version of the VAMP model 
can be used in test oracles for generated text cases. *}

 
abbreviation "is_register r \<equiv> r > 0 \<and> r < 32" (* why not r=0 ??? bu *)
abbreviation "is_immediate r \<equiv> r >= 0 \<and> r < 65536"

abbreviation is_load_store_word' :: "instr \<Rightarrow> bool"
where "is_load_store_word' iw \<equiv> (\<exists> rd rs imm. (is_register rd \<and> is_register rs \<and> is_immediate imm) \<and> 
                                                iw \<in> {Ilw rd rs imm, Isw rd rs imm})"

abbreviation is_load_store_hword' :: "instr \<Rightarrow> bool"
where "is_load_store_hword' iw \<equiv> (\<exists> rd rs imm. (is_register rd \<and> is_register rs \<and> is_immediate imm) \<and> 
                                                iw \<in> {Ilh rd rs imm, Ilhu rd rs imm, Ish rd rs imm})"

abbreviation  is_load_store_byte' :: "instr \<Rightarrow> bool"
where "is_load_store_byte' iw \<equiv> (\<exists> rd rs imm. (is_register rd \<and> is_register rs \<and> is_immediate imm) \<and> 
                                                iw \<in> {Ilb rd rs imm, Ilbu rd rs imm, Isb rd rs imm})"

definition is_load_store' :: "instr \<Rightarrow> bool"
where "is_load_store' iw \<equiv> is_load_store_word' iw \<or> is_load_store_hword' iw \<or> is_load_store_byte' iw"


consts VAMP_MACHINE :: "ASMcore_t \<Rightarrow> instr list \<Rightarrow> ASMcore_t"

end
