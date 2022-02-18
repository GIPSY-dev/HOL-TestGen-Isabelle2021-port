(**
 * Copyright (c) 2004-2006 Dirk Leinenbach, Alexandra Tsyban.
 * Some rights reserved, Saarland University.
 *
 * This work is licensed under the German-Jurisdiction Creative Commons
 * Attribution Non-commercial Share Alike 2.0 License.
 * See the file LIZENZ for a full copy of the license.
**)
(* $Id: Types.thy 22840 2008-03-26 17:32:49Z MarkHillebrand $ *)
chapter {* Types and Constants *}
theory Types imports arith_range begin

subsection {* Machine Types *}

type_synonym
              -- "for register"
              regname = nat                       -- "name of a register"
type_synonym  regcont = int                       -- "contents of register"
type_synonym  registers = "regcont list"          -- "register set (size not relevant here)"
  -- "for instruction definition"
type_synonym  immed = int                         -- "immediate (constant) value"
type_synonym  shift_amount = nat                  -- "shift amount, used in R-instructions"

subsection {* Memory *}

text {* Memory is organized as a mapping from the address 
        (divided by four) to some memory cell which can be 
        interpreted as integer (in case of data) or as 
        instruction (in case of code)
     *}

type_synonym mem_cell_t = "int"
type_synonym mem_t = "nat \<Rightarrow> mem_cell_t"

consts
  -- "size of memory"
  mem_size :: nat

subsection {* limiting some types *}

definition asm_imm16 :: "int \<Rightarrow> bool"
where
  "asm_imm16 n == -(2^15) \<le> n \<and> n < 2^15"

definition asm_imm26 :: "int \<Rightarrow> bool"
where
  "asm_imm26 n == -(2^25) \<le> n \<and> n < 2^25"

definition asm_sa :: "nat \<Rightarrow> bool"
where
  "asm_sa n == n < wlen_bit"

subsubsection {* some lemmas *}

lemma asm_imm16_impl_asm_int: "asm_imm16 i \<Longrightarrow> asm_int i"
by (clarsimp simp add: asm_int_def asm_imm16_def wlen_bit_def)

lemma asm_imm16_0: "asm_imm16 0"
apply (simp add: asm_imm16_def)
done

lemma asm_imm26_impl_asm_int: "asm_imm26 x \<Longrightarrow> asm_int x"
apply (simp add: asm_imm26_def asm_int_def)
apply (simp add: wlen_bit_def)
done

lemma asm_imm26_asm_nat: "asm_imm26 (int x) \<Longrightarrow> asm_nat x"
apply (simp add: asm_imm26_def asm_nat_def)
apply (simp add: wlen_bit_def)
done

lemma asm_imm26_asm_nat_plus_four: "asm_imm26 (int x) \<Longrightarrow> asm_nat (x + 4)"
apply (simp add: asm_imm26_def asm_nat_def)
apply (simp add: wlen_bit_def)
done

end
