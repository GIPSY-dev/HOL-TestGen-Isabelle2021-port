(**
 * Copyright (c) 2006-2008 Mareike Schmidt, Alexandra Tsyban.
 * Some rights reserved, Saarland University.
 *
 * This work is licensed under the German-Jurisdiction Creative Commons
 * Attribution Non-commercial Share Alike 2.0 License.
 * See the file LIZENZ for a full copy of the license.
**)
(* $Id: Instr_convert.thy 24702 2008-08-06 13:15:07Z DirkLeinenbach $ *)
chapter {* Instruction conversion to the integer and back *}

theory Instr_convert
imports
  Instr
  Number
begin

definition imm16_to_nat :: "int \<Rightarrow> nat"
where
  "imm16_to_nat i \<equiv> nat (i + 2^16) mod 2^16"

definition imm26_to_nat :: "int \<Rightarrow> nat"
where
  "imm26_to_nat i \<equiv> nat (i + 2^26) mod 2^26"

primrec instr_to_nat :: "instr \<Rightarrow> nat"
where
  "instr_to_nat (Ilb RD rs imm)  = 32 * 2^26 + rs * 2^21 + RD * 2^16 + imm16_to_nat imm"
 | "instr_to_nat (Ilh RD rs imm)  = 33 * 2^26 + rs * 2^21 + RD * 2^16 + imm16_to_nat imm"
 | "instr_to_nat (Ilw RD rs imm)  = 35 * 2^26 + rs * 2^21 + RD * 2^16 + imm16_to_nat imm"
 | "instr_to_nat (Ilbu RD rs imm) = 36 * 2^26 + rs * 2^21 + RD * 2^16 + imm16_to_nat imm"
  |"instr_to_nat (Ilhu RD rs imm) = 37 * 2^26 + rs * 2^21 + RD * 2^16 + imm16_to_nat imm"
  |"instr_to_nat (Isb RD rs imm)  = 40 * 2^26 + rs * 2^21 + RD * 2^16 + imm16_to_nat imm"
 | "instr_to_nat (Ish RD rs imm)  = 41 * 2^26 + rs * 2^21 + RD * 2^16 + imm16_to_nat imm"
 | "instr_to_nat (Isw RD rs imm)  = 43 * 2^26 + rs * 2^21 + RD * 2^16 + imm16_to_nat imm"

 | "instr_to_nat (Iaddio RD rs imm) = 8  * 2^26 + rs * 2^21 + RD * 2^16 + imm16_to_nat imm"
 | "instr_to_nat (Iaddi RD rs imm)  = 9  * 2^26 + rs * 2^21 + RD * 2^16 + imm16_to_nat imm"
 | "instr_to_nat (Isubio RD rs imm) = 10 * 2^26 + rs * 2^21 + RD * 2^16 + imm16_to_nat imm"
 | "instr_to_nat (Isubi RD rs imm)  = 11 * 2^26 + rs * 2^21 + RD * 2^16 + imm16_to_nat imm"
 | "instr_to_nat (Iandi RD rs imm)  = 12 * 2^26 + rs * 2^21 + RD * 2^16 + imm16_to_nat imm"
 | "instr_to_nat (Iori RD rs imm)   = 13 * 2^26 + rs * 2^21 + RD * 2^16 + imm16_to_nat imm"
 | "instr_to_nat (Ixori RD rs imm)  = 14 * 2^26 + rs * 2^21 + RD * 2^16 + imm16_to_nat imm"
 | "instr_to_nat (Ilhgi RD imm)     = 15 * 2^26 +             RD * 2^16 + imm16_to_nat imm"

 | "instr_to_nat (Iclri RD)        = 24 * 2^26 +             RD * 2^16"
 | "instr_to_nat (Isgri RD rs imm) = 25 * 2^26 + rs * 2^21 + RD * 2^16 + imm16_to_nat imm"
 | "instr_to_nat (Iseqi RD rs imm) = 26 * 2^26 + rs * 2^21 + RD * 2^16 + imm16_to_nat imm"
 | "instr_to_nat (Isgei RD rs imm) = 27 * 2^26 + rs * 2^21 + RD * 2^16 + imm16_to_nat imm"
 | "instr_to_nat (Islsi RD rs imm) = 28 * 2^26 + rs * 2^21 + RD * 2^16 + imm16_to_nat imm"
 | "instr_to_nat (Isnei RD rs imm) = 29 * 2^26 + rs * 2^21 + RD * 2^16 + imm16_to_nat imm"
|  "instr_to_nat (Islei RD rs imm) = 30 * 2^26 + rs * 2^21 + RD * 2^16 + imm16_to_nat imm"
 | "instr_to_nat (Iseti RD)        = 31 * 2^26 +             RD * 2^16"

  |"instr_to_nat (Iaddo RD RS1 RS2) = RS1 * 2^21 + RS2 * 2^16 + RD * 2^11 + 32"
 | "instr_to_nat (Iadd RD RS1 RS2)  = RS1 * 2^21 + RS2 * 2^16 + RD * 2^11 + 33"
 | "instr_to_nat (Isubo RD RS1 RS2) = RS1 * 2^21 + RS2 * 2^16 + RD * 2^11 + 34"
 | "instr_to_nat (Isub RD RS1 RS2)  = RS1 * 2^21 + RS2 * 2^16 + RD * 2^11 + 35"
 | "instr_to_nat (Iand RD RS1 RS2)  = RS1 * 2^21 + RS2 * 2^16 + RD * 2^11 + 36"
|  "instr_to_nat (Ior RD RS1 RS2)   = RS1 * 2^21 + RS2 * 2^16 + RD * 2^11 + 37"
 | "instr_to_nat (Ixor RD RS1 RS2)  = RS1 * 2^21 + RS2 * 2^16 + RD * 2^11 + 38"
 | "instr_to_nat (Ilhg RD rs)       =              rs  * 2^16 + RD * 2^11 + 39"

 | "instr_to_nat (Iclr RD)         =                           RD * 2^11 + 40"
 | "instr_to_nat (Isgr RD RS1 RS2) = RS1 * 2^21 + RS2 * 2^16 + RD * 2^11 + 41"
 | "instr_to_nat (Iseq RD RS1 RS2) = RS1 * 2^21 + RS2 * 2^16 + RD * 2^11 + 42"
 | "instr_to_nat (Isge RD RS1 RS2) = RS1 * 2^21 + RS2 * 2^16 + RD * 2^11 + 43"
 | "instr_to_nat (Isls RD RS1 RS2) = RS1 * 2^21 + RS2 * 2^16 + RD * 2^11 + 44"
 | "instr_to_nat (Isne RD RS1 RS2) = RS1 * 2^21 + RS2 * 2^16 + RD * 2^11 + 45"
 | "instr_to_nat (Isle RD RS1 RS2) = RS1 * 2^21 + RS2 * 2^16 + RD * 2^11 + 46"
 | "instr_to_nat (Iset RD)         =                           RD * 2^11 + 47"

 | "instr_to_nat (Islli RD rs SA)  = rs  * 2^21 +              RD * 2^11 + SA * 2^6 + 0"
 | "instr_to_nat (Isrli RD rs SA)  = rs  * 2^21 +              RD * 2^11 + SA * 2^6 + 2"
 | "instr_to_nat (Israi RD rs SA)  = rs  * 2^21 +              RD * 2^11 + SA * 2^6 + 3"
 | "instr_to_nat (Isll RD RS1 RS2) = RS1 * 2^21 + RS2 * 2^16 + RD * 2^11 +            4"
 | "instr_to_nat (Isrl RD RS1 RS2) = RS1 * 2^21 + RS2 * 2^16 + RD * 2^11 +            6"
 | "instr_to_nat (Isra RD RS1 RS2) = RS1 * 2^21 + RS2 * 2^16 + RD * 2^11 +            7"

 | "instr_to_nat (Imovs2i RD SA) = RD * 2^11 + SA * 2^6 + 16"
 | "instr_to_nat (Imovi2s SA rs) = rs * 2^21 + SA * 2^6 + 17"

 | "instr_to_nat (Ibeqz rs imm) = 4  * 2^26 + rs * 2^21 + imm16_to_nat imm"
 | "instr_to_nat (Ibnez rs imm) = 5  * 2^26 + rs * 2^21 + imm16_to_nat imm"
|  "instr_to_nat (Ijr rs)       = 22 * 2^26 + rs * 2^21"
 | "instr_to_nat (Ijalr rs)     = 23 * 2^26 + rs * 2^21"

 | "instr_to_nat (Ij imm)   = 2 * 2^26 + imm26_to_nat imm"
 | "instr_to_nat (Ijal imm) = 3 * 2^26 + imm26_to_nat imm"

 | "instr_to_nat (Itrap imm) = 62 * 2^26 + imm26_to_nat imm"
 | "instr_to_nat (Irfe)      = 63 * 2^26"

definition instr_to_int :: "instr \<Rightarrow> int"
where
  "instr_to_int iw \<equiv> natwd_as_int (instr_to_nat iw)"

lemma asm_nat_reg_imm16:
  "\<lbrakk> r1 < 32; r2 < 32; a \<le> 4227858432 \<rbrakk> \<Longrightarrow> asm_nat (a + r1 * 2097152 + r2 * 65536 + imm16_to_nat imm)"
apply (simp add: asm_nat_def)
 apply (simp add: imm16_to_nat_def)
apply (simp add: wlen_bit_def)
done

lemma asm_nat_reg_reg:
  "\<lbrakk> ra < 32; rb < 32; rc < 32; a < 4227860480 \<rbrakk> \<Longrightarrow> asm_nat (ra * 2097152 + rb * 65536 + rc * 2048 + a)"
apply (simp add: asm_nat_def)
apply (simp add: wlen_bit_def)
done

lemma asm_nat_reg_sa:
  "\<lbrakk> ra < 32; rb < 32; rc < 32; a < 4229890112 \<rbrakk> \<Longrightarrow> asm_nat (ra * 2097152 + rb * 2048 + rc * 64 + a)"
apply (simp add: asm_nat_def)
apply (simp add: wlen_bit_def)
done

lemma asm_nat_jump_imm16:
  "\<lbrakk> r < 32; a \<le> 4229890048 \<rbrakk> \<Longrightarrow> asm_nat (a + r * 2097152 + imm16_to_nat imm)"
apply (simp add: asm_nat_def)
 apply (simp add: imm16_to_nat_def)
apply (simp add: wlen_bit_def)
done

lemma asm_nat_jump_imm26:
  "a \<le> 4227858432 \<Longrightarrow> asm_nat (a + imm26_to_nat imm)"
apply (simp add: asm_nat_def)
 apply (simp add: imm26_to_nat_def)
apply (simp add: wlen_bit_def)
done

lemma asm_nat_jump_reg:
  "\<lbrakk> r < 32; a < 4229955584 \<rbrakk> \<Longrightarrow> asm_nat (a + r * 2097152)"
apply (simp add: asm_nat_def)
apply (simp add: wlen_bit_def)
done

lemma is_instr_impl_asm_nat_instr_to_nat: 
      "is_instr iw \<Longrightarrow> asm_nat (instr_to_nat iw)"
apply (case_tac iw)
apply (simp_all add: is_instr_def)

apply (erule_tac [1-26] conjE)
apply (erule_tac [1-8] conjE)

apply (erule asm_nat_reg_imm16, assumption)
apply simp

apply (erule asm_nat_reg_imm16, assumption)
apply simp

apply (erule asm_nat_reg_imm16, assumption)
apply simp

apply (erule asm_nat_reg_imm16, assumption)
apply simp

apply (erule asm_nat_reg_imm16, assumption)
apply simp

apply (erule asm_nat_reg_imm16, assumption)
apply simp

apply (erule asm_nat_reg_imm16, assumption)
apply simp

apply (erule asm_nat_reg_imm16, assumption)
apply simp

apply (simp add: asm_nat_def)
apply (rule_tac y= "1006632960 + 31 * 65536 + imm16_to_nat  x92" in le_less_trans)
 apply simp
apply (rule_tac y = "1006632960 + 31 * 65536 + 2^16" in less_le_trans)
 apply (simp add: imm16_to_nat_def)
apply (simp add: wlen_bit_def)

apply (simp add: asm_nat_def)
apply (rule_tac y = "31 * 65536 + x101 * 2048 + 39" in le_less_trans)
 apply simp
apply (rule_tac y = "31 * 65536 + 31 * 2048 + 39" in le_less_trans)
 apply simp
apply (simp add: wlen_bit_def)

apply (simp add: asm_nat_def)
apply (rule_tac y = "31 * 2048 + x112 * 64 + 16" in le_less_trans)
 apply simp
apply (rule_tac y= "31 * 2048 + 31 * 64 + 16" in le_less_trans)
 apply simp
apply (simp add: wlen_bit_def)

apply (simp add: asm_nat_def)
apply (rule_tac y = "31 * 2097152 + x121 * 64 + 17" in le_less_trans)
 apply simp
apply (rule_tac y = "31 * 2097152 + 31 * 64 + 17" in le_less_trans)
 apply simp
apply (simp add: wlen_bit_def)

apply (erule_tac [1-14] conjE)

apply (erule asm_nat_reg_imm16, assumption)
apply simp

apply (erule asm_nat_reg_imm16, assumption)
apply simp

apply (erule asm_nat_reg_imm16, assumption)
apply simp

apply (erule asm_nat_reg_imm16, assumption)
apply simp

apply (erule asm_nat_reg_imm16, assumption)
apply simp

apply (erule asm_nat_reg_imm16, assumption)
apply simp

apply (erule asm_nat_reg_imm16, assumption)
apply simp

apply (erule asm_nat_reg_reg, assumption+)
apply simp

apply (erule asm_nat_reg_reg, assumption+)
apply simp

apply (erule asm_nat_reg_reg, assumption+)
apply simp

apply (erule asm_nat_reg_reg, assumption+)
apply simp

apply (erule asm_nat_reg_reg, assumption+)
apply simp

apply (erule asm_nat_reg_reg, assumption+)
apply simp

apply (erule asm_nat_reg_reg, assumption+)
apply simp

apply (simp add: asm_nat_def)
apply (simp add: wlen_bit_def)

apply (erule_tac [1-6] conjE)
apply (erule_tac [1-6] conjE)

apply (erule asm_nat_reg_imm16, assumption)
apply simp

apply (erule asm_nat_reg_imm16, assumption)
apply simp

apply (erule asm_nat_reg_imm16, assumption)
apply simp

apply (erule asm_nat_reg_imm16, assumption)
apply simp

apply (erule asm_nat_reg_imm16, assumption)
apply simp

apply (erule asm_nat_reg_imm16, assumption)
apply simp

apply (simp add: asm_nat_def)
apply (simp add: wlen_bit_def)

apply (simp add: asm_nat_def)
apply (rule_tac y = "31 * 2048 + 40" in le_less_trans)
 apply simp
apply (simp add: wlen_bit_def)

apply (erule_tac [1-6] conjE)
apply (erule_tac [1-6] conjE)
apply (simp add: asm_nat_reg_reg)
apply (erule asm_nat_reg_reg, assumption+)
apply simp

apply (erule asm_nat_reg_reg, assumption+)
apply simp

apply (erule asm_nat_reg_reg, assumption+)
apply simp

apply (erule asm_nat_reg_reg, assumption+)
apply simp

apply (erule asm_nat_reg_reg, assumption+)
apply simp+

apply (simp add: asm_nat_def)
apply (rule_tac y = "31 * 2048 + 47" in le_less_trans)
 apply simp
apply (simp add: wlen_bit_def)

apply (erule_tac [1-8] conjE)
apply (erule_tac [1-6] conjE)

apply (simp_all add: asm_sa_def)
apply (simp_all add: wlen_bit_def)

apply (drule_tac a = 0 and ra = x432 and rb = x431 and rc = x433 in asm_nat_reg_sa, assumption+)
 apply simp
apply simp

apply (drule_tac a = 2 and ra = x442 and rb = x441 and rc = x443 in asm_nat_reg_sa, assumption+)
 apply simp
apply simp

apply (erule asm_nat_reg_sa, assumption+)
apply simp

apply (erule asm_nat_reg_reg, assumption+)
apply simp

apply (erule asm_nat_reg_reg, assumption+)
apply simp

apply (erule asm_nat_reg_reg, assumption+)
apply simp

apply (erule asm_nat_jump_imm16)
apply simp

apply (erule asm_nat_jump_imm16)
apply simp

apply (rule asm_nat_jump_imm26)
apply simp

apply (erule asm_nat_jump_reg)
apply simp

apply (rule asm_nat_jump_imm26)
apply simp

apply (erule asm_nat_jump_reg)
apply simp

apply (rule asm_nat_jump_imm26)
apply simp

apply (simp add: asm_nat_def wlen_bit_def)
done

lemma is_instr_impl_asm_int_instr_to_int: "is_instr iw \<Longrightarrow> asm_int (instr_to_int iw)"
apply (simp only: instr_to_int_def)
apply (rule asm_int_natwd_as_int)
apply (erule is_instr_impl_asm_nat_instr_to_nat)
done

definition nat_to_instr_R_shift :: "[nat, nat, nat, nat, nat] \<Rightarrow> instr"
where
"nat_to_instr_R_shift r1 r2 r3 r4 opcode \<equiv>
     if opcode \<in> {0,1} then Islli r3 r1 r4 else
     if opcode = 2 then Isrli r3 r1 r4 else
     if opcode = 3 then Israi r3 r1 r4 else
     if opcode \<in> {4,5} then Isll r3 r1 r2 else
     if opcode = 6 then Isrl r3 r1 r2 else
     if opcode = 7 then Isra r3 r1 r2 else
     undefined"

definition nat_to_instr_R_mov :: "[nat, nat, nat, nat] \<Rightarrow> instr"
where
"nat_to_instr_R_mov r1 r3 r4 opcode \<equiv>
     if opcode = 16 then Imovs2i r3 r4 else
     if opcode = 17 then Imovi2s r4 r1 else
     undefined"

definition nat_to_instr_R_al :: "[nat, nat, nat, nat] \<Rightarrow> instr"
 where  "nat_to_instr_R_al r1 r2 r3 opcode \<equiv>
     if opcode = 32 then Iaddo r3 r1 r2 else
     if opcode = 33 then Iadd r3 r1 r2 else
     if opcode = 34 then Isubo r3 r1 r2 else
     if opcode = 35 then Isub r3 r1 r2 else
     if opcode = 36 then Iand r3 r1 r2 else
     if opcode = 37 then Ior r3 r1 r2 else
     if opcode = 38 then Ixor r3 r1 r2 else
     if opcode = 39 then Ilhg r3 r2 else
     undefined"

definition  nat_to_instr_R_comp :: "[nat, nat, nat, nat] \<Rightarrow> instr"
where
  "nat_to_instr_R_comp r1 r2 r3 opcode \<equiv>
     if opcode = 40 then Iclr r3 else
     if opcode = 41 then Isgr r3 r1 r2 else
     if opcode = 42 then Iseq r3 r1 r2 else
     if opcode = 43 then Isge r3 r1 r2 else
     if opcode = 44 then Isls r3 r1 r2 else
     if opcode = 45 then Isne r3 r1 r2 else
     if opcode = 46 then Isle r3 r1 r2 else
     if opcode = 47 then Iset r3 else
     undefined"

definition nat_to_instr_R :: "nat \<Rightarrow> instr"
where
  "nat_to_instr_R n \<equiv> 
     let r1 = n div 2^21;
         r2 = (n mod 2^21) div 2^16;
         r3 = (n mod 2^16) div 2^11;
         r4 = (n mod 2^11) div 2^6;
         opcode = n mod 2^6
     in if opcode \<le> 7 then nat_to_instr_R_shift r1 r2 r3 r4 opcode else
        if 16 \<le> opcode \<and> opcode \<le> 17 then nat_to_instr_R_mov r1 r3 r4 opcode else
        if 32 \<le> opcode \<and> opcode \<le> 39 then nat_to_instr_R_al r1 r2 r3 opcode else
        if 40 \<le> opcode \<and> opcode \<le> 47 then nat_to_instr_R_comp r1 r2 r3 opcode else
        undefined"

definition nat_to_imm16 :: "nat \<Rightarrow> int"
where
  "nat_to_imm16 n \<equiv> if 2^15 \<le> n then int n - 2^16 else int n"

definition nat_to_imm26 :: "nat \<Rightarrow> int"
where
  "nat_to_imm26 n \<equiv> if 2^25 \<le> n then int n - 2^26 else int n"

definition nat_to_instr_I_jump :: "[nat, int, int, nat] \<Rightarrow> instr"
where 
"nat_to_instr_I_jump r1 imm16 imm26 opcode \<equiv>
     if opcode = 2 then Ij imm26 else
     if opcode = 3 then Ijal imm26 else
     if opcode = 4 then Ibeqz r1 imm16 else
     if opcode = 5 then Ibnez r1 imm16 else
     if opcode = 22 then Ijr r1 else
     if opcode = 23 then Ijalr r1 else
     undefined"

definition  nat_to_instr_I_al :: "[nat, nat, int, nat] \<Rightarrow> instr"
 where  "nat_to_instr_I_al r1 r2 imm16 opcode \<equiv> 
     if opcode = 8 then Iaddio r2 r1 imm16 else
     if opcode = 9 then Iaddi r2 r1 imm16 else
     if opcode = 10 then Isubio r2 r1 imm16 else
     if opcode = 11 then Isubi r2 r1 imm16 else
     if opcode = 12 then Iandi r2 r1 imm16 else
     if opcode = 13 then Iori r2 r1 imm16 else
     if opcode = 14 then Ixori r2 r1 imm16 else
     if opcode = 15 then Ilhgi r2 imm16 else
     undefined"

definition nat_to_instr_I_comp :: "[nat, nat, int, nat] \<Rightarrow> instr"
where

"nat_to_instr_I_comp r1 r2 imm16 opcode \<equiv>
     if opcode = 24 then Iclri r2 else
     if opcode = 25 then Isgri r2 r1 imm16 else
     if opcode = 26 then Iseqi r2 r1 imm16 else
     if opcode = 27 then Isgei r2 r1 imm16 else
     if opcode = 28 then Islsi r2 r1 imm16 else
     if opcode = 29 then Isnei r2 r1 imm16 else
     if opcode = 30 then Islei r2 r1 imm16 else
     if opcode = 31 then Iseti r2 else
     undefined"

definition nat_to_instr_I_mem :: "[nat, nat, int, nat] \<Rightarrow> instr"
where 
"nat_to_instr_I_mem r1 r2 imm16 opcode \<equiv> 
     if opcode = 32 then Ilb r2 r1 imm16 else
     if opcode = 33 then Ilh r2 r1 imm16 else
     if opcode = 35 then Ilw r2 r1 imm16 else
     if opcode = 36 then Ilbu r2 r1 imm16 else
     if opcode = 37 then Ilhu r2 r1 imm16 else
     if opcode = 40 then Isb r2 r1 imm16 else
     if opcode = 41 then Ish r2 r1 imm16 else
     if opcode = 43 then Isw r2 r1 imm16 else
     undefined"

definition  nat_to_instr_I :: "nat \<Rightarrow> instr"
where
  "nat_to_instr_I n \<equiv>
     let opcode = n div 2^26;
         r1 = (n mod 2^26) div 2^21;
         r2 = (n mod 2^21) div 2^16;
         imm16 = nat_to_imm16 (n mod 2^16);
         imm26 = nat_to_imm26 (n mod 2^26)
     in if 2 \<le> opcode \<and> opcode \<le> 5 \<or> 22 \<le> opcode \<and> opcode \<le> 23 then nat_to_instr_I_jump r1 imm16 imm26 opcode else
        if 8 \<le> opcode \<and> opcode \<le> 15 then nat_to_instr_I_al r1 r2 imm16 opcode else
        if 24 \<le> opcode \<and> opcode \<le> 31 then nat_to_instr_I_comp r1 r2 imm16 opcode else
        if 32 \<le> opcode \<and> opcode \<le> 43 then nat_to_instr_I_mem r1 r2 imm16 opcode else
        if opcode = 62 then Itrap imm26 else
        if opcode = 63 then Irfe else
        undefined"

definition nat_to_instr :: "nat \<Rightarrow> instr"
where
"nat_to_instr n \<equiv> 
      if n div 2^26 = 0 
      then nat_to_instr_R n 
      else nat_to_instr_I n"

definition int_to_instr :: "int \<Rightarrow> instr"
where
"int_to_instr i \<equiv> nat_to_instr (intwd_as_nat i)"

lemma add_mod_div: "\<lbrakk> b * e + c < d; c < e \<rbrakk> \<Longrightarrow> (a * d + b * e + c) mod d div e = (b::nat)"
apply (subst mod_add_eq)
apply simp
done

lemma convert_reg_imm_opcode:
  "\<lbrakk> ra < 32; rb < 32; a = k * 67108864 \<rbrakk> \<Longrightarrow> (a + ra * 2097152 + rb * 65536 + imm16_to_nat imm) div 67108864 = k"
apply (cut_tac a = "0" and 
               b = "k" and 
               c = "ra * 2097152 + rb * 65536 + imm16_to_nat imm" and
               d = "Suc (a + ra * 2097152 + rb * 65536 + imm16_to_nat imm)" and
               e = "67108864" in add_mod_div)
  apply simp
 apply (simp add: imm16_to_nat_def)
apply (rotate_tac -1, erule subst)
apply (subst mod_less)
 apply simp
apply (rule_tac f = "\<lambda>i. i div 67108864" in arg_cong)
apply simp
done

lemma nat_to_instr_eq_nat_to_instr_I:
  "\<lbrakk> ra < 32; rb < 32; a = k * 67108864; k \<noteq> 0 \<rbrakk> 
  \<Longrightarrow> nat_to_instr (a + ra * 2097152 + rb * 65536 + imm16_to_nat imm) = nat_to_instr_I (a + ra * 2097152 + rb * 65536 + imm16_to_nat imm)"
apply (simp (no_asm) add: nat_to_instr_def)
apply (subst convert_reg_imm_opcode, assumption+)
apply simp
done

lemma convert_reg_imm_reg1:
  "\<lbrakk> ra < 32; rb < 32; a = k * 67108864 \<rbrakk> \<Longrightarrow> (a + ra * 2097152 + rb * 65536 + imm16_to_nat imm) mod 67108864 div 2097152 = ra"
apply (cut_tac a = "k" and 
               b = "ra" and 
               c = "rb * 65536 + imm16_to_nat imm" and
               d = "67108864" and
               e = "2097152" in add_mod_div)
  apply (rule_tac y = "31 * 2097152 + (rb * 65536 + imm16_to_nat imm)" in le_less_trans)
   apply simp
  apply (rule_tac y = "31 * 2097152 + (31 * 65536 + imm16_to_nat imm)" in le_less_trans)
   apply simp
  apply simp
  apply (simp add: imm16_to_nat_def)
 apply (rule_tac y = "31 * 65536 + imm16_to_nat imm" in le_less_trans)
  apply simp
 apply simp
 apply (simp add: imm16_to_nat_def)
apply (rotate_tac -1)
apply (simp add: add.assoc)
done

lemma convert_reg_imm_reg2:
  "\<lbrakk> rb < 32; a = k * 67108864 \<rbrakk> \<Longrightarrow> (a + ra * 2097152 + rb * 65536 + imm16_to_nat imm) mod 2097152 div 65536 = rb"
apply (cut_tac a = "32 * k + ra" and 
               b = "rb" and 
               c = "imm16_to_nat imm" and
               d = "2097152" and
               e = "65536" in add_mod_div)

  apply (simp add: imm16_to_nat_def)
 apply (simp add: imm16_to_nat_def)
apply (rotate_tac -1)
apply simp
apply (simp add: mult.commute)
done

lemma convert_reg_imm_imm16:
  "a = k * 67108864 \<Longrightarrow> (a + ra * 2097152 + rb * 65536 + imm16_to_nat imm) mod 65536 = imm16_to_nat imm"
apply (cut_tac a = "1024 * k + 32 * ra + rb" and 
               b = "imm16_to_nat imm" and 
               c = "0" and
               d = "65536" and
               e = "1" in add_mod_div)
  apply (simp add: imm16_to_nat_def)
 apply simp
apply (rotate_tac -1)
apply simp
apply (simp add: mult.commute)
done

lemma nat_to_imm16_imm16_to_nat:
  "asm_imm16 imm \<Longrightarrow> nat_to_imm16 (imm16_to_nat imm) = imm"
apply (simp add: imm16_to_nat_def)
apply (simp add: nat_to_imm16_def)
apply (simp add: asm_imm16_def)
apply (case_tac "0 \<le> imm")
 apply simp
 apply (frule_tac z' = "65536" in nat_add_distrib)
  apply simp
 apply (rotate_tac -1, erule ssubst)
 apply simp
 apply (cut_tac m = "nat imm" and n = "65536" in mod_less)
  apply arith
 apply (rotate_tac -1, erule ssubst)
 apply simp
done

lemma nat_to_instr_I_eq_nat_to_instr_I_mem:
  "\<lbrakk> ra < 32; rb < 32; asm_imm16 imm; a = k * 67108864; 32 \<le> k \<and> k \<le> 43 \<rbrakk> 
  \<Longrightarrow> nat_to_instr_I (a + ra * 2097152 + rb * 65536 + imm16_to_nat imm) = nat_to_instr_I_mem ra rb imm k"
apply (simp (no_asm) add: nat_to_instr_I_def split del: if_split del: Let_def)
apply (subst convert_reg_imm_opcode, assumption+)
apply (subst convert_reg_imm_reg1, assumption+)
apply (subst convert_reg_imm_reg2, assumption+)
apply (subst convert_reg_imm_imm16, assumption)
apply (subst nat_to_imm16_imm16_to_nat, assumption)
apply (simp only: Let_def)
apply (subgoal_tac "(2 \<le> k \<and> k \<le> 5 \<or> 22 \<le> k \<and> k \<le> 23) = False")
 prefer 2
 apply simp
apply (rotate_tac -1, erule ssubst)
apply (split if_split)
apply (rule conjI)
 apply (simp (no_asm))
apply (rule impI)
apply (split if_split)
apply (rule conjI)
 apply simp
apply (rule impI)
apply (split if_split)
apply (rule conjI)
 apply simp
apply (rule impI)
apply (split if_split)
apply (rule conjI)
 apply simp
apply (rule impI)
apply (rotate_tac -1)
apply (erule notE)
apply simp
done

lemma nat_to_instr_eq_nat_to_instr_I_mem:
  "\<lbrakk> ra < 32; rb < 32; asm_imm16 imm; a = k * 67108864; 32 \<le> k \<and> k \<le> 43 \<rbrakk> 
  \<Longrightarrow> nat_to_instr (a + ra * 2097152 + rb * 65536 + imm16_to_nat imm) = nat_to_instr_I_mem ra rb imm k"
apply (subst nat_to_instr_eq_nat_to_instr_I, assumption+)
 apply simp
apply (erule nat_to_instr_I_eq_nat_to_instr_I_mem, assumption+)
done

lemma nat_to_instr_I_eq_nat_to_instr_I_al:
  "\<lbrakk> ra < 32; rb < 32; asm_imm16 imm; a = k * 67108864; 8 \<le> k \<and> k \<le> 15 \<rbrakk> 
  \<Longrightarrow> nat_to_instr_I (a + ra * 2097152 + rb * 65536 + imm16_to_nat imm) = nat_to_instr_I_al ra rb imm k"
apply (simp (no_asm) add: nat_to_instr_I_def split del: if_split del: Let_def)
apply (subst convert_reg_imm_opcode, assumption+)
apply (subst convert_reg_imm_reg1, assumption+)
apply (subst convert_reg_imm_reg2, assumption+)
apply (subst convert_reg_imm_imm16, assumption)
apply (subst nat_to_imm16_imm16_to_nat, assumption)
apply (simp only: Let_def)
apply (subgoal_tac "(2 \<le> k \<and> k \<le> 5 \<or> 22 \<le> k \<and> k \<le> 23) = False")
 prefer 2
 apply simp
apply (rotate_tac -1, erule ssubst)
apply (split if_split)
apply (rule conjI)
 apply (simp (no_asm))
apply (rule impI)
apply (split if_split)
apply (rule conjI)
 apply simp
apply (rule impI)
apply (rotate_tac -1)
apply (erule notE)
apply simp
done

lemma nat_to_instr_eq_nat_to_instr_I_al:
  "\<lbrakk> ra < 32; rb < 32; asm_imm16 imm; a = k * 67108864; 8 \<le> k \<and> k \<le> 15 \<rbrakk> 
  \<Longrightarrow> nat_to_instr (a + ra * 2097152 + rb * 65536 + imm16_to_nat imm) = nat_to_instr_I_al ra rb imm k"
apply (subst nat_to_instr_eq_nat_to_instr_I, assumption+)
 apply simp
apply (erule nat_to_instr_I_eq_nat_to_instr_I_al, assumption+)
done

lemma nat_to_instr_eq_Ilhgi:
  "\<lbrakk> rb < 32; asm_imm16 imm \<rbrakk> 
  \<Longrightarrow> nat_to_instr (1006632960 + rb * 65536 + imm16_to_nat imm) = Ilhgi rb imm"
apply (subgoal_tac "1006632960 + rb * 65536 + imm16_to_nat imm = 1006632960 + 0 * 2097152 + rb * 65536 + imm16_to_nat imm")
 prefer 2
 apply simp
apply (rotate_tac -1, erule ssubst)
apply (subst nat_to_instr_eq_nat_to_instr_I_al)
     apply simp
    apply assumption+
  apply simp
 apply simp
apply (simp add: nat_to_instr_I_al_def)
done

lemma nat_to_instr_I_eq_nat_to_instr_I_comp:
  "\<lbrakk> ra < 32; rb < 32; asm_imm16 imm; a = k * 67108864; 24 \<le> k \<and> k \<le> 31 \<rbrakk> 
  \<Longrightarrow> nat_to_instr_I (a + ra * 2097152 + rb * 65536 + imm16_to_nat imm) = nat_to_instr_I_comp ra rb imm k"
apply (simp (no_asm) add: nat_to_instr_I_def split del: if_split del: Let_def)
apply (subst convert_reg_imm_opcode, assumption+)
apply (subst convert_reg_imm_reg1, assumption+)
apply (subst convert_reg_imm_reg2, assumption+)
apply (subst convert_reg_imm_imm16, assumption)
apply (subst nat_to_imm16_imm16_to_nat, assumption)
apply (simp only: Let_def)
apply (subgoal_tac "(2 \<le> k \<and> k \<le> 5 \<or> 22 \<le> k \<and> k \<le> 23) = False")
 prefer 2
 apply simp
apply (rotate_tac -1, erule ssubst)
apply (split if_split)
apply (rule conjI)
 apply (simp (no_asm))
apply (rule impI)
apply (split if_split)
apply (rule conjI)
 apply simp
apply (rule impI)
apply (split if_split)
apply (rule conjI)
 apply simp
apply (rule impI)
apply (rotate_tac -1)
apply (erule notE)
apply simp
done

lemma nat_to_instr_eq_nat_to_instr_I_comp:
  "\<lbrakk> ra < 32; rb < 32; asm_imm16 imm; a = k * 67108864; 24 \<le> k \<and> k \<le> 31 \<rbrakk> 
  \<Longrightarrow> nat_to_instr (a + ra * 2097152 + rb * 65536 + imm16_to_nat imm) = nat_to_instr_I_comp ra rb imm k"
apply (subst nat_to_instr_eq_nat_to_instr_I, assumption+)
 apply simp
apply (erule nat_to_instr_I_eq_nat_to_instr_I_comp, assumption+)
done

lemma imm16_to_nat_0: "imm16_to_nat 0 = 0"
apply (simp add: imm16_to_nat_def)
done

lemma nat_to_instr_eq_nat_to_instr_I_comp_clr_or_set:
  "\<lbrakk> rb < 32; a = k * 67108864; 24 \<le> k \<and> k \<le> 31 \<rbrakk> 
  \<Longrightarrow> nat_to_instr (a + rb * 65536) = nat_to_instr_I_comp 0 rb 0 k"
apply (subgoal_tac "a + rb * 65536 = a + 0 * 2097152 + rb * 65536 + imm16_to_nat 0")
 prefer 2
 apply (simp add: imm16_to_nat_0)
apply (rotate_tac -1, erule ssubst)
apply (rule nat_to_instr_eq_nat_to_instr_I_comp)
    apply simp
   apply assumption
  apply (rule asm_imm16_0)
 apply assumption+
done

lemma nat_to_instr_eq_nat_to_instr_I_branch:
  "\<lbrakk> r < 32; asm_imm16 imm; a = k * 67108864; k = 4 \<or> k = 5 \<rbrakk> 
  \<Longrightarrow> nat_to_instr (a + r * 2097152 + imm16_to_nat imm) = (if k = 4 then Ibeqz r imm else if k = 5 then Ibnez r imm else undefined)"
apply (simp add: nat_to_instr_def split del: if_split)
apply (frule_tac rb = 0 and imm = imm in convert_reg_imm_opcode)
  apply simp
 apply assumption
apply (simp split del: if_split)
apply (rotate_tac -1, erule ssubst)
apply (rule sym)
apply (split if_split)
apply (intro conjI impI)
 apply simp
apply (simp (no_asm) add: nat_to_instr_I_def split del: if_split del: Let_def)
apply (subgoal_tac "k * 67108864 + r * 2097152 + imm16_to_nat imm = a + r * 2097152 + 0 * 65536 + imm16_to_nat imm")
 prefer 2
 apply simp
apply (rotate_tac -1, erule ssubst)
apply (subst convert_reg_imm_opcode, assumption)
  apply simp
 apply assumption
apply (subst convert_reg_imm_reg1, assumption)
  apply simp
 apply assumption
apply (subst convert_reg_imm_reg2)
  apply simp
 apply assumption
apply (subst convert_reg_imm_imm16, assumption)
apply (subst nat_to_imm16_imm16_to_nat, assumption)
apply (simp only: Let_def)
apply (subgoal_tac "(2 \<le> k \<and> k \<le> 5 \<or> 22 \<le> k \<and> k \<le> 23) = True")
 prefer 2
 apply fastforce
apply (rotate_tac -1, erule ssubst)
apply (split if_split)
apply (intro conjI impI)
 apply (erule disjE)
  apply (simp add: nat_to_instr_I_jump_def)
 apply (simp add: nat_to_instr_I_jump_def)
apply (rotate_tac -1)
apply (erule notE)
apply simp
done

lemma nat_to_instr_eq_nat_to_instr_I_jump_reg:
  "\<lbrakk> r < 32; a = k * 67108864; k = 22 \<or> k = 23 \<rbrakk> 
  \<Longrightarrow> nat_to_instr (a + r * 2097152) = (if k = 22 then Ijr r else if k = 23 then Ijalr r else undefined)"
apply (simp add: nat_to_instr_def split del: if_split)
apply (frule_tac rb = 0 and imm = 0 in convert_reg_imm_opcode)
  apply simp
 apply assumption
apply (simp add: imm16_to_nat_0 split del: if_split)
apply (rotate_tac -1, erule ssubst)
apply (rule sym)
apply (split if_split)
apply (intro conjI impI)
 apply simp
apply (simp (no_asm) add: nat_to_instr_I_def split del: if_split del: Let_def)
apply (subgoal_tac "k * 67108864 + r * 2097152 = a + r * 2097152 + 0 * 65536 + imm16_to_nat 0")
 prefer 2
 apply (simp add: imm16_to_nat_0)
(* ================== rev. 12634 ======================
apply (rotate_tac -1, erule ssubst)
apply (subst convert_reg_imm_opcode, assumption)
  apply simp
 apply assumption
apply (subst convert_reg_imm_reg1, assumption)
  apply simp
 apply assumption
apply (subgoal_tac "k * 67108864 mod 2097152 div 65536 = 0")
 prefer 2
 apply (subst mod_mult1_eq)
 apply simp
apply (rotate_tac -1, erule ssubst)
apply (subst convert_reg_imm_imm16, assumption)
apply (simp only: Let_def)
apply (subgoal_tac "(2 \<le> k \<and> k \<le> 5 \<or> 22 \<le> k \<and> k \<le> 23) = True")
 prefer 2
 apply fastsimp
apply (rotate_tac -1, erule ssubst)
apply (split if_split)
apply (intro conjI impI)
 apply (erule disjE)
  apply (simp add: nat_to_instr_I_jump_def)
 apply (simp add: nat_to_instr_I_jump_def)
apply (rotate_tac -1)
apply (erule notE)
apply simp
   ================== rev. 12634 ====================== *)

sorry

lemma convert_reg_imm_opcode_26:
  "a = k * 67108864 \<Longrightarrow> (a + imm26_to_nat imm) div 67108864 = k"
apply (cut_tac a = "0" and 
               b = "k" and 
               c = "imm26_to_nat imm" and
               d = "Suc (k * 67108864 + imm26_to_nat imm)" and
               e = "67108864" in add_mod_div)
  apply simp
 apply (simp add: imm26_to_nat_def)
apply (rotate_tac -1)
 apply simp
done

lemma convert_reg_imm_imm26:
  "a = k * 67108864 \<Longrightarrow> (a + imm26_to_nat imm) mod 67108864 = imm26_to_nat imm"
apply (cut_tac a = "k" and 
               b = "imm26_to_nat imm" and 
               c = "0" and
               d = "67108864" and
               e = "1" in add_mod_div)
  apply (simp add: imm26_to_nat_def)
 apply simp
apply (rotate_tac -1)
apply simp
done

lemma nat_to_imm26_imm26_to_nat:
  "asm_imm26 imm \<Longrightarrow> nat_to_imm26 (imm26_to_nat imm) = imm"
apply (simp add: imm26_to_nat_def)
apply (simp add: nat_to_imm26_def)
apply (simp add: asm_imm26_def)
apply (case_tac "0 \<le> imm")
 apply simp
 apply (frule_tac z' = "67108864" in nat_add_distrib)
  apply simp
 apply (rotate_tac -1, erule ssubst)
 apply simp
 apply (cut_tac m = "nat imm" and n = "67108864" in mod_less)
  apply arith
 apply (rotate_tac -1, erule ssubst)
 apply simp
done

lemma nat_to_instr_eq_nat_to_instr_I_jump_imm:
  "\<lbrakk>asm_imm26 imm; a = k * 67108864; k = 2 \<or> k = 3 \<rbrakk> \<Longrightarrow> 
    nat_to_instr (a + imm26_to_nat imm) = 
    (if k = 2 then Ij imm else if k = 3 then Ijal imm else undefined)"
apply (simp add: nat_to_instr_def split del: if_split)
(* ================== rev. 12634 ======================

apply (subst convert_reg_imm_opcode_26)
 apply (rule refl)
apply (rule sym)
apply (split if_split)
apply (intro conjI impI)
 apply simp
apply (simp (no_asm) add: nat_to_instr_I_def split del: if_split del: Let_def)
apply (subst convert_reg_imm_opcode_26)
 apply (rule refl)
apply (subst convert_reg_imm_imm26)
 apply (rule refl)
apply (subst convert_reg_imm_imm26)
 apply (rule refl)
apply (subst nat_to_imm26_imm26_to_nat, assumption)
apply (simp only: Let_def)
apply (subgoal_tac "(2 \<le> k \<and> k \<le> 5 \<or> 22 \<le> k \<and> k \<le> 23) = True")
 prefer 2
 apply fastsimp
apply (rotate_tac -1, erule ssubst)
apply (split if_split)
apply (intro conjI impI)
 apply (erule disjE)
  apply (simp add: nat_to_instr_I_jump_def)
 apply (simp add: nat_to_instr_I_jump_def)
apply (rotate_tac -1)
apply (erule notE)
apply simp
   ================== rev. 12634 ====================== *)
sorry

lemma nat_to_instr_eq_Itrap:
  "\<lbrakk> asm_imm26 imm \<rbrakk> \<Longrightarrow> nat_to_instr (4160749568 + imm26_to_nat imm) = Itrap imm"
apply (simp add: nat_to_instr_def split del: if_split)
apply (subst convert_reg_imm_opcode_26)
 apply simp
apply simp
apply (simp (no_asm) add: nat_to_instr_I_def split del: if_split del: Let_def)
apply (subst convert_reg_imm_opcode_26)
 apply simp
apply (subst convert_reg_imm_imm26)
 apply simp
apply (subst convert_reg_imm_imm26)
 apply simp
apply (subst nat_to_imm26_imm26_to_nat, assumption)
apply simp
done

lemma nat_to_instr_eq_Irfe:
  "nat_to_instr 4227858432 = Irfe"
apply (simp add: nat_to_instr_def split del: if_split)
apply (simp add: nat_to_instr_I_def)
done

lemma convert_reg_reg_opcode1_help:
  "\<lbrakk> ra < 32; rb < 32; rc < 32; rd < 32; k < 64 \<rbrakk> \<Longrightarrow> (ra * 2097152 + rb * 65536 + rc * 2048 + rd * 64 + (k::nat)) div 67108864 = 0"
apply (rule div_less)
 apply simp
done

lemma convert_reg_reg_opcode1:
  "\<lbrakk> ra < 32; rb < 32; rc < 32; k < 64 \<rbrakk> \<Longrightarrow> (ra * 2097152 + rb * 65536 + rc * 2048 + (k::nat)) div 67108864 = 0"
apply (drule_tac rc = rc and rd = 0 in convert_reg_reg_opcode1_help, assumption+)
  apply simp
apply assumption
apply simp
done

lemma convert_reg_reg_opcode1_SA:
  "\<lbrakk> ra < 32; rc < 32; asm_sa rd; k < 64 \<rbrakk> \<Longrightarrow> (ra * 2097152 + rc * 2048 + rd * 64 + (k::nat)) div 67108864 = 0"
apply (drule_tac rb = 0 and rd = rd in convert_reg_reg_opcode1_help)
    apply simp
   apply assumption
  apply (simp add: asm_sa_def)
  apply (simp add: wlen_bit_def)
 apply assumption
apply simp
done

lemma nat_to_instr_eq_nat_to_instr_R:
  "\<lbrakk> ra < 32; rb < 32; rc < 32; k < 64 \<rbrakk> 
  \<Longrightarrow> nat_to_instr (ra * 2097152 + rb * 65536 + rc * 2048 + k) = nat_to_instr_R (ra * 2097152 + rb * 65536 + rc * 2048 + k)"
apply (simp (no_asm) add: nat_to_instr_def)
apply (subst convert_reg_reg_opcode1, assumption+)
apply simp
done

lemma nat_to_instr_eq_nat_to_instr_R_SA:
  "\<lbrakk> ra < 32; rc < 32; asm_sa rd; k < 64 \<rbrakk> 
  \<Longrightarrow> nat_to_instr (ra * 2097152 + rc * 2048 + rd * 64 + k) = nat_to_instr_R (ra * 2097152 + rc * 2048 + rd * 64 + k)"
apply (simp (no_asm) add: nat_to_instr_def)
apply (subst convert_reg_reg_opcode1_SA, assumption+)
apply simp
done

lemma convert_reg_reg_reg1_help:
  "\<lbrakk> rb < 32; rc < 32; rd < 32; k < 64 \<rbrakk> \<Longrightarrow> (ra * 2097152 + rb * 65536 + rc * 2048 + rd * 64 + (k::nat)) div 2097152 = ra"
apply (cut_tac a = "0" and 
               b = "ra" and 
               c = "rb * 65536 + rc * 2048 + rd * 64 + k" and
               d = "Suc (ra * 2097152 + rb * 65536 + rc * 2048 + rd * 64 + k)" and
               e = "2097152" in add_mod_div)
  apply simp+
done

lemma convert_reg_reg_reg1:
  "\<lbrakk> rb < 32; rc < 32; k < 64 \<rbrakk> \<Longrightarrow> (ra * 2097152 + rb * 65536 + rc * 2048 + (k::nat)) div 2097152 = ra"
apply (drule_tac ra = ra and rd = 0 in convert_reg_reg_reg1_help, assumption)
  apply simp
 apply assumption
apply simp
done

lemma convert_reg_reg_reg1_SA:
  "\<lbrakk> rc < 32; asm_sa rd; k < 64 \<rbrakk> \<Longrightarrow> (ra * 2097152 + rc * 2048 + rd * 64 + (k::nat)) div 2097152 = ra"
apply (cut_tac ra = ra and rb = 0 and rd = rd in convert_reg_reg_reg1_help)
    apply simp
   apply assumption
  apply (simp add: asm_sa_def)
  apply (simp add: wlen_bit_def)
 apply assumption
apply simp
done

lemma convert_reg_reg_reg2_help:
  "\<lbrakk> rb < 32; rc < 32; rd < 32; k < 64 \<rbrakk> \<Longrightarrow> (ra * 2097152 + rb * 65536 + rc * 2048 + rd * 64 + (k::nat)) mod 2097152 div 65536 = rb"
apply (cut_tac a = "ra" and 
               b = "rb" and 
               c = "rc * 2048 + rd * 64 + k" and
               d = "2097152" and
               e = "65536" in add_mod_div)
  apply (rule_tac y = "31 * 65536 + (rc * 2048 + rd * 64 + k)" in le_less_trans)
   apply simp
  apply (rule_tac y = "31 * 65536 + (31 * 2048 + rd * 64 + k)" in le_less_trans)
   apply simp
  apply (rule_tac y = "31 * 65536 + (31 * 2048 + 31 * 64 + k)" in le_less_trans)
   apply simp
  apply simp
 apply (rule_tac y = "31 * 2048 + rd * 64 + k" in le_less_trans)
  apply simp
 apply (rule_tac y = "31 * 2048 + 31 * 64 + k" in le_less_trans)
  apply simp
 apply simp
apply (simp add: add.assoc)
done

lemma convert_reg_reg_reg2:
  "\<lbrakk> rb < 32; rc < 32; k < 64 \<rbrakk> \<Longrightarrow> (ra * 2097152 + rb * 65536 + rc * 2048 + (k::nat)) mod 2097152 div 65536 = rb"
apply (drule_tac rd = 0 in convert_reg_reg_reg2_help, assumption)
  apply simp
 apply assumption
apply simp
done

lemma convert_reg_reg_reg2_SA:
  "\<lbrakk> rc < 32; asm_sa rd; k < 64 \<rbrakk> \<Longrightarrow> (ra * 2097152 + rc * 2048 + rd * 64 + (k::nat)) mod 2097152 div 65536 = 0"
apply (cut_tac rb = 0 and rd = rd in convert_reg_reg_reg2_help)
    apply simp
   apply assumption
  apply (simp add: asm_sa_def wlen_bit_def)
 apply assumption
apply simp
done

lemma convert_reg_reg_reg3_help:
  "\<lbrakk> rc < 32; rd < 32; k < 64 \<rbrakk> \<Longrightarrow> (ra * 2097152 + rb * 65536 + rc * 2048 + rd * 64 + (k::nat)) mod 65536 div 2048 = rc"
apply (cut_tac a = "32 * ra + rb" and 
               b = "rc" and 
               c = "rd * 64 + k" and
               d = "65536" and
               e = "2048" in add_mod_div)  
apply (simp_all add: add.assoc mult.commute)
done

lemma convert_reg_reg_reg3:
  "\<lbrakk> rc < 32; k < 64 \<rbrakk> \<Longrightarrow> (ra * 2097152 + rb * 65536 + rc * 2048 + (k::nat)) mod 65536 div 2048 = rc"
apply (drule_tac rd = 0 in convert_reg_reg_reg3_help)
  apply simp
 apply assumption
apply simp
done

lemma convert_reg_reg_reg3_SA:
  "\<lbrakk> rc < 32; asm_sa rd; k < 64 \<rbrakk> \<Longrightarrow> (ra * 2097152 + rc * 2048 + rd * 64 + (k::nat)) mod 65536 div 2048 = rc"
apply (drule_tac rb = 0 and rd = rd in convert_reg_reg_reg3_help)
  apply (simp add: asm_sa_def wlen_bit_def)
 apply assumption
apply simp
done

lemma convert_reg_reg_reg4_help:
  "\<lbrakk> rd < 32; k < 64 \<rbrakk> \<Longrightarrow> (ra * 2097152 + rb * 65536 + rc * 2048 + rd * 64 + (k::nat)) mod 2048 div 64 = rd"
apply (cut_tac a = "32 * 32 * ra + 32 * rb + rc" and 
               b = "rd" and 
               c = "k" and
               d = "2048" and
               e = "64" in add_mod_div)
   apply simp+
apply (simp add: mult.commute)
done

lemma convert_reg_reg_reg4:
  "\<lbrakk> k < 64 \<rbrakk> \<Longrightarrow> (ra * 2097152 + rb * 65536 + rc * 2048 + (k::nat)) mod 2048 div 64 = 0"
apply (cut_tac rd = 0 in convert_reg_reg_reg4_help)
  apply simp
 apply assumption
apply simp
done

lemma convert_reg_reg_reg4_SA:
  "\<lbrakk> asm_sa rd; k < 64 \<rbrakk> \<Longrightarrow> (ra * 2097152 + rc * 2048 + rd * 64 + (k::nat)) mod 2048 div 64 = rd"
apply (cut_tac rb = 0 and rd = rd in convert_reg_reg_reg4_help)
  apply (simp add: asm_sa_def wlen_bit_def)
 apply assumption
apply simp
done

lemma convert_reg_reg_opcode2_help:
  "\<lbrakk> k < 64 \<rbrakk> \<Longrightarrow> (ra * 2097152 + rb * 65536 + rc * 2048 + rd * 64 + (k::nat)) mod 64 = k"
apply (cut_tac a = "32 * 32 * 32 * ra + 32 * 32 * rb + 32 * rc + rd" and 
               b = "k" and 
               c = "0" and
               d = "64" and
               e = "1" in add_mod_div)
  apply simp
 apply simp
apply simp
apply (simp add: mult.commute)
done

lemma convert_reg_reg_opcode2:
  "\<lbrakk> k < 64 \<rbrakk> \<Longrightarrow> (ra * 2097152 + rb * 65536 + rc * 2048 + (k::nat)) mod 64 = k"
apply (drule_tac rd = 0 in convert_reg_reg_opcode2_help)
apply simp
done

lemma convert_reg_reg_opcode2_SA:
  "\<lbrakk> k < 64 \<rbrakk> \<Longrightarrow> (ra * 2097152 + rc * 2048 + rd * 64 + (k::nat)) mod 64 = k"
apply (drule_tac rb = 0 in convert_reg_reg_opcode2_help)
apply simp
done

lemma nat_to_instr_R_eq_nat_to_instr_R_al:
  "\<lbrakk> ra < 32; rb < 32; rc < 32; 32 \<le> k \<and> k \<le> 39 \<rbrakk> 
  \<Longrightarrow> nat_to_instr_R (ra * 2097152 + rb * 65536 + rc * 2048 + k) = nat_to_instr_R_al ra rb rc k"
apply (simp (no_asm) add: nat_to_instr_R_def split del: if_split del: Let_def)
apply (subst convert_reg_reg_reg1, assumption+)
 apply simp
apply (subst convert_reg_reg_reg2, assumption+)
 apply simp
apply (subst convert_reg_reg_reg3, assumption+)
 apply simp
apply (subst convert_reg_reg_reg4)
 apply simp
apply (subst convert_reg_reg_opcode2)
 apply simp
apply simp
done

lemma nat_to_instr_eq_nat_to_instr_R_al:
  "\<lbrakk>ra < 32; rb < 32; rc < 32; 32 \<le> k \<and> k \<le> 39 \<rbrakk> 
  \<Longrightarrow> nat_to_instr (ra * 2097152 + rb * 65536 + rc * 2048 + k) = nat_to_instr_R_al ra rb rc k"
apply (subst nat_to_instr_eq_nat_to_instr_R, assumption+)
 apply simp
apply (erule nat_to_instr_R_eq_nat_to_instr_R_al, assumption+)
done

lemma nat_to_instr_eq_Ilhg:
  "\<lbrakk>rb < 32; rc < 32 \<rbrakk> 
  \<Longrightarrow> nat_to_instr (rb * 65536 + rc * 2048 + 39) = Ilhg rc rb"
apply (subgoal_tac "rb * 65536 + rc * 2048 + 39 = 0 * 2097152 + rb * 65536 + rc * 2048 + 39")
 prefer 2
 apply simp
apply (rotate_tac -1, erule ssubst)
apply (subst nat_to_instr_eq_nat_to_instr_R_al)
    apply simp
   apply assumption+
 apply simp
apply (simp add: nat_to_instr_R_al_def)
done

lemma nat_to_instr_R_eq_nat_to_instr_R_comp:
  "\<lbrakk> ra < 32; rb < 32; rc < 32; 40 \<le> k \<and> k \<le> 47 \<rbrakk> 
  \<Longrightarrow> nat_to_instr_R (ra * 2097152 + rb * 65536 + rc * 2048 + k) = nat_to_instr_R_comp ra rb rc k"
apply (simp (no_asm) add: nat_to_instr_R_def split del: if_split del: Let_def)
apply (subst convert_reg_reg_reg1, assumption+)
 apply simp
apply (subst convert_reg_reg_reg2, assumption+)
 apply simp
apply (subst convert_reg_reg_reg3, assumption+)
 apply simp
apply (subst convert_reg_reg_reg4)
 apply simp
apply (subst convert_reg_reg_opcode2)
 apply simp
apply simp
done

lemma nat_to_instr_eq_nat_to_instr_R_comp:
  "\<lbrakk>ra < 32; rb < 32; rc < 32; 40 \<le> k \<and> k \<le> 47 \<rbrakk> 
  \<Longrightarrow> nat_to_instr (ra * 2097152 + rb * 65536 + rc * 2048 + k) = nat_to_instr_R_comp ra rb rc k"
apply (subst nat_to_instr_eq_nat_to_instr_R, assumption+)
 apply simp
apply (erule nat_to_instr_R_eq_nat_to_instr_R_comp, assumption+)
done

lemma nat_to_instr_eq_nat_to_instr_R_comp_clr_or_set:
  "\<lbrakk> rc < 32; 40 \<le> k \<and> k \<le> 47 \<rbrakk> 
  \<Longrightarrow> nat_to_instr (rc * 2048 + k) = nat_to_instr_R_comp 0 0 rc k"
apply (subgoal_tac "rc * 2048 + k = 0 * 2097152 + 0 * 65536 + rc * 2048 + k")
 prefer 2
 apply simp
apply (rotate_tac -1, erule ssubst)
apply (rule nat_to_instr_eq_nat_to_instr_R_comp)
   apply simp
  apply simp
 apply assumption
apply simp
done

lemma nat_to_instr_R_eq_nat_to_instr_R_shift_help:
  "\<lbrakk> ra < 32; rb < 32; rc < 32; rd < 32; k < 8 \<rbrakk>
  \<Longrightarrow> nat_to_instr_R (ra * 2097152 + rb * 65536 + rc * 2048 + rd * 64 + k) = nat_to_instr_R_shift ra rb rc rd k"
apply (simp (no_asm) add: nat_to_instr_R_def split del: if_split del: Let_def)
apply (subst convert_reg_reg_reg1_help, assumption+)
 apply simp
apply (subst convert_reg_reg_reg2_help, assumption+)
 apply simp
apply (subst convert_reg_reg_reg3_help, assumption+)
 apply simp
apply (subst convert_reg_reg_reg4_help, assumption+)
 apply simp
apply (subst convert_reg_reg_opcode2_help)
 apply simp
apply simp
done

lemma nat_to_instr_R_eq_nat_to_instr_R_shift:
  "\<lbrakk> ra < 32; rb < 32; rc < 32; k < 8 \<rbrakk>
  \<Longrightarrow> nat_to_instr_R (ra * 2097152 + rb * 65536 + rc * 2048 + k) = nat_to_instr_R_shift ra rb rc 0 k"
apply (drule_tac rc = rc and rd = 0 in nat_to_instr_R_eq_nat_to_instr_R_shift_help, assumption+)
  apply simp
 apply assumption
apply simp
done

lemma nat_to_instr_R_eq_nat_to_instr_R_shift_SA:
  "\<lbrakk> ra < 32; rc < 32; asm_sa rd; k < 8 \<rbrakk>
  \<Longrightarrow> nat_to_instr_R (ra * 2097152 + rc * 2048 + rd * 64 + k) = nat_to_instr_R_shift ra 0 rc rd k"
apply (drule_tac rb = 0 and rd = rd in nat_to_instr_R_eq_nat_to_instr_R_shift_help)
    apply simp
   apply assumption
  apply (simp add: asm_sa_def wlen_bit_def)
 apply assumption
apply simp
done

lemma nat_to_instr_eq_nat_to_instr_R_shift:
  "\<lbrakk> ra < 32; rb < 32; rc < 32; k < 8 \<rbrakk>
  \<Longrightarrow> nat_to_instr (ra * 2097152 + rb * 65536 + rc * 2048 + k) = nat_to_instr_R_shift ra rb rc 0 k"
apply (subst nat_to_instr_eq_nat_to_instr_R, assumption+)
 apply simp
apply (erule nat_to_instr_R_eq_nat_to_instr_R_shift, assumption+)
done

lemma nat_to_instr_eq_nat_to_instr_R_shift_SA:
  "\<lbrakk> ra < 32; rc < 32; asm_sa rd; k < 8 \<rbrakk>
  \<Longrightarrow> nat_to_instr (ra * 2097152 + rc * 2048 + rd * 64 + k) = nat_to_instr_R_shift ra 0 rc rd k"
apply (subst nat_to_instr_eq_nat_to_instr_R_SA, assumption+)
 apply simp
apply (erule nat_to_instr_R_eq_nat_to_instr_R_shift_SA, assumption+)
done

lemma nat_to_instr_eq_Imovs2i:
  "\<lbrakk> rc < 32; rd < 32 \<rbrakk>
  \<Longrightarrow> nat_to_instr (rc * 2048 + rd * 64 + 16) = Imovs2i rc rd"
apply (simp (no_asm) add: nat_to_instr_def split del: if_split)
apply (subgoal_tac "rc * 2048 + rd * 64 + 16 = 0 * 2097152 + 0 * 65536 + rc * 2048 + rd * 64 + 16")
 prefer 2
 apply simp
apply (rotate_tac -1, erule ssubst)
apply (subst convert_reg_reg_opcode1_help)
    apply simp
   apply assumption+
 apply simp
apply simp
apply (simp (no_asm) add: nat_to_instr_R_def split del: if_split del: Let_def)
apply (subgoal_tac "rc * 2048 + rd * 64 + 16 = 0 * 2097152 + 0 * 65536 + rc * 2048 + rd * 64 + 16")
 prefer 2
 apply simp
apply (rotate_tac -1, erule ssubst)
apply (subst convert_reg_reg_reg3_help, assumption+)
 apply simp
apply (subst convert_reg_reg_reg4_help, assumption)
 apply simp
apply (subst convert_reg_reg_opcode2_help)
 apply simp
apply (simp (no_asm))
apply (simp (no_asm) add: nat_to_instr_R_mov_def)
done

lemma nat_to_instr_eq_Imovi2s:
  "\<lbrakk> ra < 32; rd < 32 \<rbrakk>
  \<Longrightarrow> nat_to_instr (ra * 2097152 + rd * 64 + 17) = Imovi2s rd ra"
apply (simp (no_asm) add: nat_to_instr_def split del: if_split)
apply (subgoal_tac "ra * 2097152 + rd * 64 + 17 = ra * 2097152 + 0 * 65536 + 0 * 2048 + rd * 64 + 17")
 prefer 2
 apply simp
apply (rotate_tac -1, erule ssubst)
apply (subst convert_reg_reg_opcode1_help, assumption)
   apply simp
  apply assumption
 apply simp
apply simp
apply (simp (no_asm) add: nat_to_instr_R_def split del: if_split del: Let_def)
apply (subgoal_tac "ra * 2097152 + rd * 64 + 17 = ra * 2097152 + 0 * 65536 + 0 * 2048 + rd * 64 + 17")
 prefer 2
 apply simp
apply (rotate_tac -1, erule ssubst)
apply (subst convert_reg_reg_reg1_help)
   apply simp
  apply assumption
 apply simp
apply (subst convert_reg_reg_reg4_help, assumption)
 apply simp
apply (subst convert_reg_reg_opcode2_help)
 apply simp
apply (simp (no_asm))
apply (simp (no_asm) add: nat_to_instr_R_mov_def)
done

lemma instr_to_nat_to_instr: "is_instr iw \<Longrightarrow> nat_to_instr (instr_to_nat iw) = iw"
apply (case_tac iw)
apply (simp_all add: is_instr_def)

apply (erule_tac [1-26] conjE)
apply (erule_tac [1-8] conjE)

apply (subst nat_to_instr_eq_nat_to_instr_I_mem, assumption+)
  apply simp
 apply simp
apply (simp add: nat_to_instr_I_mem_def)

apply (subst nat_to_instr_eq_nat_to_instr_I_mem, assumption+)
  apply simp
 apply simp
apply (simp add: nat_to_instr_I_mem_def)

apply (subst nat_to_instr_eq_nat_to_instr_I_mem, assumption+)
  apply simp
 apply simp
apply (simp add: nat_to_instr_I_mem_def)

apply (subst nat_to_instr_eq_nat_to_instr_I_mem, assumption+)
  apply simp
 apply simp
apply (simp add: nat_to_instr_I_mem_def)

apply (subst nat_to_instr_eq_nat_to_instr_I_mem, assumption+)
  apply simp
 apply simp
apply (simp add: nat_to_instr_I_mem_def)

apply (subst nat_to_instr_eq_nat_to_instr_I_mem, assumption+)
  apply simp
 apply simp
apply (simp add: nat_to_instr_I_mem_def)

apply (subst nat_to_instr_eq_nat_to_instr_I_mem, assumption+)
  apply simp
 apply simp
apply (simp add: nat_to_instr_I_mem_def)

apply (subst nat_to_instr_eq_nat_to_instr_I_mem, assumption+)
  apply simp
 apply simp
apply (simp add: nat_to_instr_I_mem_def)

apply (erule nat_to_instr_eq_Ilhgi, assumption)

apply (erule nat_to_instr_eq_Ilhg, assumption)

apply (erule nat_to_instr_eq_Imovs2i, assumption)

apply (erule nat_to_instr_eq_Imovi2s, assumption)

apply (erule_tac [1-14] conjE)

apply (subst nat_to_instr_eq_nat_to_instr_I_al, assumption+)
  apply simp
 apply simp
apply (simp add: nat_to_instr_I_al_def)

apply (subst nat_to_instr_eq_nat_to_instr_I_al, assumption+)
  apply simp
 apply simp
apply (simp add: nat_to_instr_I_al_def)

apply (subst nat_to_instr_eq_nat_to_instr_I_al, assumption+)
  apply simp
 apply simp
apply (simp add: nat_to_instr_I_al_def)

apply (subst nat_to_instr_eq_nat_to_instr_I_al, assumption+)
  apply simp
 apply simp
apply (simp add: nat_to_instr_I_al_def)

apply (subst nat_to_instr_eq_nat_to_instr_I_al, assumption+)
  apply simp
 apply simp
apply (simp add: nat_to_instr_I_al_def)

apply (subst nat_to_instr_eq_nat_to_instr_I_al, assumption+)
  apply simp
 apply simp
apply (simp add: nat_to_instr_I_al_def)

apply (subst nat_to_instr_eq_nat_to_instr_I_al, assumption+)
  apply simp
 apply simp
apply (simp add: nat_to_instr_I_al_def)

apply (subst nat_to_instr_eq_nat_to_instr_R_al, assumption+)
 apply simp
apply (simp add: nat_to_instr_R_al_def)

apply (subst nat_to_instr_eq_nat_to_instr_R_al, assumption+)
 apply simp
apply (simp add: nat_to_instr_R_al_def)

apply (subst nat_to_instr_eq_nat_to_instr_R_al, assumption+)
 apply simp
apply (simp add: nat_to_instr_R_al_def)

apply (subst nat_to_instr_eq_nat_to_instr_R_al, assumption+)
 apply simp
apply (simp add: nat_to_instr_R_al_def)

apply (subst nat_to_instr_eq_nat_to_instr_R_al, assumption+)
 apply simp
apply (simp add: nat_to_instr_R_al_def)

apply (subst nat_to_instr_eq_nat_to_instr_R_al, assumption+)
 apply simp
apply (simp add: nat_to_instr_R_al_def)

apply (subst nat_to_instr_eq_nat_to_instr_R_al, assumption+)
 apply simp
apply (simp add: nat_to_instr_R_al_def)

apply (subst nat_to_instr_eq_nat_to_instr_I_comp_clr_or_set, assumption)
  apply simp
 apply simp
apply (simp add: nat_to_instr_I_comp_def)

apply (erule_tac [1-6] conjE)
apply (erule_tac [1-6] conjE)

apply (subst nat_to_instr_eq_nat_to_instr_I_comp, assumption+)
  apply simp
 apply simp
apply (simp add: nat_to_instr_I_comp_def)

apply (subst nat_to_instr_eq_nat_to_instr_I_comp, assumption+)
  apply simp
 apply simp
apply (simp add: nat_to_instr_I_comp_def)

apply (subst nat_to_instr_eq_nat_to_instr_I_comp, assumption+)
  apply simp
 apply simp
apply (simp add: nat_to_instr_I_comp_def)

apply (subst nat_to_instr_eq_nat_to_instr_I_comp, assumption+)
  apply simp
 apply simp
apply (simp add: nat_to_instr_I_comp_def)

apply (subst nat_to_instr_eq_nat_to_instr_I_comp, assumption+)
  apply simp
 apply simp
apply (simp add: nat_to_instr_I_comp_def)

apply (subst nat_to_instr_eq_nat_to_instr_I_comp, assumption+)
  apply simp
 apply simp
apply (simp add: nat_to_instr_I_comp_def)

apply (subst nat_to_instr_eq_nat_to_instr_I_comp_clr_or_set, assumption)
  apply simp
 apply simp
apply (simp add: nat_to_instr_I_comp_def)

apply (subst nat_to_instr_eq_nat_to_instr_R_comp_clr_or_set, assumption)
 apply simp
apply (simp add: nat_to_instr_R_comp_def)

apply (erule_tac [1-6] conjE)
apply (erule_tac [1-6] conjE)
apply (simp add : nat_to_instr_eq_nat_to_instr_R_comp )
apply (simp add: nat_to_instr_R_comp_def)

apply (subst nat_to_instr_eq_nat_to_instr_R_comp, assumption+)
 apply simp
apply (simp add: nat_to_instr_R_comp_def)

apply (subst nat_to_instr_eq_nat_to_instr_R_comp, assumption+)
 apply simp
apply (simp add: nat_to_instr_R_comp_def)

apply (subst nat_to_instr_eq_nat_to_instr_R_comp, assumption+)
 apply simp
apply (simp add: nat_to_instr_R_comp_def)

apply (subst nat_to_instr_eq_nat_to_instr_R_comp, assumption+)
 apply simp
apply (simp add: nat_to_instr_R_comp_def)

apply (subst nat_to_instr_eq_nat_to_instr_R_comp, assumption+)
 apply simp
apply (simp add: nat_to_instr_R_comp_def)

apply (subst nat_to_instr_eq_nat_to_instr_R_comp_clr_or_set, assumption)
 apply simp
apply (simp add: nat_to_instr_R_comp_def)

apply (erule_tac [1-8] conjE)
apply (erule_tac [1-6] conjE)

apply (drule_tac ra = x432 and rc = x431 and rd = x433 and k = 0 in 
       nat_to_instr_eq_nat_to_instr_R_shift_SA, assumption+)
 apply simp
apply simp
apply (rotate_tac -1, erule ssubst)
apply (simp add: nat_to_instr_R_shift_def)

apply (drule_tac ra = x442 and rc = x441 and rd = x443 and k = 2 in 
       nat_to_instr_eq_nat_to_instr_R_shift_SA, assumption+)
 apply simp
apply simp
apply (rotate_tac -1, erule ssubst)
apply (simp add: nat_to_instr_R_shift_def)

apply (subst nat_to_instr_eq_nat_to_instr_R_shift_SA, assumption+)
 apply simp
apply (simp add: nat_to_instr_R_shift_def)

apply (subst nat_to_instr_eq_nat_to_instr_R_shift, assumption+)
 apply simp
apply (simp add: nat_to_instr_R_shift_def)

apply (subst nat_to_instr_eq_nat_to_instr_R_shift, assumption+)
 apply simp
apply (simp add: nat_to_instr_R_shift_def)

apply (subst nat_to_instr_eq_nat_to_instr_R_shift, assumption+)
 apply simp
apply (simp add: nat_to_instr_R_shift_def)

apply (subst nat_to_instr_eq_nat_to_instr_I_branch, assumption+)
  apply simp
 apply simp
apply simp

apply (subst nat_to_instr_eq_nat_to_instr_I_branch, assumption+)
  apply simp
 apply simp
apply simp

apply (subst nat_to_instr_eq_nat_to_instr_I_jump_imm, assumption+)
  apply simp
 apply simp
apply simp

apply (subst nat_to_instr_eq_nat_to_instr_I_jump_reg, assumption+)
  apply simp
 apply simp
apply simp

apply (subst nat_to_instr_eq_nat_to_instr_I_jump_imm, assumption+)
  apply simp
 apply simp
apply simp

apply (subst nat_to_instr_eq_nat_to_instr_I_jump_reg, assumption+)
  apply simp
 apply simp
apply simp

apply (erule nat_to_instr_eq_Itrap)

apply (rule nat_to_instr_eq_Irfe)
done

lemma instr_to_int_to_instr: "is_instr iw \<Longrightarrow> int_to_instr (instr_to_int iw) = iw"
apply (simp add: int_to_instr_def instr_to_int_def)
apply (simp add: natwd2intwd2natwd)
apply (erule instr_to_nat_to_instr)
done

definition is_R_opcode :: "nat \<Rightarrow> bool"
where
  "is_R_opcode n \<equiv> n \<le> 7 \<or> 16 \<le> n \<and> n \<le> 17 \<or> 32 \<le> n \<and> n \<le> 47"

definition is_I_opcode :: "nat \<Rightarrow> bool"
where
  "is_I_opcode n \<equiv> 2 \<le> n \<and> n \<le> 5 \<or> 8 \<le> n \<and> n \<le> 15 \<or> 22 \<le> n \<and> n \<le> 33 \<or> 35 \<le> n \<and> n \<le> 37 \<or> 40 \<le> n \<and> n \<le> 41 \<or> n = 43 \<or> 62 \<le> n \<and> n \<le> 63"

definition decodable_instr_nat :: "nat \<Rightarrow> bool"
where
  "decodable_instr_nat n \<equiv> n div 2^26 = 0 \<and> is_R_opcode (n mod 2^6) \<or> is_I_opcode (n div 2^26)"

definition decodable_instr_int :: "int \<Rightarrow> bool"
where
  "decodable_instr_int i \<equiv> decodable_instr_nat (intwd_as_nat i)"

lemma decodable_instr_nat_eq_is_R_opcode: "n < 67108864 \<Longrightarrow> decodable_instr_nat n = is_R_opcode (n mod 64)"
apply (simp add: decodable_instr_nat_def)
apply (simp add: is_I_opcode_def)
done

lemma decodable_instr_nat_eq_is_I_opcode: "67108864 \<le> n \<Longrightarrow> decodable_instr_nat n = is_I_opcode (n div 67108864)"
apply (simp add: decodable_instr_nat_def)
apply (case_tac "is_I_opcode (n div 67108864)", simp_all)
apply (rule disjI1)
apply (subst div_if)
 apply simp
apply simp
done

lemma decodable_instr_nat_eq_is_R_opcode'':
      "\<lbrakk> ra < 32; rb < 32; rc < 32; rd < 32; k < 64 \<rbrakk> \<Longrightarrow> decodable_instr_nat (ra * 2097152 + rb * 65536 + rc * 2048 + rd * 64 + k) = is_R_opcode k"
apply (subst decodable_instr_nat_eq_is_R_opcode)
 apply (rule_tac y = "31 * 2097152 + rb * 65536 + rc * 2048 + rd * 64 + k" in le_less_trans)
  apply simp
 apply (rule_tac y = "31 * 2097152 + 31 * 65536 + rc * 2048 + rd * 64 + k" in le_less_trans)
  apply simp
 apply (rule_tac y = "31 * 2097152 + 31 * 65536 + 31 * 2048 + rd * 64 + k" in le_less_trans)
  apply simp
 apply (rule_tac y = "31 * 2097152 + 31 * 65536 + 31 * 2048 + 31 * 64 + k" in le_less_trans)
  apply simp+
apply (rule_tac f = "is_R_opcode" in arg_cong)
apply (erule convert_reg_reg_opcode2_help)
done

lemma decodable_instr_nat_eq_is_R_opcode':
      "\<lbrakk> ra < 32; rb < 32; rc < 32; k < 64 \<rbrakk> \<Longrightarrow> decodable_instr_nat (ra * 2097152 + rb * 65536 + rc * 2048 + k) = is_R_opcode k"
apply (cut_tac ra = ra and rb = rb and rc = rc and rd = 0 in decodable_instr_nat_eq_is_R_opcode'', assumption+)
  apply simp
 apply assumption
apply simp
done

lemma decodable_instr_nat_eq_is_I_opcode':
      "\<lbrakk> ra < 32; rb < 32; a = k * 67108864; Suc 0 \<le> k \<rbrakk> \<Longrightarrow> decodable_instr_nat (a + ra * 2097152 + rb * 65536 + imm16_to_nat imm) = is_I_opcode k"
apply (subst decodable_instr_nat_eq_is_I_opcode)
 apply (rule trans_le_add1)+
 apply simp
apply (rule_tac f = "is_I_opcode" in arg_cong)
apply (rule convert_reg_imm_opcode, assumption+)
done

lemma decodable_instr_nat_eq_is_I_opcode'':
      "\<lbrakk> a = k * 67108864; Suc 0 \<le> k \<rbrakk> \<Longrightarrow> decodable_instr_nat (a + imm26_to_nat imm) = is_I_opcode k"
apply (subst decodable_instr_nat_eq_is_I_opcode)
 apply (rule trans_le_add1)
 apply simp
apply (rule_tac f = "is_I_opcode" in arg_cong)
apply (rule convert_reg_imm_opcode_26, assumption+)
done

lemma  is_instr_imp_decodable:
"is_instr iw \<Longrightarrow> decodable_instr_int (instr_to_int iw)"
apply (simp add: instr_to_int_def)
apply (simp add: decodable_instr_int_def)
apply (subst natwd2intwd2natwd)
apply (case_tac iw, simp_all)

apply (clarsimp simp add: is_instr_def)
apply (subst decodable_instr_nat_eq_is_I_opcode', assumption+)
  apply simp
 apply simp
apply (simp add: is_I_opcode_def)

apply (clarsimp simp add: is_instr_def)
apply (subst decodable_instr_nat_eq_is_I_opcode', assumption+)
  apply simp
 apply simp
apply (simp add: is_I_opcode_def)

apply (clarsimp simp add: is_instr_def)
apply (subst decodable_instr_nat_eq_is_I_opcode', assumption+)
  apply simp
 apply simp
apply (simp add: is_I_opcode_def)

apply (clarsimp simp add: is_instr_def)
apply (subst decodable_instr_nat_eq_is_I_opcode', assumption+)
  apply simp
 apply simp
apply (simp add: is_I_opcode_def)

apply (clarsimp simp add: is_instr_def)
apply (subst decodable_instr_nat_eq_is_I_opcode', assumption+)
  apply simp
 apply simp
apply (simp add: is_I_opcode_def)

apply (clarsimp simp add: is_instr_def)
apply (subst decodable_instr_nat_eq_is_I_opcode', assumption+)
  apply simp
 apply simp
apply (simp add: is_I_opcode_def)

apply (clarsimp simp add: is_instr_def)
apply (subst decodable_instr_nat_eq_is_I_opcode', assumption+)
  apply simp
 apply simp
apply (simp add: is_I_opcode_def)

apply (clarsimp simp add: is_instr_def)
apply (subst decodable_instr_nat_eq_is_I_opcode', assumption+)
  apply simp
 apply simp
apply (simp add: is_I_opcode_def)

apply (clarsimp simp add: is_instr_def)
apply (subst decodable_instr_nat_eq_is_I_opcode'[where ra = 0, simplified], assumption)
  apply simp
 apply simp
apply (simp add: is_I_opcode_def)

apply (clarsimp simp add: is_instr_def)
apply (subst decodable_instr_nat_eq_is_R_opcode'[where ra = 0, simplified], assumption+)
 apply simp
apply (simp add: is_R_opcode_def)

apply (clarsimp simp add: is_instr_def)
apply (subst decodable_instr_nat_eq_is_R_opcode''[where ra = 0 and rb = 0, simplified], assumption+)
 apply simp
apply (simp add: is_R_opcode_def)

apply (clarsimp simp add: is_instr_def)
apply (subst decodable_instr_nat_eq_is_R_opcode''[where rb = 0 and rc = 0, simplified], assumption+)
 apply simp
apply (simp add: is_R_opcode_def)

apply (clarsimp simp add: is_instr_def)
apply (subst decodable_instr_nat_eq_is_I_opcode', assumption+)
  apply simp
 apply simp
apply (simp add: is_I_opcode_def)

apply (clarsimp simp add: is_instr_def)
apply (subst decodable_instr_nat_eq_is_I_opcode', assumption+)
  apply simp
 apply simp
apply (simp add: is_I_opcode_def)

apply (clarsimp simp add: is_instr_def)
apply (subst decodable_instr_nat_eq_is_I_opcode', assumption+)
  apply simp
 apply simp
apply (simp add: is_I_opcode_def)

apply (clarsimp simp add: is_instr_def)
apply (subst decodable_instr_nat_eq_is_I_opcode', assumption+)
  apply simp
 apply simp
apply (simp add: is_I_opcode_def)

apply (clarsimp simp add: is_instr_def)
apply (subst decodable_instr_nat_eq_is_I_opcode', assumption+)
  apply simp
 apply simp
apply (simp add: is_I_opcode_def)

apply (clarsimp simp add: is_instr_def)
apply (subst decodable_instr_nat_eq_is_I_opcode', assumption+)
  apply simp
 apply simp
apply (simp add: is_I_opcode_def)

apply (clarsimp simp add: is_instr_def)
apply (subst decodable_instr_nat_eq_is_I_opcode', assumption+)
  apply simp
 apply simp
apply (simp add: is_I_opcode_def)

apply (clarsimp simp add: is_instr_def)
apply (subst decodable_instr_nat_eq_is_R_opcode', assumption+)
 apply simp
apply (simp add: is_R_opcode_def)

apply (clarsimp simp add: is_instr_def)
apply (subst decodable_instr_nat_eq_is_R_opcode', assumption+)
 apply simp
apply (simp add: is_R_opcode_def)

apply (clarsimp simp add: is_instr_def)
apply (subst decodable_instr_nat_eq_is_R_opcode', assumption+)
 apply simp
apply (simp add: is_R_opcode_def)

apply (clarsimp simp add: is_instr_def)
apply (subst decodable_instr_nat_eq_is_R_opcode', assumption+)
 apply simp
apply (simp add: is_R_opcode_def)

apply (clarsimp simp add: is_instr_def)
apply (subst decodable_instr_nat_eq_is_R_opcode', assumption+)
 apply simp
apply (simp add: is_R_opcode_def)

apply (clarsimp simp add: is_instr_def)
apply (subst decodable_instr_nat_eq_is_R_opcode', assumption+)
 apply simp
apply (simp add: is_R_opcode_def)

apply (clarsimp simp add: is_instr_def)
apply (subst decodable_instr_nat_eq_is_R_opcode', assumption+)
 apply simp
apply (simp add: is_R_opcode_def)

apply (clarsimp simp add: is_instr_def)
apply (subgoal_tac "1610612736 + x27 * 65536 = 
                    1610612736 + 0 * 2097152 + x27 * 65536 + imm16_to_nat 0")
 prefer 2
 apply (simp add: imm16_to_nat_def)
apply (rotate_tac -1, erule ssubst)
apply (subst decodable_instr_nat_eq_is_I_opcode')
    apply simp
   apply assumption
  apply simp
 apply simp
apply (simp add: is_I_opcode_def)

apply (clarsimp simp add: is_instr_def)
apply (subst decodable_instr_nat_eq_is_I_opcode', assumption+)
  apply simp
 apply simp
apply (simp add: is_I_opcode_def)

apply (clarsimp simp add: is_instr_def)
apply (subst decodable_instr_nat_eq_is_I_opcode', assumption+)
  apply simp
 apply simp
apply (simp add: is_I_opcode_def)

apply (clarsimp simp add: is_instr_def)
apply (subst decodable_instr_nat_eq_is_I_opcode', assumption+)
  apply simp
 apply simp
apply (simp add: is_I_opcode_def)

apply (clarsimp simp add: is_instr_def)
apply (subst decodable_instr_nat_eq_is_I_opcode', assumption+)
  apply simp
 apply simp
apply (simp add: is_I_opcode_def)

apply (clarsimp simp add: is_instr_def)
apply (subst decodable_instr_nat_eq_is_I_opcode', assumption+)
  apply simp
 apply simp
apply (simp add: is_I_opcode_def)

apply (clarsimp simp add: is_instr_def)
apply (subst decodable_instr_nat_eq_is_I_opcode', assumption+)
  apply simp
 apply simp
apply (simp add: is_I_opcode_def)

apply (clarsimp simp add: is_instr_def)
apply (subgoal_tac "2080374784 + x34 * 65536 = 
       2080374784 + 0 * 2097152 + x34 * 65536 + imm16_to_nat 0")
 prefer 2
 apply (simp add: imm16_to_nat_def)
apply (rotate_tac -1, erule ssubst)
apply (subst decodable_instr_nat_eq_is_I_opcode')
    apply simp
   apply assumption
  apply simp
 apply simp
apply (simp add: is_I_opcode_def)

apply (clarsimp simp add: is_instr_def)
apply (subst decodable_instr_nat_eq_is_R_opcode'[where ra = 0 and rb = 0, simplified], assumption)
 apply simp
apply (simp add: is_R_opcode_def)

apply (clarsimp simp add: is_instr_def)
apply (subst decodable_instr_nat_eq_is_R_opcode', assumption+)
 apply simp
apply (simp add: is_R_opcode_def)

apply (clarsimp simp add: is_instr_def)
apply (subst decodable_instr_nat_eq_is_R_opcode', assumption+)
 apply simp
apply (simp add: is_R_opcode_def)

apply (clarsimp simp add: is_instr_def)
apply (subst decodable_instr_nat_eq_is_R_opcode', assumption+)
 apply simp
apply (simp add: is_R_opcode_def)

apply (clarsimp simp add: is_instr_def)
apply (subst decodable_instr_nat_eq_is_R_opcode', assumption+)
 apply simp
apply (simp add: is_R_opcode_def)

apply (clarsimp simp add: is_instr_def)
apply (subst decodable_instr_nat_eq_is_R_opcode', assumption+)
 apply simp
apply (simp add: is_R_opcode_def)

apply (clarsimp simp add: is_instr_def)
apply (subst decodable_instr_nat_eq_is_R_opcode', assumption+)
 apply simp
apply (simp add: is_R_opcode_def)

apply (clarsimp simp add: is_instr_def)
apply (subst decodable_instr_nat_eq_is_R_opcode'[where ra = 0 and rb = 0, simplified], assumption)
 apply simp
apply (simp add: is_R_opcode_def)

apply (clarsimp simp add: is_instr_def)
apply (subst decodable_instr_nat_eq_is_R_opcode''[where rb = 0 and k = 0, simplified], assumption+)
 apply (simp add: asm_sa_def wlen_bit_def)
apply (simp add: is_R_opcode_def)

apply (clarsimp simp add: is_instr_def)
apply (subst decodable_instr_nat_eq_is_R_opcode''[where rb = 0 and k = 2, simplified], assumption+)
 apply (simp add: asm_sa_def wlen_bit_def)
apply (simp add: is_R_opcode_def)

apply (clarsimp simp add: is_instr_def)
apply (subst decodable_instr_nat_eq_is_R_opcode''[where rb = 0, simplified], assumption+)
  apply (simp add: asm_sa_def wlen_bit_def)
 apply simp
apply (simp add: is_R_opcode_def)

apply (clarsimp simp add: is_instr_def)
apply (subst decodable_instr_nat_eq_is_R_opcode', assumption+)
 apply simp
apply (simp add: is_R_opcode_def)

apply (clarsimp simp add: is_instr_def)
apply (subst decodable_instr_nat_eq_is_R_opcode', assumption+)
 apply simp
apply (simp add: is_R_opcode_def)

apply (clarsimp simp add: is_instr_def)
apply (subst decodable_instr_nat_eq_is_R_opcode', assumption+)
 apply simp
apply (simp add: is_R_opcode_def)

apply (clarsimp simp add: is_instr_def)
apply (subst decodable_instr_nat_eq_is_I_opcode'[where rb = 0, simplified], assumption+)
  apply simp
 apply simp
apply (simp add: is_I_opcode_def)

apply (clarsimp simp add: is_instr_def)
apply (subst decodable_instr_nat_eq_is_I_opcode'[where rb = 0, simplified], assumption+)
  apply simp
 apply simp
apply (simp add: is_I_opcode_def)

apply (clarsimp simp add: is_instr_def)
apply (subst decodable_instr_nat_eq_is_I_opcode'')
  apply simp
 apply simp
apply (simp add: is_I_opcode_def)

apply (clarsimp simp add: is_instr_def)
apply (subgoal_tac "1543503872 + x52a * 2097152 = 
                    1543503872 + x52a * 2097152 + 0 * 65536 + imm16_to_nat 0")
 prefer 2
 apply (simp add: imm16_to_nat_def)
apply (rotate_tac -1, erule ssubst)
apply (subst decodable_instr_nat_eq_is_I_opcode', assumption)
   apply simp
  apply simp
 apply simp
apply (simp add: is_I_opcode_def)

apply (clarsimp simp add: is_instr_def)
apply (subst decodable_instr_nat_eq_is_I_opcode'')
  apply simp
 apply simp
apply (simp add: is_I_opcode_def)

apply (clarsimp simp add: is_instr_def)
apply (subgoal_tac "1476395008 + x54 * 2097152 = 
                    1476395008 + x54 * 2097152 + 0 * 65536 + imm16_to_nat 0")
 prefer 2
 apply (simp add: imm16_to_nat_def)
apply (rotate_tac -1, erule ssubst)
apply (subst decodable_instr_nat_eq_is_I_opcode', assumption)
   apply simp
  apply simp
 apply simp
apply (simp add: is_I_opcode_def)

apply (clarsimp simp add: is_instr_def)
apply (subst decodable_instr_nat_eq_is_I_opcode'')
  apply simp
 apply simp
apply (simp add: is_I_opcode_def)

apply (simp add: decodable_instr_nat_def)
apply (simp add: is_I_opcode_def)
done

lemma decodable_imp_is_instr:
assumes "decodable_instr_int i"
  shows "is_instr (int_to_instr i)"
proof -

  have less_32:
     "intwd_as_nat i mod 65536 div 2048 < 32 \<and>
      intwd_as_nat i mod 67108864 div 2097152 < 32 \<and>
      intwd_as_nat i mod 2097152 div 65536 < 32 \<and>
      intwd_as_nat i mod 2048 div 64 < 32"
    apply (cut_tac a = "intwd_as_nat i mod 2097152" and b = "32"
               and c = "65536" in less_mult_impl_div_less, simp_all)
    apply (cut_tac a = "intwd_as_nat i mod 67108864" and b = "32"
               and c= "2097152" in less_mult_impl_div_less, simp_all)
    by (cut_tac a = "intwd_as_nat i mod 65536" and b = "32"
               and c = "2048" in less_mult_impl_div_less, simp_all)


  have asm_imm16:
  "asm_imm16 (nat_to_imm16 (intwd_as_nat i mod 65536))"
  by (clarsimp simp add: asm_imm16_def nat_to_imm16_def, arith)

  have asm_imm26:
  "asm_imm26 (nat_to_imm26 (intwd_as_nat i mod 67108864))"
  by (clarsimp simp add: asm_imm26_def nat_to_imm26_def, arith)

  have asm_sa:
  "asm_sa (intwd_as_nat i mod 2048 div 64)"
  by (simp add: asm_sa_def wlen_bit_def)

  have R_less_32:
    "intwd_as_nat i div 67108864 = 0
      \<Longrightarrow> intwd_as_nat i div 2097152 < 32"
    by (cut_tac a = "intwd_as_nat i"and b = "32"
               and c = "2097152" in less_mult_impl_div_less, simp_all)

  have is_instr_I_mem:
  "\<lbrakk>intwd_as_nat i div 67108864 = 43 \<or>
    40 \<le> intwd_as_nat i div 67108864 \<and> intwd_as_nat i div 67108864 \<le> 41 \<or>
    35 \<le> intwd_as_nat i div 67108864 \<and> intwd_as_nat i div 67108864 \<le> 37 \<or>
    32 \<le> intwd_as_nat i div 67108864 \<and> intwd_as_nat i div 67108864 \<le> 33 \<rbrakk>
   \<Longrightarrow>  is_instr (nat_to_instr_I_mem (intwd_as_nat i mod 67108864 div 2097152)
                                     (intwd_as_nat i mod 2097152 div 65536)
                                     (nat_to_imm16 (intwd_as_nat i mod 65536))
                                     (intwd_as_nat i div 67108864))"
  using less_32 asm_imm16
    apply (simp add: nat_to_instr_I_mem_def)
    apply (case_tac "32 \<le> intwd_as_nat i div 67108864 \<and>
                     intwd_as_nat i div 67108864 \<le> 33", simp add: is_instr_def)
    apply (case_tac "35 \<le> intwd_as_nat i div 67108864 \<and>
                     intwd_as_nat i div 67108864 \<le> 37", simp add: is_instr_def)
    apply (case_tac "40 \<le> intwd_as_nat i div 67108864 \<and>
                     intwd_as_nat i div 67108864 \<le> 41", simp add: is_instr_def)
  by (case_tac "intwd_as_nat i div 67108864 = 43", simp_all add: is_instr_def)

  have is_instr_I_comp:
  "\<lbrakk>22 \<le> intwd_as_nat i div 67108864; intwd_as_nat i div 67108864 \<le> 33;
    \<not> 32 \<le> intwd_as_nat i div 67108864; 24 \<le> intwd_as_nat i div 67108864 \<rbrakk>
    \<Longrightarrow> is_instr (nat_to_instr_I_comp (intwd_as_nat i mod 67108864 div 2097152)
                                      (intwd_as_nat i mod 2097152 div 65536)
                                      (nat_to_imm16 (intwd_as_nat i mod 65536))
                                      (intwd_as_nat i div 67108864))"
  using less_32 asm_imm16
    apply (simp add: nat_to_instr_I_comp_def)
    apply (intro conjI impI)
    prefer 8
  by (simp add: is_instr_def less_32)+

  have is_instr_I_al: 
  "\<lbrakk>8 \<le> intwd_as_nat i div 67108864; intwd_as_nat i div 67108864 \<le> 15\<rbrakk>
    \<Longrightarrow> is_instr (nat_to_instr_I_al (intwd_as_nat i mod 67108864 div 2097152)
                                    (intwd_as_nat i mod 2097152 div 65536)
                                    (nat_to_imm16 (intwd_as_nat i mod 65536))
                                    (intwd_as_nat i div 67108864))"
    apply (simp add: nat_to_instr_I_al_def)
    apply (intro conjI impI)
    prefer 8
  by (simp add: is_instr_def less_32 asm_imm16)+

  have is_instr_R_shift:
  "\<lbrakk>intwd_as_nat i mod 64 \<le> 7; intwd_as_nat i div 67108864 = 0\<rbrakk>
    \<Longrightarrow> is_instr (nat_to_instr_R_shift (intwd_as_nat i div 2097152)
                                       (intwd_as_nat i mod 2097152 div 65536)
                                       (intwd_as_nat i mod 65536 div 2048)
                                       (intwd_as_nat i mod 2048 div 64)
                                       (intwd_as_nat i mod 64))"
  using less_32 R_less_32 asm_sa
    apply (simp add: nat_to_instr_R_shift_def)
    apply (intro conjI impI)
  by (simp add: is_instr_def)+

  have is_instr_R_comp:
  "\<lbrakk>intwd_as_nat i div 67108864 = 0; 32 \<le> intwd_as_nat i mod 64;
    intwd_as_nat i mod 64 \<le> 47; 40 \<le> intwd_as_nat i mod 64 \<rbrakk>
    \<Longrightarrow> is_instr (nat_to_instr_R_comp (intwd_as_nat i div 2097152)
                                      (intwd_as_nat i mod 2097152 div 65536)
                                      (intwd_as_nat i mod 65536 div 2048)
                                      (intwd_as_nat i mod 64))"
    apply (simp add: nat_to_instr_R_comp_def)
    apply (intro conjI impI)
    prefer 8
  apply (simp add: is_instr_def less_32 R_less_32)+ 
  prefer 2 
  apply (simp add: is_instr_def less_32 R_less_32) 
 sorry

  have is_instr_I_jump:
  "\<lbrakk>22 \<le> intwd_as_nat i div 67108864 \<and> intwd_as_nat i div 67108864 \<le> 23 \<or>
     2 \<le> intwd_as_nat i div 67108864 \<and> intwd_as_nat i div 67108864 \<le> 5 \<rbrakk>
   \<Longrightarrow> is_instr (nat_to_instr_I_jump (intwd_as_nat i mod 67108864 div 2097152)
                                     (nat_to_imm16 (intwd_as_nat i mod 65536))
                                     (nat_to_imm26 (intwd_as_nat i mod 67108864))
                                     (intwd_as_nat i div 67108864))"
  using less_32 asm_imm16 asm_imm26
    apply (simp add: nat_to_instr_I_jump_def)
    apply (cases" 2 \<le> intwd_as_nat i div 67108864 \<and>
                  intwd_as_nat i div 67108864 \<le> 5", simp add: is_instr_def)
  by (cases "22 \<le> intwd_as_nat i div 67108864 \<and>
             intwd_as_nat i div 67108864 \<le> 23", simp_all add: is_instr_def)

  show ?thesis using assms
    apply (simp add: decodable_instr_int_def decodable_instr_nat_def)
    apply (simp add: instr_to_int_def int_to_instr_def natwd2intwd2natwd)
    apply (cases "is_I_opcode (intwd_as_nat i div 67108864)")
    apply simp_all
    apply (simp add: is_I_opcode_def nat_to_instr_I_def)
    apply (simp add: nat_to_instr_def nat_to_instr_I_def Let_def)
      apply (cases "2 \<le> intwd_as_nat i div 67108864 \<and>
                    intwd_as_nat i div 67108864 \<le> 5", simp add: is_instr_I_jump)
      apply (cases "8 \<le> intwd_as_nat i div 67108864 \<and> 
                    intwd_as_nat i div 67108864 \<le> 15", simp add: is_instr_I_al)
      apply  (cases "22 \<le> intwd_as_nat i div 67108864 \<and>
                     intwd_as_nat i div 67108864 \<le> 33",
              simp add: is_instr_I_mem is_instr_I_jump is_instr_I_comp)
      apply (cases "35 \<le> intwd_as_nat i div 67108864 \<and>
                    intwd_as_nat i div 67108864 \<le> 37",simp add: is_instr_I_mem)
      apply (cases "40 \<le> intwd_as_nat i div 67108864 \<and>
                    intwd_as_nat i div 67108864 \<le> 41", simp add: is_instr_I_mem)
      apply (cases "intwd_as_nat i div 67108864 = 43", simp) 
      apply (cut_tac is_instr_I_mem, simp+)
      using asm_imm26 apply (simp add: is_instr_def)

      apply (simp add: nat_to_instr_def is_R_opcode_def
                       nat_to_instr_R_def Let_def, clarsimp)
      apply (cases "intwd_as_nat i mod 64 \<le> 7", simp add: is_instr_R_shift)
      apply (cases "16 \<le> intwd_as_nat i  mod 64 \<and> intwd_as_nat i mod 64 \<le> 17",
             simp add: nat_to_instr_R_mov_def is_instr_def less_32 R_less_32)
      apply (cases "32 \<le> intwd_as_nat i mod 64 \<and> intwd_as_nat i mod 64 \<le> 47",
             simp add: is_instr_R_comp)
      apply (clarsimp, simp add: nat_to_instr_R_al_def)
      apply (intro conjI impI)
      prefer 8
  by (simp add: is_instr_def less_32 R_less_32)+
qed

end
