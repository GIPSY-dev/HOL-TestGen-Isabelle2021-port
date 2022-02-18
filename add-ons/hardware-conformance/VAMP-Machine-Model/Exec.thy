(**
 * Copyright (c) 2004-2009 Matthias Daum, Dirk Leinenbach,
 * Thomas In der Rieden, Mareike Schmidt, Alexandra Tsyban.
 * Some rights reserved, Saarland University.
 *
 * This work is licensed under the German-Jurisdiction Creative Commons
 * Attribution Non-commercial Share Alike 2.0 License.
 * See the file LIZENZ for a full copy of the license.
**)
(* $Id: Exec.thy 29816 2009-11-24 12:55:59Z DirkLeinenbach $ *)
chapter {* Instruction Execution *}
theory Exec imports Config begin

subsection {* Auxiliary definitions *}

definition inc_pcp_by :: "[nat, int] \<Rightarrow> nat" -- "increment program counter by a certain amount"
where
 "inc_pcp_by PC inc == fit_nat (PC + intwd_as_nat inc)"

definition inc_pcs_st :: "ASMcore_t \<Rightarrow> ASMcore_t"
where
  "inc_pcs_st st == st \<lparr> dpc := pcp st,
                         pcp := inc_pcp_by (pcp st) (int wlen_byte) \<rparr>"

lemma is_ASMcore_after_inc_pcs_st:
  "is_ASMcore asm \<Longrightarrow> is_ASMcore (inc_pcs_st asm)"
  by (simp add: inc_pcs_st_def is_ASMcore_def inc_pcp_by_def asm_nat_fit_nat)

lemma inc_pcs_st_simps[simp]:
"dpc (inc_pcs_st asm) =  pcp asm"
"gprs (inc_pcs_st asm) = gprs asm"
"sprs (inc_pcs_st asm) = sprs asm"
"mm (inc_pcs_st asm) = mm asm"
  by (auto simp add: inc_pcs_st_def)


text {* Like @{text inc_pc_by} but without range check *}

definition  add_pc :: "nat \<Rightarrow> int \<Rightarrow> nat"
where
   "add_pc pc i \<equiv> nat (int pc + i)"

definition load_from_mem :: "[mem_t, nat, nat, nat, bv \<Rightarrow> bv] \<Rightarrow> int"
where
  "load_from_mem memory ad off d extf == let new_nat = ((intwd_as_nat (data_mem_read memory ad)) div 2^(8 * off)) mod 2^(8 * d)
                                         in if extf = fill0_wd then int new_nat
                                            else bv_to_int (extf (bv_extend (8 * d) 0 (nat_to_bv new_nat)))"											

definition load_from_mem' :: "[mem_t, nat, nat, nat] \<Rightarrow> int"
where
  "load_from_mem' memory ad off d  == let new_nat = ((intwd_as_nat (data_mem_read memory ad)) div 2^(8 * off)) mod 2^(8 * d)
                                         in int new_nat"
                                            																						
definition load_from_mem'' :: "[mem_t, nat, nat, nat] \<Rightarrow> int"
where
  "load_from_mem'' memory ad off d == let new_nat = ((intwd_as_nat (data_mem_read memory ad)) div 2^(8 * off)) mod 2^(8 * d)
                                         in bv_to_int (sxt_wd (bv_extend (8 * d) 0 (nat_to_bv new_nat)))"


lemma load_trans' [code_unfold, simp]: 
"load_from_mem memory ad off d fill0_wd = load_from_mem' memory ad off d"
by (simp add: load_from_mem'_def load_from_mem_def)

lemma temp_lemm [code_unfold, simp]: "sxt_wd \<noteq> fill0_wd"
apply (simp add: sxt_wd_def fill0_wd_def fun_eq_iff bv_msb_def)
apply (rule_tac x="[1]" in exI, clarsimp simp add: bv_extend_def wlen_bit_def)
done

lemma load_trans'' [code_unfold, simp]: 
"load_from_mem memory ad off d sxt_wd = load_from_mem'' memory ad off d"
by (simp add: load_from_mem''_def load_from_mem_def temp_lemm)
									 							
definition store_to_mem :: "[mem_t, nat, nat, nat, int] \<Rightarrow> mem_t"
 where "store_to_mem memory ad off d i == let owi = intwd_as_nat (data_mem_read memory ad);
                                         wi  = intwd_as_nat i;
                                         hwi = (owi div 2^(8 * (off + d))) * 2^(8 * (off + d));
                                         lwi = owi mod 2^(8 * off);
                                         mwi = (wi mod 2^(8 * d)) * 2^(8 * off);
                                         ni  = natwd_as_int ((hwi + mwi + lwi) mod 2 ^ wlen_bit)
                                     in data_mem_write memory ad ni"

lemma sxt_wd_neq_fill0_wd[simp]: "sxt_wd \<noteq> fill0_wd"
apply (rule ccontr)
apply simp
apply (insert eval_nat_numeral)
done

lemma fill0_wd_norm_unsigned[rule_format]: "length x \<le> 32 \<longrightarrow> fill0_wd (norm_unsigned x) = fill0_wd x"
apply (induct x)
 apply simp
apply (intro impI)
apply (drule mp, simp)
apply (case_tac a, simp_all)
apply (simp add: fill0_wd_def)
apply (simp add: wlen_bit_def bv_extend_def)
apply (subgoal_tac "[0] = replicate 1 0")
 prefer 2
 apply simp
apply (rotate_tac -1, erule ssubst)
apply (subst replicate_add[THEN sym])
apply (subgoal_tac "32 - length x = 31 - length x + 1")
 prefer 2
 apply arith
apply (rotate_tac -1, erule ssubst)
apply (rule refl)
done

lemma fill0_wd_sxt_wd: "fill0_wd (sxt_wd x) = sxt_wd x"
apply (simp add: fill0_wd_def)
apply (simp add: bv_extend_def)
apply (subgoal_tac "wlen_bit \<le> length (sxt_wd x)")
 apply simp
apply (simp add: sxt_wd_def)
apply (simp add: bv_extend_def)
done

lemma sxt_wd_sxt_wd: "sxt_wd (sxt_wd x) = sxt_wd x"
apply (simp add: sxt_wd_def)
apply (simp add: bv_extend_def)
done

lemma correct_load_from_mem_word: 
      "is_ASMcore d \<Longrightarrow> load_from_mem (mm d) x 0 4 sxt_wd = data_mem_read (mm d) x"
apply (clarsimp simp add: load_from_mem_def is_ASMcore_def)
apply (fold wlen_bit_def)
apply (fold fill0_wd_def)
apply (unfold wlen_bit_def)
apply (rotate_tac -1)
apply (erule_tac x = "x" in allE)
apply (frule asm_nat_intwd_as_nat)
apply (rotate_tac -1, drule mod_wlen_bit_is_same)
apply (simp add: wlen_bit_def)
apply (subst intwd_as_nat_meaning, assumption)
apply simp
apply (subst fill0_wd_norm_unsigned)
 apply (drule asm_int_impl_length_int_to_bv)
 apply (simp add: wlen_bit_def sxt_wd_def bv_msb_def bv_extend_def)
apply (subst fill0_wd_sxt_wd)
apply (subst sxt_wd_sxt_wd)
apply (rule bv_to_int_sxt_wd_int_to_bv)
done

lemma valid_store_to_mem:
assumes "asm_int (data_mem_read memory x)"
    and "asm_int i"
  shows "store_to_mem memory x 0 4 i = memory (x div 4 := data2cell i)"
using assms
  apply (clarsimp simp add: store_to_mem_def is_ASMcore_def data_mem_write_def)
  apply (drule asm_nat_intwd_as_nat)
  apply (rotate_tac -1, drule div_wlen_bit_is_zero)
  apply (frule asm_nat_intwd_as_nat)
  apply (rotate_tac -1, drule mod_wlen_bit_is_same)
  apply (simp add: wlen_bit_def)
  apply (drule intwd2natwd2intwd, simp)
  done
  
lemma correct_store_to_mem_word_imm:
      "\<lbrakk> is_ASMcore d; asm_int i \<rbrakk> \<Longrightarrow>
      store_to_mem (mm d) x 0 4 i = (mm d) (x div 4 := data2cell i)"
by (clarsimp simp add: is_ASMcore_def valid_store_to_mem)

lemma correct_store_to_mem_word: "\<lbrakk>is_ASMcore d; 0 < y \<and> y < 32\<rbrakk> \<Longrightarrow> store_to_mem (mm d) x 0 4 (gprs d ! y) = (mm d) (x div 4 := data2cell (gprs d ! y))"
apply (rule correct_store_to_mem_word_imm)
 apply assumption
apply (clarsimp simp add: is_ASMcore_def)
apply (erule_tac x = "y" in allE)
apply simp
done

lemma correct_store_to_mem_word2: "\<lbrakk>is_ASMcore d; y < 32\<rbrakk> \<Longrightarrow> store_to_mem (mm d) x 0 4 (reg (gprs d) y) = (mm d) (x div 4 := data2cell (reg (gprs d) y))"
apply (rule correct_store_to_mem_word_imm, simp)
apply (clarsimp simp add: is_ASMcore_def)
done

definition int_add :: "[int, int] \<Rightarrow> int"
where
  "int_add i1 i2 == natwd_as_int (fit_nat (intwd_as_nat i1 + intwd_as_nat i2))"

definition int_sub :: "[int, int] \<Rightarrow> int"
where
  "int_sub i1 i2 == natwd_as_int (fit_nat (2 ^ wlen_bit + intwd_as_nat i1 - intwd_as_nat i2))"

definition const_load :: "[int, int] \<Rightarrow> int"
where
"const_load a b == natwd_as_int (((intwd_as_nat b) mod 2^16) * 2^16)"

definition const_load_imm :: "[int, int] \<Rightarrow> int"
where
"const_load_imm a b == b * 2^16"

definition is_system_mode :: "ASMcore_t \<Rightarrow> bool"
where
  "is_system_mode a \<equiv> (sprs a) ! SPR_MODE = 0"

subsection {* Execution of individual instructions *}

definition arith_exec :: "[ASMcore_t, [int, int] \<Rightarrow> int, int, int, regname] \<Rightarrow> ASMcore_t"
where
  "arith_exec st arithf opd1 opd2 dest == (inc_pcs_st st) \<lparr> gprs := (gprs st) [dest := arithf opd1 opd2] \<rparr>"

definition comp_exec :: "[ASMcore_t, [int, int] \<Rightarrow> bool, int, int, regname] \<Rightarrow> ASMcore_t"
where
  "comp_exec st compf opd1 opd2 dest == (inc_pcs_st st) \<lparr> gprs := (gprs st) [dest := if (compf opd1 opd2) then 1 else 0]  \<rparr>"

definition load_exec :: "[ASMcore_t, bv \<Rightarrow> bv, int, int, nat, regname] \<Rightarrow> ASMcore_t"
where
  "load_exec st extf adr adi d dest == let ad = fit_nat (intwd_as_nat adr + intwd_as_nat adi)
                                       in (inc_pcs_st st) \<lparr> gprs := (gprs st) [dest := load_from_mem (mm st) ad (ad mod 4) d extf] \<rparr>"

definition load_exec' :: "[ASMcore_t, int, int, nat, regname] \<Rightarrow> ASMcore_t"
where
  "load_exec' st adr adi d dest == let ad = fit_nat (intwd_as_nat adr + intwd_as_nat adi)
                                       in (inc_pcs_st st) \<lparr> gprs := (gprs st) [dest := load_from_mem' (mm st) ad (ad mod 4) d] \<rparr>"


definition load_exec'' :: "[ASMcore_t, int, int, nat, regname] \<Rightarrow> ASMcore_t"
where
  "load_exec'' st adr adi d dest == let ad = fit_nat (intwd_as_nat adr + intwd_as_nat adi)
                                       in (inc_pcs_st st) \<lparr> gprs := (gprs st) [dest := load_from_mem'' (mm st) ad (ad mod 4) d] \<rparr>"

lemma load_exec_trans' [code_unfold, simp]: 
"load_exec st fill0_wd adr adi d dest  = load_exec' st adr adi d dest"
by (simp add: load_exec'_def load_exec_def)

lemma load_exec_trans'' [code_unfold, simp]: 
"load_exec st sxt_wd adr adi d dest  = load_exec'' st adr adi d dest"
by (simp add: load_exec''_def load_exec_def)

definition store_exec :: "[ASMcore_t, int, int, nat, regname] \<Rightarrow> ASMcore_t"
where
  "store_exec st adr adi d sour == let ad = fit_nat (intwd_as_nat adr + intwd_as_nat adi)
                                   in (inc_pcs_st st) \<lparr> mm := store_to_mem (mm st) ad (ad mod 4) d (reg (gprs st) sour) \<rparr>"

fun exec_instr :: "[ASMcore_t, instr] \<Rightarrow> ASMcore_t"

where
  -- "Arithmetic Instructions"
  "exec_instr st (Iaddo RD RS1 RS2) = arith_exec st int_add (reg (gprs st) RS1) (reg (gprs st) RS2) RD"
  |"exec_instr st (Isubo RD RS1 RS2) = arith_exec st int_sub (reg (gprs st) RS1) (reg (gprs st) RS2) RD"
 | "exec_instr st (Iadd RD RS1 RS2) = arith_exec st int_add (reg (gprs st) RS1) (reg (gprs st) RS2) RD"
 | "exec_instr st (Isub RD RS1 RS2) = arith_exec st int_sub (reg (gprs st) RS1) (reg (gprs st) RS2) RD"
 | "exec_instr st (Iaddio RD rs imm) = arith_exec st int_add (reg (gprs st) rs) imm RD"
 | "exec_instr st (Isubio RD rs imm) = arith_exec st int_sub (reg (gprs st) rs) imm RD"
 | "exec_instr st (Iaddi RD rs imm) = arith_exec st int_add (reg (gprs st) rs) imm RD"
 | "exec_instr st (Isubi RD rs imm) = arith_exec st int_sub (reg (gprs st) rs) imm RD"

  -- "Logical Instructions"
 | "exec_instr st (Iand RD RS1 RS2) = arith_exec st s_and (reg (gprs st) RS1) (reg (gprs st) RS2) RD"
 | "exec_instr st (Ior RD RS1 RS2)  = arith_exec st s_or  (reg (gprs st) RS1) (reg (gprs st) RS2) RD"
 | "exec_instr st (Ixor RD RS1 RS2) = arith_exec st s_xor (reg (gprs st) RS1) (reg (gprs st) RS2) RD"
 | "exec_instr st (Iandi RD rs imm) = arith_exec st s_and (reg (gprs st) rs) imm RD"
 | "exec_instr st (Iori RD rs imm)  = arith_exec st s_or  (reg (gprs st) rs) imm RD"
 | "exec_instr st (Ixori RD rs imm) = arith_exec st s_xor (reg (gprs st) rs) imm RD"

  -- "Shift Instructions"
 | "exec_instr st (Isll RD RS1 RS2) = arith_exec st sllog (reg (gprs st) RS1) (reg (gprs st) RS2) RD"
 | "exec_instr st (Isrl RD RS1 RS2) = arith_exec st srlog (reg (gprs st) RS1) (reg (gprs st) RS2) RD"
 | "exec_instr st (Isra RD RS1 RS2) = arith_exec st srath (reg (gprs st) RS1) (reg (gprs st) RS2) RD"
 | "exec_instr st (Islli RD rs sh_am) = arith_exec st sllog (reg (gprs st) rs) (int sh_am) RD"
 | "exec_instr st (Isrli RD rs sh_am) = arith_exec st srlog (reg (gprs st) rs) (int sh_am) RD"
 | "exec_instr st (Israi RD rs sh_am) = arith_exec st srath (reg (gprs st) rs) (int sh_am) RD"

  -- "Constant Load"
 | "exec_instr st (Ilhg RD rs) = arith_exec st const_load 0 (reg (gprs st) rs) RD"
 | "exec_instr st (Ilhgi RD imm) = arith_exec st const_load_imm 0 imm RD"

  -- "Set Instructions"
 | "exec_instr st (Iclr RD) = comp_exec st (\<lambda> a b. False) 0 0  RD"
 | "exec_instr st (Isgr RD RS1 RS2) = comp_exec st (op <) (reg (gprs st) RS2) (reg (gprs st) RS1) RD"
 | "exec_instr st (Iseq RD RS1 RS2) = comp_exec st (op =) (reg (gprs st) RS1) (reg (gprs st) RS2) RD"
 | "exec_instr st (Isge RD RS1 RS2) = comp_exec st (op \<le>) (reg (gprs st) RS2) (reg (gprs st) RS1) RD"
 | "exec_instr st (Isls RD RS1 RS2) = comp_exec st (op <) (reg (gprs st) RS1) (reg (gprs st) RS2) RD"
 | "exec_instr st (Isne RD RS1 RS2) = comp_exec st (\<lambda> a b. a \<noteq> b) (reg (gprs st) RS1) (reg (gprs st) RS2) RD"
 | "exec_instr st (Isle RD RS1 RS2) = comp_exec st (op \<le>) (reg (gprs st) RS1) (reg (gprs st) RS2) RD"
 | "exec_instr st (Iset RD) = comp_exec st (\<lambda> a b. True) 0 0  RD"

 | "exec_instr st (Iclri RD ) = comp_exec st (\<lambda> a b. False)  0  0 RD"
 | "exec_instr st (Isgri RD rs imm) = comp_exec st (op <) imm (reg (gprs st) rs) RD"
 | "exec_instr st (Iseqi RD rs imm) = comp_exec st (op =) (reg (gprs st) rs) imm RD"
 | "exec_instr st (Isgei RD rs imm) = comp_exec st (op \<le>) imm (reg (gprs st) rs) RD"
 | "exec_instr st (Islsi RD rs imm) = comp_exec st (op <) (reg (gprs st) rs) imm RD"
 | "exec_instr st (Isnei RD rs imm) = comp_exec st (\<lambda> a b. a \<noteq> b) (reg (gprs st) rs) imm RD"
 | "exec_instr st (Islei RD rs imm) = comp_exec st (op \<le>) (reg (gprs st) rs) imm RD"
 | "exec_instr st (Iseti RD) = comp_exec st (\<lambda> a b. True) 0 0  RD"

  -- "Load Instructions"
 | "exec_instr st (Ilb RD rs imm) = load_exec st sxt_wd (reg (gprs st) rs) imm 1 RD"
 | "exec_instr st (Ilh RD rs imm) = load_exec st sxt_wd (reg (gprs st) rs) imm 2 RD"
 | "exec_instr st (Ilw RD rs imm) = load_exec st sxt_wd (reg (gprs st) rs) imm 4 RD"
 | "exec_instr st (Ilbu RD rs imm) = load_exec st fill0_wd (reg (gprs st) rs) imm 1 RD"
 | "exec_instr st (Ilhu RD rs imm) = load_exec st fill0_wd (reg (gprs st) rs) imm 2 RD"
 
  -- "Store Instructions"
 | "exec_instr st (Isb RD rs imm) = store_exec st (reg (gprs st) rs) imm 1 RD"
 | "exec_instr st (Ish RD rs imm) = store_exec st (reg (gprs st) rs) imm 2 RD"
 | "exec_instr st (Isw RD rs imm) = store_exec st (reg (gprs st) rs) imm 4 RD"

  -- "Special Instructions"
  |"exec_instr st (Imovs2i RD SA) = (if \<not> is_system_mode st \<and> SA \<notin> {SPR_RM, SPR_IEEEF, SPR_FCC}
                                    then st
                                    else (inc_pcs_st st) \<lparr> gprs := (gprs st) [RD := sreg (sprs st) SA] \<rparr>)"
 | "exec_instr st (Imovi2s SA rs) = (if \<not> is_system_mode st \<and> SA \<notin> {SPR_RM, SPR_IEEEF, SPR_FCC}
                                    then st
                                    else (inc_pcs_st st) \<lparr> sprs := (sprs st) [SA := reg (gprs st) rs] \<rparr>)"

  -- "Rfe Instruction"
 | "exec_instr st Irfe = st"

  -- "Placeholder for uninterpreted trap instruction"
 | "exec_instr st (Itrap imm) = inc_pcs_st st"

  -- "Jump and Branch Instructions"

 | "exec_instr st (Ij imm) = st \<lparr> dpc := pcp st, pcp := inc_pcp_by (pcp st) imm \<rparr>"
 | "exec_instr st (Ijr rs) = st \<lparr> dpc := pcp st, pcp := intwd_as_nat (reg (gprs st) rs) \<rparr>"
 | "exec_instr st (Ijal imm) = st \<lparr> dpc := pcp st, pcp := inc_pcp_by (pcp st) imm, gprs := (gprs st) [GPR_ret := natwd_as_int (inc_pcp_by (pcp st) 4)] \<rparr>"
 | "exec_instr st (Ijalr rs) = st \<lparr> dpc := pcp st, pcp := intwd_as_nat (reg (gprs st) rs), gprs := (gprs st) [GPR_ret := natwd_as_int (inc_pcp_by (pcp st) 4)] \<rparr>"
 | "exec_instr st (Ibeqz rs imm) = (if reg (gprs st) rs = 0 
                                   then st \<lparr> dpc := pcp st, pcp := inc_pcp_by (pcp st) imm \<rparr>
                                   else inc_pcs_st st)"
 | "exec_instr st (Ibnez rs imm) = (if reg (gprs st) rs = 0 
                                   then inc_pcs_st st
                                   else st \<lparr> dpc := pcp st, pcp := inc_pcp_by (pcp st) imm \<rparr>)"

lemma nop_correct[simp]: "exec_instr st Inop = inc_pcs_st st"
apply (simp add: Inop_def)
apply (simp add: arith_exec_def inc_pcs_st_def)
apply (cases st)
apply clarsimp
apply (simp add: s_or_0_2)

done

text {* The following predicate indicates that an instruction does not get stuck, i.e. it makes progress.
  *}

primrec advancing_instr :: "[ASMcore_t, instr] \<Rightarrow> bool"
where
  "advancing_instr st (Iaddo RD RS1 RS2) = True"
 | "advancing_instr st (Iadd RD RS1 RS2) = True"
 | "advancing_instr st (Isubo RD RS1 RS2) = True"
 | "advancing_instr st (Isub RD RS1 RS2) = True"
 | "advancing_instr st (Iaddio RD rs imm) = True"
 | "advancing_instr st (Iaddi RD rs imm) = True"
 | "advancing_instr st (Isubio RD rs imm) = True"
 | "advancing_instr st (Isubi RD rs imm) = True"
 | "advancing_instr st (Iand RD RS1 RS2) = True"
 | "advancing_instr st (Ior RD RS1 RS2)  = True"
 | "advancing_instr st (Ixor RD RS1 RS2) = True"
 | "advancing_instr st (Iandi RD rs imm) = True"
 | "advancing_instr st (Iori RD rs imm)  = True"
|"advancing_instr st (Ixori RD rs imm) = True"
 | "advancing_instr st (Isll RD RS1 RS2) = True"
 | "advancing_instr st (Isrl RD RS1 RS2) = True"
 | "advancing_instr st (Isra RD RS1 RS2) = True"
 | "advancing_instr st (Islli RD rs sh_am) = True"
|"advancing_instr st (Isrli RD rs sh_am) = True"
| "advancing_instr st (Israi RD rs sh_am) = True"

|  "advancing_instr st (Ilhg RD rs) = True"
 | "advancing_instr st (Ilhgi RD imm) = True"
 | "advancing_instr st (Iclr RD) = True"
 | "advancing_instr st (Isgr RD RS1 RS2) = True"
 | "advancing_instr st (Iseq RD RS1 RS2) = True"
 | "advancing_instr st (Isge RD RS1 RS2) = True"
|"advancing_instr st (Isls RD RS1 RS2) = True"
|"advancing_instr st (Isne RD RS1 RS2) = True"
|  "advancing_instr st (Isle RD RS1 RS2) = True"
|"advancing_instr st (Iset RD) = True"
|  "advancing_instr st (Iclri RD ) = True"
 | "advancing_instr st (Isgri RD rs imm) = True"
 | "advancing_instr st (Iseqi RD rs imm) = True"
 | "advancing_instr st (Isgei RD rs imm) = True"
 | "advancing_instr st (Islsi RD rs imm) = True"
 | "advancing_instr st (Isnei RD rs imm) = True"
|"advancing_instr st (Islei RD rs imm) = True"
 | "advancing_instr st (Iseti RD) = True"
 | "advancing_instr st (Ilb RD rs imm) = True"
 | "advancing_instr st (Ilh RD rs imm) = True"
 | "advancing_instr st (Ilw RD rs imm) = True"
 | "advancing_instr st (Ilbu RD rs imm) = True"
 | "advancing_instr st (Ilhu RD rs imm) = True"
 | "advancing_instr st (Isb RD rs imm) = True"
 | "advancing_instr st (Ish RD rs imm) = True"
 | "advancing_instr st (Isw RD rs imm) = True"
 | "advancing_instr st (Imovs2i RD SA) = (is_system_mode st \<or> SA \<in> {SPR_RM, SPR_IEEEF, SPR_FCC})"
 | "advancing_instr st (Imovi2s SA rs) = (is_system_mode st \<or> SA \<in> {SPR_RM, SPR_IEEEF, SPR_FCC})"
|"advancing_instr st Irfe = False"
 | "advancing_instr st (Itrap imm) = True"
|"advancing_instr st (Ij imm) = True"
 | "advancing_instr st (Ijr rs) = True"
 | "advancing_instr st (Ijal imm) = True"
 | "advancing_instr st (Ijalr rs) = True"
 | "advancing_instr st (Ibeqz rs imm) = True"
 | "advancing_instr st (Ibnez rs imm) = True"

lemma advancing_instr_dpc_exec_instr:
  "advancing_instr s i \<Longrightarrow> dpc (exec_instr s i) = pcp s"
  by (case_tac i, auto simp add: load_exec_def store_exec_def arith_exec_def
    comp_exec_def Let_def)

lemma non_advancing_instr_stucks:
  "~ advancing_instr s i ==> exec_instr s i = s"
  by (case_tac i) simp_all  


lemma 
  "advancing_instr s (current_instr s) \<equiv>
   \<not> is_Irfe (current_instr s) \<and>
   (\<not> is_Imovi2s (current_instr s) \<and> \<not> is_Imovs2i (current_instr s) \<or>
    is_system_mode s \<or>
    sa_arg (current_instr s) \<in> {SPR_RM, SPR_IEEEF, SPR_FCC})"
by (rule eq_reflection) 
  (case_tac "current_instr s",
   simp_all add: is_Irfe_def  is_Imovi2s_def is_Imovs2i_def)
 
definition
  load_store_target :: "ASMcore_t \<Rightarrow> nat"
where
  "load_store_target d \<equiv> fit_nat (intwd_as_nat (reg (gprs d) (RS1_arg (current_instr d))) + intwd_as_nat (imm_arg (current_instr d)))"

definition devices_border :: nat
where
  "devices_border \<equiv> (2^17 - 1) * 2^15"

definition is_mem_addr :: "nat \<Rightarrow> bool"
where
  "is_mem_addr ad \<equiv> ad < devices_border"

definition is_dev_addr :: "nat \<Rightarrow> bool"
where
  "is_dev_addr ad \<equiv> devices_border \<le> ad"

end
