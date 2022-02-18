(**
 * Copyright (c) 2004-2007 Thomas In der Rieden, Dirk Leinenbach,
 * Mareike Schmidt, Alexandra Tsyban.
 * Some rights reserved, Saarland University.
 *
 * This work is licensed under the German-Jurisdiction Creative Commons
 * Attribution Non-commercial Share Alike 2.0 License.
 * See the file LIZENZ for a full copy of the license.
**)
(* $Id: Config.thy 27377 2009-04-30 00:02:35Z MatthiasDaum $ *)
chapter {* Configurations Definitions *}

theory Config imports Memory begin

subsection {* Assembler Core *}

text
{* The configuration of the assembler core for both 
   machines: physical and virtual. The virtual machine 
   is actual a assembler core.
*}

record ASMcore_t =
  dpc   :: nat
  pcp   :: nat
  gprs  :: registers
  sprs  :: registers
  mm   :: mem_t

lemma ASMcore_t_truncate[simp]:
  "ASMcore_t.truncate (asm::ASMcore_t) = asm"
and ASMcore_t_extend[simp]:
  "ASMcore_t.extend (asm::ASMcore_t) x = asm"
and ASMcore_t_truncate_extend[simp]:
  "ASMcore_t.truncate (ASMcore_t.extend asm y) = asm"
  by (simp_all add: ASMcore_t.defs)

definition reg :: "[registers, nat] \<Rightarrow> regcont"
where 
"reg xs n \<equiv> if n = 0 then 0 else xs ! n"

lemma [simp]: "reg xs 0 = 0"
by (simp add: reg_def)

lemma [simp]: "n \<noteq> 0 \<Longrightarrow> reg xs n = xs ! n"
by (simp add: reg_def)

lemma DISTINCT_upd_reg[rule_format]: "DISTINCT xs \<longrightarrow> x \<in> set xs \<longrightarrow> y \<in> set (remove1 x xs) \<longrightarrow> reg (g [ y := z ]) x = reg g x "
apply clarsimp
apply (simp add: DISTINCT_def)
apply clarsimp
apply (simp add: reg_def)
done

lemmas DISTINCT_upds = DISTINCT_upd DISTINCT_upd_reg

text {* access to sprs *}

  -- "named registers of SPRS"

definition SPR_SR :: regname
where  "SPR_SR == 0"

definition  SPR_ESR :: regname
where  "SPR_ESR == 1"
 
definition  SPR_ECA :: regname
 where  "SPR_ECA == 2"

definition  SPR_EPC :: regname
where  "SPR_EPC == 3"

definition  SPR_EDPC :: regname
 where  "SPR_EDPC == 4"

definition  SPR_EData :: regname
 where  "SPR_EData == 5"

definition  SPR_RM :: regname
 where "SPR_RM == 6"

definition  SPR_IEEEF :: regname
 where "SPR_IEEEF == 7"

 definition SPR_FCC :: regname
 where "SPR_FCC == 8"

 definition  SPR_PTO :: regname
 where "SPR_PTO == 9"

 definition SPR_PTL :: regname
 where "SPR_PTL == 10"

  definition SPR_EMODE :: regname
  where "SPR_EMODE == 11"
 
definition SPR_MODE :: regname
  where "SPR_MODE == 16"

definition used_sprs :: "regname set"
where
  "used_sprs \<equiv> {SPR_SR, SPR_ESR, SPR_ECA, SPR_EPC, SPR_EDPC, SPR_EData, SPR_RM,
                SPR_IEEEF, SPR_FCC, SPR_PTO, SPR_PTL, SPR_EMODE, SPR_MODE}"

definition sreg :: "[registers, regname] \<Rightarrow> regcont"
where
  "sreg xs n \<equiv> if n \<in> used_sprs then xs ! n else 0"

definition pages_used :: "ASMcore_t \<Rightarrow> nat"
where
"pages_used up \<equiv> intwd_as_nat (sprs up ! SPR_PTL + 1)"

lemma [simp]: "sreg xs SPR_SR = xs ! SPR_SR"
by (simp add: sreg_def used_sprs_def)

lemma [simp]: "sreg xs SPR_ESR = xs ! SPR_ESR"
by (simp add: sreg_def used_sprs_def)

lemma [simp]: "sreg xs SPR_ECA = xs ! SPR_ECA"
by (simp add: sreg_def used_sprs_def)

lemma [simp]: "sreg xs SPR_EPC = xs ! SPR_EPC"
by (simp add: sreg_def used_sprs_def)

lemma [simp]: "sreg xs SPR_EDPC = xs ! SPR_EDPC"
by (simp add: sreg_def used_sprs_def)

lemma [simp]: "sreg xs SPR_EData = xs ! SPR_EData"
by (simp add: sreg_def used_sprs_def)

lemma [simp]: "sreg xs SPR_RM = xs ! SPR_RM"
by (simp add: sreg_def used_sprs_def)

lemma [simp]: "sreg xs SPR_IEEEF = xs ! SPR_IEEEF"
by (simp add: sreg_def used_sprs_def)

lemma [simp]: "sreg xs SPR_FCC = xs ! SPR_FCC"
by (simp add: sreg_def used_sprs_def)

lemma [simp]: "sreg xs SPR_PTO = xs ! SPR_PTO"
by (simp add: sreg_def used_sprs_def)

lemma [simp]: "sreg xs SPR_PTL = xs ! SPR_PTL"
by (simp add: sreg_def used_sprs_def)

lemma [simp]: "sreg xs SPR_EMODE = xs ! SPR_EMODE"
by (simp add: sreg_def used_sprs_def)

lemma [simp]: "sreg xs SPR_MODE = xs ! SPR_MODE"
by (simp add: sreg_def used_sprs_def)

definition is_ASMcore :: "ASMcore_t \<Rightarrow> bool"
where
  "is_ASMcore st == asm_nat (dpc st) \<and>
                    asm_nat (pcp st) \<and>
                    length (gprs st) = 32 \<and> 
                    length (sprs st) = 32 \<and> 
                    (\<forall> ind < 32. asm_int (reg (gprs st)  ind)) \<and>
                    (\<forall> ind < 32. asm_int (sreg (sprs st) ind)) \<and>
                    (\<forall> ad. asm_int (data_mem_read (mm st) ad))"

  -- "sacred registers (from GPRS)"

definition GPR_ret :: regname
where
  "GPR_ret == 31"

definition GPR_heap :: regname
 where "GPR_heap == 30"

definition GPR_funframe :: regname
where
"GPR_funframe == 29"

definition GPR_glvar :: regname
where
"GPR_glvar == 28"

lemma data_mem_read_asm_int[rule_format]: "is_ASMcore d \<longrightarrow> asm_int (data_mem_read (mm d) i)"
apply clarsimp
apply (simp add: is_ASMcore_def)
done


definition  current_instr :: "ASMcore_t \<Rightarrow> instr"
where      "current_instr d \<equiv> instr_mem_read (mm d) (dpc d)"



subsection {* Physical machine *}

text {*  The physical machine consists of assembler core and swap memory. *}

record PhysMach_t =  ASMcore  :: ASMcore_t
                     swap     :: mem_t


definition  is_PhysMach :: "PhysMach_t \<Rightarrow> bool"
where      "is_PhysMach st == is_ASMcore (ASMcore st) \<and> (\<forall> ad. asm_int (cell2data ((swap st) ad)))"
end
