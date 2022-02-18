(**
 * Copyright (c) 2005-2008 Dirk Leinenbach, Alexandra Tsyban.
 * Some rights reserved, Saarland University.
 *
 * This work is licensed under the German-Jurisdiction Creative Commons
 * Attribution Non-commercial Share Alike 2.0 License.
 * See the file LIZENZ for a full copy of the license.
**)
(* $Id: ASMcore_consis.thy 26531 2009-02-07 10:12:00Z MarkHillebrand $ *)
chapter {* Proof that assembler core never leaves the correct state *}

theory ASMcore_consis imports Step begin

declare Let_def[simp]

lemma ASMcore_consis_ind[rule_format]: 
     "is_ASMcore st \<longrightarrow> is_instr iw \<longrightarrow> is_ASMcore (exec_instr st iw)"
apply (case_tac iw)

--"@{text Ilb}"
apply (clarsimp simp add: load_exec_def inc_pcs_st_def inc_pcp_by_def 
       wlen_byte_def load_from_mem_def is_ASMcore_def asm_nat_fit_nat)
apply (case_tac "ind = 0", simp add: asm_int_zero)
apply (case_tac "ind = x11")
 apply simp
 apply (rule asm_int_bv_to_int)
 apply (rule eq_imp_le)
 apply (rule length_sxt_wd)
 apply (rule length_bv_extend_le_wlen_bit)
  apply (simp add: wlen_bit_def)
 apply (rule length_nat_to_bv_le_wlen_bit)
 apply (rule asm_nat_mod, simp)
 apply (rule asm_nat_div_power)
 apply (rule asm_nat_intwd_as_nat)
 apply simp
apply (erule_tac x = "ind" in allE, simp)

--"@{text Ilh}"
apply (clarsimp simp add: load_exec_def inc_pcs_st_def inc_pcp_by_def wlen_byte_def load_from_mem_def is_ASMcore_def asm_nat_fit_nat)
apply (case_tac "ind = 0", simp add: asm_int_zero)
apply (case_tac "ind = x21")
 apply simp
 apply (rule asm_int_bv_to_int)
 apply (rule eq_imp_le)
 apply (rule length_sxt_wd)
 apply (rule length_bv_extend_le_wlen_bit)
  apply (simp add: wlen_bit_def)
 apply (rule length_nat_to_bv_le_wlen_bit)
 apply (rule asm_nat_mod, simp)
 apply (rule asm_nat_div_power)
 apply (rule asm_nat_intwd_as_nat)
 apply simp
apply (erule_tac x = "ind" in allE, simp)

--"@{text Ilw}"
apply (clarsimp simp add: load_exec_def inc_pcs_st_def inc_pcp_by_def wlen_byte_def load_from_mem_def is_ASMcore_def asm_nat_fit_nat)
apply (case_tac "ind = 0", simp add: asm_int_zero)
apply (case_tac "ind = x31")
 apply simp
 apply (rule asm_int_bv_to_int)
 apply (rule eq_imp_le)
 apply (rule length_sxt_wd)
 apply (rule length_bv_extend_le_wlen_bit)
  apply (simp add: wlen_bit_def)
 apply (rule length_nat_to_bv_le_wlen_bit)
 apply (rule asm_nat_mod, simp)
 apply (rule asm_nat_div_power)
 apply (rule asm_nat_intwd_as_nat)
 apply simp
apply (erule_tac x = "ind" in allE, simp)

--"@{text Ilbu}"
apply (clarsimp simp add: load_exec_def inc_pcs_st_def inc_pcp_by_def wlen_byte_def load_from_mem_def is_ASMcore_def asm_nat_fit_nat)
apply (case_tac "ind = 0", simp add: asm_int_zero)
apply (case_tac "ind = x41")
 apply simp
 apply (rule asm_int_int_mod)
 apply simp
apply (erule_tac x = "ind" in allE, simp)

--"@{text Ilhu}"
apply (clarsimp simp add: load_exec_def inc_pcs_st_def inc_pcp_by_def wlen_byte_def load_from_mem_def is_ASMcore_def asm_nat_fit_nat)
apply (case_tac "ind = 0", simp add: asm_int_zero)
apply (case_tac "ind = x51")
 apply simp
 apply (rule asm_int_int_mod)
 apply simp
apply (erule_tac x = "ind" in allE, simp)

--"@{text Isb}"
apply (clarsimp simp add: store_exec_def inc_pcs_st_def inc_pcp_by_def wlen_byte_def is_ASMcore_def 
                          asm_nat_fit_nat store_to_mem_def data_mem_read_def data_mem_write_def)
apply (simp add: data2cell2data)
apply (rule asm_int_natwd_as_int)
apply (rule asm_nat_mod_wlen_bit)

--"@{text Ish}"
apply (clarsimp simp add: store_exec_def inc_pcs_st_def inc_pcp_by_def wlen_byte_def is_ASMcore_def 
                          asm_nat_fit_nat store_to_mem_def data_mem_read_def data_mem_write_def)
apply (simp add: data2cell2data)
apply (rule asm_int_natwd_as_int)
apply (rule asm_nat_mod_wlen_bit)

--"@{text Isw}"
apply (clarsimp simp add: store_exec_def inc_pcs_st_def inc_pcp_by_def wlen_byte_def is_ASMcore_def 
                          asm_nat_fit_nat store_to_mem_def data_mem_read_def data_mem_write_def)
apply (simp add: data2cell2data)
apply (rule asm_int_natwd_as_int)
apply (rule asm_nat_mod_wlen_bit)

--"@{text Ilhgi}"
apply (clarsimp simp add: arith_exec_def inc_pcs_st_def inc_pcp_by_def wlen_byte_def is_ASMcore_def asm_nat_fit_nat const_load_imm_def)
apply (case_tac "ind = 0", simp add: asm_int_zero)
apply (case_tac "ind = x91")
 apply simp
 apply (simp (no_asm) add: asm_int_def wlen_bit_def)
 apply (clarsimp simp add: is_instr_def asm_imm16_def)
apply (erule_tac x = "ind" in allE, simp)

--"@{text Ilhg}"
apply (clarsimp simp add: arith_exec_def inc_pcs_st_def inc_pcp_by_def wlen_byte_def is_ASMcore_def asm_nat_fit_nat const_load_def)
apply (case_tac "ind = 0", simp add: asm_int_zero)
apply (case_tac "ind = x101")
 apply simp
 apply (rule asm_int_natwd_as_int)
 apply (rule asm_nat_mod_mult_65536)
 apply (rule asm_nat_intwd_as_nat)
 apply (clarsimp simp add: is_instr_def)
apply (erule_tac x = "ind" in allE, simp)

--"@{text Imovs2i}"
apply (intro impI)
apply (simp add: is_ASMcore_def split del: if_split)
apply (rule conjI, clarsimp simp add: inc_pcs_st_def)
apply (rule conjI, clarsimp simp add: inc_pcs_st_def inc_pcp_by_def asm_nat_fit_nat)
apply (rule conjI, clarsimp)
apply (rule conjI, clarsimp)
apply (rule conjI)
 apply (intro allI impI)
 apply (case_tac "ind = 0", simp add: asm_int_zero)
 apply (case_tac "ind = x111")
  apply (clarsimp simp add: is_instr_def)
  apply (erule_tac x = "x111" in allE, simp)
 apply clarsimp
 apply (erule_tac x = "ind" in allE, simp)
apply clarsimp

--"@{text Imovi2s}"
apply (intro impI)
apply (simp add: is_ASMcore_def split del: if_split)
apply (rule conjI, clarsimp simp add: inc_pcs_st_def)
apply (rule conjI, clarsimp simp add: inc_pcs_st_def inc_pcp_by_def asm_nat_fit_nat)
apply (rule conjI, clarsimp)
apply (rule conjI, clarsimp)
apply (rule conjI, clarsimp)
apply (rule conjI)
 apply (intro allI impI)
 apply (case_tac "ind = x121")
  apply (simp add: is_instr_def)
  apply (simp add: sreg_def asm_int_zero)
 apply clarsimp
 apply (erule_tac x = "ind" in allE)+
 apply (clarsimp simp add: sreg_def asm_int_zero)
apply simp

--"@{text Iaddio}"
apply (clarsimp simp add: arith_exec_def inc_pcs_st_def inc_pcp_by_def wlen_byte_def is_ASMcore_def asm_nat_fit_nat int_add_def)
apply (case_tac "ind = 0", simp add: asm_int_zero)
apply (case_tac "ind = x131")
 apply simp
 apply (rule asm_int_natwd_as_int)
 apply (rule asm_nat_fit_nat)
apply (erule_tac x = "ind" in allE, simp)

--"@{text Iaddi}"
apply (clarsimp simp add: arith_exec_def inc_pcs_st_def inc_pcp_by_def wlen_byte_def is_ASMcore_def asm_nat_fit_nat int_add_def)
apply (case_tac "ind = 0", simp add: asm_int_zero)
apply (case_tac "ind = x141")
 apply simp
 apply (rule asm_int_natwd_as_int)
 apply (rule asm_nat_fit_nat)
apply (erule_tac x = "ind" in allE, simp)

--"@{text Isubo}"
apply (clarsimp simp add: arith_exec_def inc_pcs_st_def inc_pcp_by_def wlen_byte_def is_ASMcore_def asm_nat_fit_nat int_sub_def)
apply (case_tac "ind = 0", simp add: asm_int_zero)
apply (case_tac "ind = x151")
 apply simp
 apply (rule asm_int_natwd_as_int)
 apply (rule asm_nat_fit_nat)
apply (erule_tac x = "ind" in allE, simp)

--"@{text Isubi}"
apply (clarsimp simp add: arith_exec_def inc_pcs_st_def inc_pcp_by_def wlen_byte_def is_ASMcore_def asm_nat_fit_nat int_sub_def)
apply (case_tac "ind = 0", simp add: asm_int_zero)
apply (case_tac "ind = x161")
 apply simp
 apply (rule asm_int_natwd_as_int)
 apply (rule asm_nat_fit_nat)
apply (erule_tac x = "ind" in allE, simp)

--"@{text Iandi}"
apply (clarsimp simp add: arith_exec_def inc_pcs_st_def inc_pcp_by_def wlen_byte_def is_ASMcore_def asm_nat_fit_nat)
apply (case_tac "ind = 0", simp add: asm_int_zero)
apply (case_tac "ind = x171")
 apply simp
 apply (rule asm_int_int_and)
  apply (clarsimp simp add: is_instr_def)
 apply (rule asm_imm16_impl_asm_int)
 apply (clarsimp simp add: is_instr_def)
apply (erule_tac x = "ind" in allE, simp)

--"@{text Iori}"
apply (clarsimp simp add: arith_exec_def inc_pcs_st_def inc_pcp_by_def wlen_byte_def is_ASMcore_def asm_nat_fit_nat)
apply (case_tac "ind = 0", simp add: asm_int_zero)
apply (case_tac "ind = x181")
 apply simp
 apply (rule asm_int_int_or)
  apply (clarsimp simp add: is_instr_def)
 apply (rule asm_imm16_impl_asm_int)
 apply (clarsimp simp add: is_instr_def)
apply (erule_tac x = "ind" in allE, simp)

--"@{text Ixori}"
apply (clarsimp simp add: arith_exec_def inc_pcs_st_def inc_pcp_by_def wlen_byte_def is_ASMcore_def asm_nat_fit_nat)
apply (case_tac "ind = 0", simp add: asm_int_zero)
apply (case_tac "ind = x191")
 apply simp
 apply (rule asm_int_int_xor)
  apply (clarsimp simp add: is_instr_def)
 apply (rule asm_imm16_impl_asm_int)
 apply (clarsimp simp add: is_instr_def)
apply (erule_tac x = "ind" in allE, simp)

--"@{text Iaddo}"
apply (clarsimp simp add: arith_exec_def inc_pcs_st_def inc_pcp_by_def wlen_byte_def is_ASMcore_def asm_nat_fit_nat int_add_def)
apply (case_tac "ind = 0", simp add: asm_int_zero)
apply (case_tac "ind = x201")
 apply simp
 apply (rule asm_int_natwd_as_int)
 apply (rule asm_nat_fit_nat)
apply (erule_tac x = "ind" in allE, simp)

--"@{text Iadd}"
apply (clarsimp simp add: arith_exec_def inc_pcs_st_def inc_pcp_by_def wlen_byte_def is_ASMcore_def asm_nat_fit_nat int_add_def)
apply (case_tac "ind = 0", simp add: asm_int_zero)
apply (case_tac "ind = x211")
 apply simp
 apply (rule asm_int_natwd_as_int)
 apply (rule asm_nat_fit_nat)
apply (erule_tac x = "ind" in allE, simp)

--"@{text Isubo}"
apply (clarsimp simp add: arith_exec_def inc_pcs_st_def inc_pcp_by_def wlen_byte_def is_ASMcore_def asm_nat_fit_nat int_sub_def)
apply (case_tac "ind = 0", simp add: asm_int_zero)
apply (case_tac "ind = x221")
 apply simp
 apply (rule asm_int_natwd_as_int)
 apply (rule asm_nat_fit_nat)
apply (erule_tac x = "ind" in allE, simp)

--"@{text Isub}"
apply (clarsimp simp add: arith_exec_def inc_pcs_st_def inc_pcp_by_def wlen_byte_def is_ASMcore_def asm_nat_fit_nat int_sub_def)
apply (case_tac "ind = 0", simp add: asm_int_zero)
apply (case_tac "ind = x231")
 apply simp
 apply (rule asm_int_natwd_as_int)
 apply (rule asm_nat_fit_nat)
apply (erule_tac x = "ind" in allE, simp)

--"@{text Iand}"
apply (clarsimp simp add: arith_exec_def inc_pcs_st_def inc_pcp_by_def wlen_byte_def is_ASMcore_def asm_nat_fit_nat)
apply (case_tac "ind = 0", simp add: asm_int_zero)
apply (case_tac "ind = x241")
 apply simp
 apply (rule asm_int_int_and)
  apply (clarsimp simp add: is_instr_def)
 apply (clarsimp simp add: is_instr_def)
apply (erule_tac x = "ind" in allE, simp)

--"@{text Ior}"
apply (clarsimp simp add: arith_exec_def inc_pcs_st_def inc_pcp_by_def wlen_byte_def is_ASMcore_def asm_nat_fit_nat)
apply (case_tac "ind = 0", simp add: asm_int_zero)
apply (case_tac "ind = x251")
 apply simp
 apply (rule asm_int_int_or)
  apply (clarsimp simp add: is_instr_def)
 apply (clarsimp simp add: is_instr_def)
apply (erule_tac x = "ind" in allE, simp)

--"@{text Ixor}"
apply (clarsimp simp add: arith_exec_def inc_pcs_st_def inc_pcp_by_def wlen_byte_def is_ASMcore_def asm_nat_fit_nat)
apply (case_tac "ind = 0", simp add: asm_int_zero)
apply (case_tac "ind = x261")
 apply simp
 apply (rule asm_int_int_xor)
  apply (clarsimp simp add: is_instr_def)
 apply (clarsimp simp add: is_instr_def)
apply (erule_tac x = "ind" in allE, simp)

--"@{text Iclri}"
apply (clarsimp simp add: comp_exec_def inc_pcs_st_def inc_pcp_by_def wlen_byte_def is_ASMcore_def asm_nat_fit_nat)
apply (case_tac "ind = 0", simp add: asm_int_zero)
apply (case_tac "ind = x27", simp add: asm_int_zero)
apply (erule_tac x = "ind" in allE, simp)

--"@{text Isgri}"
apply (intro impI)
apply (clarsimp simp add: comp_exec_def inc_pcs_st_def inc_pcp_by_def wlen_byte_def is_ASMcore_def asm_nat_fit_nat)
apply (rule conjI)
 apply clarsimp
 apply (case_tac "ind = 0", simp add: asm_int_zero)
 apply (case_tac "ind = x281", simp add: asm_int_one)
 apply (erule_tac x = "ind" in allE, simp)
apply clarsimp
apply (case_tac "ind = 0", simp add: asm_int_zero)
apply (case_tac "ind = x281", simp add: asm_int_zero)
apply (erule_tac x = "ind" in allE, simp)

--"@{text Iseqi}"
apply (intro impI)
apply (clarsimp simp add: comp_exec_def inc_pcs_st_def inc_pcp_by_def wlen_byte_def is_ASMcore_def asm_nat_fit_nat)
apply (rule conjI)
 apply clarsimp
 apply (case_tac "ind = 0", simp add: asm_int_zero)
 apply (case_tac "ind = x291", simp add: asm_int_one)
 apply (erule_tac x = "ind" in allE, simp)
apply clarsimp
apply (case_tac "ind = 0", simp add: asm_int_zero)
apply (case_tac "ind = x291", simp add: asm_int_zero)
apply (erule_tac x = "ind" in allE, simp)

--"@{text Isgei}"
apply (intro impI)
apply (clarsimp simp add: comp_exec_def inc_pcs_st_def inc_pcp_by_def wlen_byte_def is_ASMcore_def asm_nat_fit_nat)
apply (rule conjI)
 apply clarsimp
 apply (case_tac "ind = 0", simp add: asm_int_zero)
 apply (case_tac "ind = x301", simp add: asm_int_one)
 apply (erule_tac x = "ind" in allE, simp)
apply clarsimp
apply (case_tac "ind = 0", simp add: asm_int_zero)
apply (case_tac "ind = x301", simp add: asm_int_zero)
apply (erule_tac x = "ind" in allE, simp)

--"@{text Islsi}"
apply (intro impI)
apply (clarsimp simp add: comp_exec_def inc_pcs_st_def inc_pcp_by_def wlen_byte_def is_ASMcore_def asm_nat_fit_nat)
apply (rule conjI)
 apply clarsimp
 apply (case_tac "ind = 0", simp add: asm_int_zero)
 apply (case_tac "ind = x311", simp add: asm_int_one)
 apply (erule_tac x = "ind" in allE, simp)
apply clarsimp
apply (case_tac "ind = 0", simp add: asm_int_zero)
apply (case_tac "ind = x311", simp add: asm_int_zero)
apply (erule_tac x = "ind" in allE, simp)

--"@{text Isnei}"
apply (intro impI)
apply (clarsimp simp add: comp_exec_def inc_pcs_st_def inc_pcp_by_def wlen_byte_def is_ASMcore_def asm_nat_fit_nat)
apply (rule conjI)
 apply clarsimp
 apply (case_tac "ind = 0", simp add: asm_int_zero)
 apply (case_tac "ind = x321", simp add: asm_int_one)
 apply (erule_tac x = "ind" in allE, simp)
apply clarsimp
apply (case_tac "ind = 0", simp add: asm_int_zero)
apply (case_tac "ind = x321", simp add: asm_int_zero)
apply (erule_tac x = "ind" in allE, simp)

--"@{text Islei}"
apply (intro impI)
apply (clarsimp simp add: comp_exec_def inc_pcs_st_def inc_pcp_by_def wlen_byte_def is_ASMcore_def asm_nat_fit_nat)
apply (rule conjI)
 apply clarsimp
 apply (case_tac "ind = 0", simp add: asm_int_zero)
 apply (case_tac "ind = x331", simp add: asm_int_one)
 apply (erule_tac x = "ind" in allE, simp)
apply clarsimp
apply (case_tac "ind = 0", simp add: asm_int_zero)
apply (case_tac "ind = x331", simp add: asm_int_zero)
apply (erule_tac x = "ind" in allE, simp)

--"@{text Iseti}"
apply (clarsimp simp add: comp_exec_def inc_pcs_st_def inc_pcp_by_def wlen_byte_def is_ASMcore_def asm_nat_fit_nat)
apply (case_tac "ind = 0", simp add: asm_int_zero)
apply (case_tac "ind = x34", simp add: asm_int_one)
apply (erule_tac x = "ind" in allE, simp)

--"@{text Iclr}"
apply (clarsimp simp add: comp_exec_def inc_pcs_st_def inc_pcp_by_def wlen_byte_def is_ASMcore_def asm_nat_fit_nat)
apply (case_tac "ind = 0", simp add: asm_int_zero)
apply (case_tac "ind = x35", simp add: asm_int_zero)
apply (erule_tac x = "ind" in allE, simp)

--"@{text Isgr}"
apply (intro impI)
apply (clarsimp simp add: comp_exec_def inc_pcs_st_def inc_pcp_by_def wlen_byte_def is_ASMcore_def asm_nat_fit_nat)
apply (rule conjI)
 apply clarsimp
 apply (case_tac "ind = 0", simp add: asm_int_zero)
 apply (case_tac "ind = x361", simp add: asm_int_one)
 apply (erule_tac x = "ind" in allE, simp)
apply clarsimp
apply (case_tac "ind = 0", simp add: asm_int_zero)
apply (case_tac "ind = x361", simp add: asm_int_zero)
apply (erule_tac x = "ind" in allE, simp)

--"@{text Iseq}"
apply (intro impI)
apply (clarsimp simp add: comp_exec_def inc_pcs_st_def inc_pcp_by_def wlen_byte_def is_ASMcore_def asm_nat_fit_nat)
apply (rule conjI)
 apply clarsimp
 apply (case_tac "ind = 0", simp add: asm_int_zero)
 apply (case_tac "ind = x371", simp add: asm_int_one)
 apply (erule_tac x = "ind" in allE, simp)
apply clarsimp
apply (case_tac "ind = 0", simp add: asm_int_zero)
apply (case_tac "ind = x371", simp add: asm_int_zero)
apply (erule_tac x = "ind" in allE, simp)

--"@{text Isge}"
apply (intro impI)
apply (clarsimp simp add: comp_exec_def inc_pcs_st_def inc_pcp_by_def wlen_byte_def is_ASMcore_def asm_nat_fit_nat)
apply (rule conjI)
 apply clarsimp
 apply (case_tac "ind = 0", simp add: asm_int_zero)
 apply (case_tac "ind = x381", simp add: asm_int_one)
 apply (erule_tac x = "ind" in allE, simp)
apply clarsimp
apply (case_tac "ind = 0", simp add: asm_int_zero)
apply (case_tac "ind = x381", simp add: asm_int_zero)
apply (erule_tac x = "ind" in allE, simp)

--"@{text Isls}"
apply (intro impI)
apply (clarsimp simp add: comp_exec_def inc_pcs_st_def inc_pcp_by_def wlen_byte_def is_ASMcore_def asm_nat_fit_nat)
apply (rule conjI)
 apply clarsimp
 apply (case_tac "ind = 0", simp add: asm_int_zero)
 apply (case_tac "ind = x391", simp add: asm_int_one)
 apply (erule_tac x = "ind" in allE, simp)
apply clarsimp
apply (case_tac "ind = 0", simp add: asm_int_zero)
apply (case_tac "ind = x391", simp add: asm_int_zero)
apply (erule_tac x = "ind" in allE, simp)

--"@{text Isne}"
apply (intro impI)
apply (clarsimp simp add: comp_exec_def inc_pcs_st_def inc_pcp_by_def wlen_byte_def is_ASMcore_def asm_nat_fit_nat)
apply (rule conjI)
 apply clarsimp
 apply (case_tac "ind = 0", simp add: asm_int_zero)
 apply (case_tac "ind = x401", simp add: asm_int_one)
 apply (erule_tac x = "ind" in allE, simp)
apply clarsimp
apply (case_tac "ind = 0", simp add: asm_int_zero)
apply (case_tac "ind = x401", simp add: asm_int_zero)
apply (erule_tac x = "ind" in allE, simp)

--"@{text Isle}"
apply (intro impI)
apply (clarsimp simp add: comp_exec_def inc_pcs_st_def inc_pcp_by_def wlen_byte_def is_ASMcore_def asm_nat_fit_nat)
apply (rule conjI)
 apply clarsimp
 apply (case_tac "ind = 0", simp add: asm_int_zero)
 apply (case_tac "ind = x411", simp add: asm_int_one)
 apply (erule_tac x = "ind" in allE, simp)
apply clarsimp
apply (case_tac "ind = 0", simp add: asm_int_zero)
apply (case_tac "ind = x411", simp add: asm_int_zero)
apply (erule_tac x = "ind" in allE, simp)

--"@{text Iset}"
apply (clarsimp simp add: comp_exec_def inc_pcs_st_def inc_pcp_by_def wlen_byte_def is_ASMcore_def asm_nat_fit_nat)
apply (case_tac "ind = 0", simp add: asm_int_zero)
apply (case_tac "ind = x42a", simp add: asm_int_one)
apply (erule_tac x = "ind" in allE, simp)

--"@{text Islli}"
apply (clarsimp simp add: arith_exec_def inc_pcs_st_def inc_pcp_by_def wlen_byte_def is_ASMcore_def asm_nat_fit_nat sllog_def)
apply (case_tac "ind = 0", simp add: asm_int_zero)
apply (case_tac "ind = x431")
 apply simp
 apply (rule asm_int_s_lsh)
 apply (clarsimp simp add: is_instr_def)
apply (erule_tac x = "ind" in allE, simp)

--"@{text Isrli}"
apply (clarsimp simp add: arith_exec_def inc_pcs_st_def inc_pcp_by_def wlen_byte_def is_ASMcore_def asm_nat_fit_nat srlog_def)
apply (case_tac "ind = 0", simp add: asm_int_zero)
apply (case_tac "ind = x441")
 apply simp
 apply (rule asm_int_s_rsh)
 apply (clarsimp simp add: is_instr_def)
apply (erule_tac x = "ind" in allE, simp)

--"@{text Israi}"
apply (clarsimp simp add: arith_exec_def inc_pcs_st_def inc_pcp_by_def wlen_byte_def is_ASMcore_def asm_nat_fit_nat srath_def)
apply (case_tac "ind = 0", simp add: asm_int_zero)
apply (case_tac "ind = x451")
 apply simp
 apply (rule asm_int_div)
  apply (simp add: zero_less_power)
 apply (clarsimp simp add: is_instr_def)
apply (erule_tac x = "ind" in allE, simp)

--"@{text Isll}"
apply (clarsimp simp add: arith_exec_def inc_pcs_st_def inc_pcp_by_def wlen_byte_def is_ASMcore_def asm_nat_fit_nat sllog_def)
apply (case_tac "ind = 0", simp add: asm_int_zero)
apply (case_tac "ind = x461")
 apply simp
 apply (rule asm_int_s_lsh)
 apply (clarsimp simp add: is_instr_def)
apply (erule_tac x = "ind" in allE, simp)

--"@{text Isrl}"
apply (clarsimp simp add: arith_exec_def inc_pcs_st_def inc_pcp_by_def wlen_byte_def is_ASMcore_def asm_nat_fit_nat srlog_def)
apply (case_tac "ind = 0", simp add: asm_int_zero)
apply (case_tac "ind = x471")
 apply simp
 apply (rule asm_int_s_rsh)
 apply (clarsimp simp add: is_instr_def)
apply (erule_tac x = "ind" in allE, simp)

--"@{text Isra}"
apply (clarsimp simp add: arith_exec_def inc_pcs_st_def inc_pcp_by_def wlen_byte_def is_ASMcore_def asm_nat_fit_nat srath_def)
apply (case_tac "ind = 0", simp add: asm_int_zero)
apply (case_tac "ind = x481")
 apply simp
 apply (rule asm_int_div)
  apply (simp add: zero_less_power)
 apply (clarsimp simp add: is_instr_def)
apply (erule_tac x = "ind" in allE, simp)

--"@{text Ibeqz}"
apply (clarsimp simp add: inc_pcp_by_def is_ASMcore_def asm_nat_fit_nat inc_pcs_st_def)

--"@{text Ibnez}"
apply (clarsimp simp add: inc_pcp_by_def is_ASMcore_def asm_nat_fit_nat inc_pcs_st_def)

--"@{text Ijal}"
apply (clarsimp simp add: inc_pcp_by_def is_ASMcore_def asm_nat_fit_nat)
apply (case_tac "ind = 0", simp add: asm_int_zero)
apply (case_tac "ind = GPR_ret")
 apply simp
 apply (rule asm_int_natwd_as_int)
 apply (rule asm_nat_fit_nat)
apply (erule_tac x = "ind" in allE, simp)

--"@{text Ijalr}"
apply (clarsimp simp add: inc_pcp_by_def is_ASMcore_def)
apply (rule conjI)
 apply (rule asm_nat_intwd_as_nat)
 apply (clarsimp simp add: is_instr_def)
apply clarsimp
apply (case_tac "ind = 0", simp add: asm_int_zero)
apply (case_tac "ind = GPR_ret")
 apply simp
 apply (rule asm_int_natwd_as_int)
 apply (rule asm_nat_fit_nat)
apply (erule_tac x = "ind" in allE, simp)

--"@{text Ij}"
apply (clarsimp simp add: inc_pcp_by_def is_ASMcore_def asm_nat_fit_nat)

--"@{text Ijr}"
apply (clarsimp simp add: is_ASMcore_def)
apply (rule asm_nat_intwd_as_nat)
apply (clarsimp simp add: is_instr_def)

--"@{text Itrap}"
apply (clarsimp simp add: inc_pcs_st_def is_ASMcore_def inc_pcp_by_def asm_nat_fit_nat)

--"@{text Irfe}"
apply simp
done

lemma ASMcore_consis_current_instr: 
      "\<lbrakk>is_ASMcore d; is_instr (current_instr d)\<rbrakk> \<Longrightarrow> is_ASMcore (Step d)"
apply (simp add: Step_def)
apply (erule ASMcore_consis_ind)
apply assumption
done

lemma is_not_branch_and_store_exec_instr: 
      "\<lbrakk>asm_nat( 8 + dpc d); pcp d = dpc d + 4; is_not_branch_and_store i \<rbrakk> \<Longrightarrow> 
                      dpc(exec_instr d i) = dpc d + 4 \<and> 
                      pcp (exec_instr d i) = pcp d + 4 \<and> 
                      mm (exec_instr d i) = mm d "
apply (induct i)

apply (simp_all add: load_exec_def Let_def inc_pcs_st_def wlen_byte_def inc_pcp_by_def fit_nat_def asm_nat_def wlen_bit_def
                     arith_exec_def comp_exec_def arith_exec_def)

apply (simp_all add: intwd_as_nat_4)

done

lemma is_not_branch_and_store_Step: 
      "\<lbrakk> asm_nat( 8 + dpc d); pcp d = dpc d + 4; is_not_branch_and_store (instr_mem_read (mm d) (dpc d)) \<rbrakk> \<Longrightarrow> 
                                          dpc(Step d) = dpc d + 4 \<and> 
                                          pcp (Step d) = pcp d + 4 \<and> 
                                          mm (Step d) = mm d "
apply (simp add: Step_def)
apply (simp add: current_instr_def)
apply (simp add: is_not_branch_and_store_exec_instr)
done

lemma ASMcore_consis_BigStep[rule_format]: 
      "\<forall> d. is_ASMcore d 
             \<longrightarrow> asm_nat (dpc d + 4 * n + 4)
             \<longrightarrow> pcp d = dpc d + 4
             \<longrightarrow> list_all (\<lambda> i. is_instr i \<and> is_not_branch_and_store i) (get_instr_list (mm d) (dpc d) n) 
             \<longrightarrow> is_ASMcore (BigStep d n)"
apply (induct_tac n)
 apply clarsimp
apply clarsimp
apply (simp add: list_all_iff)
apply (simp add: get_instr_list_def)
apply clarsimp
apply (erule_tac x="Step d" in allE)
apply (frule ASMcore_consis_current_instr)
 apply (simp add: current_instr_def)
 apply (simp add: instr_mem_read_def)
apply clarsimp
apply (subgoal_tac "asm_nat (8 + dpc d)")
 apply (frule is_not_branch_and_store_Step, simp)
  apply (simp add: instr_mem_read_def)
 apply clarsimp
 apply auto
  apply (subgoal_tac "(dpc d + 4) div 4 = Suc (dpc d div 4)")
   apply simp
apply (simp_all add: asm_nat_def)
  by (simp add: div_geq)

declare Let_def[simp del]

end
