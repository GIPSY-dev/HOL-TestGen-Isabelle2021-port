(**
 * Copyright (c) 2004-2007 Dirk Leinenbach.
 * Some rights reserved, Saarland University.
 *
 * This work is licensed under the German-Jurisdiction Creative Commons
 * Attribution Non-commercial Share Alike 2.0 License.
 * See the file LIZENZ for a full copy of the license.
**)
(* $Id: asm_execution_common.thy 23152 2008-04-16 07:25:27Z AlexandraTsyban $ *)
theory asm_execution_common imports Exec_properties prog_step_computation begin

declare Let_def[simp]

declare intwd_as_nat_0[simp];
declare intwd_as_nat_4[simp];
declare intwd_as_nat_8[simp];
declare intwd_as_nat_12[simp];

lemma beqz_execution1[rule_format]: "is_ASMcore d \<longrightarrow> reg (gprs d) r \<noteq> 0 \<longrightarrow> current_instr d = Ibeqz r dist
                                       \<longrightarrow> asm_nat (add_pc (pcp d) 4)
                                       \<longrightarrow> BigStep d 1 = d \<lparr> dpc := pcp d, pcp := pcp d + 4 \<rparr>"
apply clarsimp
apply (simp add: Step_def)
apply (simp add: current_instr_def)
apply (simp add: inc_pcs_st_def)
apply (subgoal_tac "asm_int 4")
 apply (frule_tac x="4" and p="pcp d" in inc_pcp_by_is_add_pc)
    apply (simp add: is_ASMcore_def)
   apply simp
  apply simp
 apply (simp add: add_pc_plus)
 apply (simp add: wlen_byte_def)
apply (simp add: asm_int_def)
apply (simp add: wlen_bit_def)
done

lemma beqz_execution2[rule_format]: "is_ASMcore d \<longrightarrow> reg (gprs d) r = 0 \<longrightarrow> current_instr d = Ibeqz r dist
                                       \<longrightarrow> asm_nat (add_pc (pcp d) dist) \<longrightarrow> asm_int dist \<longrightarrow> 0 \<le> int (pcp d) + dist
                                       \<longrightarrow> BigStep d 1 = d \<lparr> dpc := pcp d, pcp := add_pc (pcp d) dist \<rparr>"
apply clarsimp
apply (simp add: Step_def)
apply (simp add: current_instr_def)
apply (frule_tac x="dist" and p="pcp d" in inc_pcp_by_is_add_pc)
   apply (simp add: is_ASMcore_def)
  apply simp
 apply simp
apply clarsimp
done

lemma bnez_execution1[rule_format]: "is_ASMcore d \<longrightarrow> reg (gprs d) r = 0 \<longrightarrow> current_instr d = Ibnez r dist
                                        \<longrightarrow> asm_nat (add_pc (pcp d) 4)
                                       \<longrightarrow> BigStep d 1 = d \<lparr> dpc := pcp d, pcp := pcp d + 4 \<rparr>"
apply clarsimp
apply (simp add: Step_def)
apply (simp add: current_instr_def)
apply (simp add: inc_pcs_st_def)
apply (subgoal_tac "asm_int 4")
 apply (frule_tac x="4" and p="pcp d" in inc_pcp_by_is_add_pc)
    apply (simp add: is_ASMcore_def)
   apply simp
  apply simp
 apply (simp add: add_pc_plus)
 apply (simp add: wlen_byte_def)
apply (simp add: asm_int_def)
apply (simp add: wlen_bit_def)
done

lemma bnez_execution2[rule_format]: "is_ASMcore d \<longrightarrow> reg (gprs d) r \<noteq> 0 \<longrightarrow> current_instr d = Ibnez r dist
                                        \<longrightarrow> asm_nat (add_pc (pcp d) dist) \<longrightarrow> asm_int dist \<longrightarrow> 0 \<le> int (pcp d) + dist
                                       \<longrightarrow> BigStep d 1 = d \<lparr> dpc := pcp d, pcp := add_pc (pcp d) dist \<rparr>"
apply clarsimp
apply (simp add: Step_def)
apply (simp add: current_instr_def)
apply (frule_tac x="dist" and p="pcp d" in inc_pcp_by_is_add_pc)
   apply (simp add: is_ASMcore_def)
  apply simp
 apply simp
apply clarsimp
done

lemma jump_execution[rule_format]: "is_ASMcore d \<longrightarrow> current_instr d = Ij dist 
                                     \<longrightarrow> asm_nat (add_pc (pcp d) dist) \<longrightarrow> asm_int dist \<longrightarrow> 0 \<le> int (pcp d) + dist
                                     \<longrightarrow> BigStep d 1 = d \<lparr> dpc := pcp d, pcp := add_pc (pcp d) dist \<rparr>"
apply clarsimp
apply (simp add: Step_def)
apply (simp add: current_instr_def)
apply (frule_tac x="dist" and p="pcp d" in inc_pcp_by_is_add_pc)
   apply (simp add: is_ASMcore_def)
  apply simp
 apply simp
apply clarsimp
done

lemma nop_execution[rule_format]: "is_ASMcore d \<longrightarrow> current_instr d = Inop
                                       \<longrightarrow> asm_nat (add_pc (pcp d) 4)
                                       \<longrightarrow> BigStep d 1 = d \<lparr> dpc := pcp d, pcp := pcp d + 4 \<rparr>"
apply clarsimp
apply (simp add: Step_def)
apply (simp add: current_instr_def)
apply (simp add: inc_pcs_st_def)
apply (simp add: wlen_byte_def)
apply (subgoal_tac "asm_int 4")
 apply (frule_tac x="4" and p="pcp d" in inc_pcp_by_is_add_pc)
    apply (simp add: is_ASMcore_def)
   apply simp
  apply simp
 apply (simp add: add_pc_plus)
apply (simp add: asm_int_def)
apply (simp add: wlen_bit_def)
done

lemma jr_execution[rule_format]: "current_instr d = Ijr r
                                     \<longrightarrow> BigStep d 1 = d \<lparr> dpc := pcp d, pcp := intwd_as_nat (reg (gprs d) r) \<rparr>"
apply clarsimp
apply (simp add: Step_def)
done

declare intwd_as_nat_0[simp del];
declare intwd_as_nat_4[simp del];
declare intwd_as_nat_8[simp del];
declare intwd_as_nat_12[simp del];

declare Let_def[simp del]

end
