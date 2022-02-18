(**
 * Copyright (c) 2006-2009 Matthias Daum, Dirk Leinenbach, Hristo Pentchev, 
 * Alexandra Tsyban.
 * Some rights reserved, Saarland University.
 *
 * This work is licensed under the German-Jurisdiction Creative Commons
 * Attribution Non-commercial Share Alike 2.0 License.
 * See the file LIZENZ for a full copy of the license.
**)
(* $Id: asm_execution_without_interrupt.thy 29816 2009-11-24 12:55:59Z DirkLeinenbach $ *)
theory asm_execution_without_interrupt imports asm_execution_common begin

declare Let_def[simp]

definition mem_access_inside_range :: "ASMcore_t \<Rightarrow> rangeT \<Rightarrow> bool"
where
  "mem_access_inside_range d address_range \<equiv>
     is_load_store (current_instr d) \<longrightarrow> fst address_range \<le> load_store_target d 
                                       \<and> load_store_target d + load_store_access_width (current_instr d) \<le> fst address_range + snd address_range"

definition no_mem_write_access_inside_code :: "ASMcore_t \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool"
where
  "no_mem_write_access_inside_code d base end \<equiv>
     is_store (current_instr d) \<longrightarrow> (4 * end \<le> load_store_target d 
                                    \<or> load_store_target d + load_store_access_width (current_instr d) \<le> 4 * base)"

definition not_dmal_in_ASM :: "ASMcore_t \<Rightarrow> bool"
where
  "not_dmal_in_ASM d \<equiv> 
     (is_load_store_word (current_instr d) \<longrightarrow> 4 dvd load_store_target d)
  \<and> (is_load_store_hword (current_instr d) \<longrightarrow> 2 dvd load_store_target d)"

definition not_imal_in_ASM :: "ASMcore_t \<Rightarrow> bool"
where
  "not_imal_in_ASM d \<equiv> (4 dvd dpc d)"

text {*
  The predicate @{text is_interrupt_free} tests if the current instruction would generate an interrupt.
  It tests for: instruction misalignment, data misalignment, memory access outside the @{text address_range}, writes to the code, and if the dpc is inside the @{text code_range}.
  *}

definition is_interrupt_free :: "ASMcore_t \<Rightarrow> (nat \<times> nat) \<Rightarrow> rangeT \<Rightarrow> bool"
where
  "is_interrupt_free d code_range address_range \<equiv>
   (
      not_imal_in_ASM d
     \<and> not_dmal_in_ASM d
     \<and> mem_access_inside_range d address_range
     \<and> no_mem_write_access_inside_code d (fst code_range) (snd code_range)
     \<and> inside_range (word_range_to_byte code_range) (dpc d)
     \<and> \<not> (is_Imovi2s (current_instr d) \<and> sa_arg (current_instr d) = SPR_MODE)
     \<and> \<not> (is_Imovi2s (current_instr d) \<and> sa_arg (current_instr d) = SPR_SR)
     \<and> \<not> is_Itrap (current_instr d)
   )
  "

inductive_set asm_executes_in_t_steps_woi :: "(ASMcore_t \<times> instr list \<times> (nat \<times> nat) \<times> rangeT \<times> nat \<times> ASMcore_t) set"
where
  AEITSWOIintro[intro] : "\<lbrakk>
                  get_instr_list (mm c) a (length q) = q;
                  dpc c = a;
                  pcp c = a + 4;
                  dpc c' = a + 4 * length q;
                  pcp c' = dpc c' + 4;
                  BigStep c k = c';
                  \<forall> k'. k' < k \<longrightarrow> (is_interrupt_free (BigStep c k') rangee address_range
                                    \<and> advancing_instr (BigStep c k') (current_instr (BigStep c k')))
                \<rbrakk>
                \<Longrightarrow> (c, q, rangee, address_range, k, c') \<in> asm_executes_in_t_steps_woi"


definition asm_executes_precondition_woi :: "ASMcore_t \<Rightarrow> (nat \<times> nat) \<Rightarrow> instr list \<Rightarrow> bool"
where
  "asm_executes_precondition_woi d rangee il \<equiv> 
   (
     is_ASMcore d
     \<and> 4 dvd (dpc d)
     \<and> pcp d= dpc d + 4
     \<and> get_instr_list (mm d) (dpc d) (length il) = il
     \<and> list_all is_instr il
     \<and> (il \<noteq> [] \<longrightarrow> inside_range (word_range_to_byte rangee) (dpc d))
     \<and> (il \<noteq> [] \<longrightarrow> inside_range (word_range_to_byte rangee) (dpc d + 4 * length il - 1))
     \<and> asm_nat (4 * snd rangee + 4)
   )
  "

definition asm_executes_woi :: "ASMcore_t \<Rightarrow> (nat \<times> nat) \<Rightarrow> rangeT \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> ASMcore_t \<Rightarrow> bool"
where
  "asm_executes_woi d rangee address_range t dest d' \<equiv> 
   (
     (
        dpc d' = dest
        \<and> pcp d' = dpc d' + 4
        \<and> BigStep d t = d'
        \<and> is_ASMcore d'
        \<and> (\<forall> t' < t. is_interrupt_free (BigStep d t') rangee address_range
                       \<and> advancing_instr (BigStep d t') (current_instr (BigStep d t'))
          )
     )
   )
  "


lemma no_mem_write_access_inside_code_mm_Step:
 "\<lbrakk>no_mem_write_access_inside_code s x y; inside_range (x, y) ad\<rbrakk>
  \<Longrightarrow> mm (Step s) ad = mm s ad"
apply (case_tac "current_instr s")
apply (simp_all add: Step_def is_store_def
            load_exec_def arith_exec_def comp_exec_def)
apply (simp_all add: no_mem_write_access_inside_code_def is_store_def
         inside_range_def load_store_target_def
         is_load_store_word_def is_load_store_hword_def
         is_load_store_byte_def is_load_store_def load_store_access_width_def
         store_exec_def store_to_mem_def data_mem_write_def)
apply arith+
done

lemma is_interrupt_free_impl_mem_unchanged_code_range:
  assumes "is_interrupt_free s crange arange"
  shows "mem_unchanged_word (mm s) (mm (Step s)) (fst crange) (snd crange)"
proof -
from assms show ?thesis
  apply -
  apply (simp add: is_interrupt_free_def)
  apply clarsimp
  apply (thin_tac "not_imal_in_ASM s", thin_tac "not_dmal_in_ASM s",
         thin_tac "mem_access_inside_range s arange",
         thin_tac "inside_range (word_range_to_byte crange) (dpc s)", thin_tac"~?P")
  apply (thin_tac "?x --> ?y")+
  apply (simp add: no_mem_write_access_inside_code_def)
  apply (simp add: mem_unchanged_word_def)
  using load_store_target_def[where d=s,symmetric, simplified]
  apply clarsimp
  apply (rename_tac i)
  apply (simp add: Step_def is_store_def)
  apply (case_tac "current_instr s")
  apply (simp_all add: load_exec_def arith_exec_def comp_exec_def Let_def)
  apply (simp_all add: load_store_access_width_def is_load_store_word_def is_load_store_hword_def)
  apply (simp_all add: store_exec_def store_to_mem_def data_mem_write_def Let_def)
  apply (simp_all add: le_simps)

  apply clarsimp
  apply (rename_tac r1 r2 imm)
  apply arith

  apply clarsimp
  apply (rename_tac r1 r2 imm)
  apply arith

  apply clarsimp
  apply (rename_tac r1 r2 imm)
  apply arith
  done
qed

lemma is_interrupt_free_impl_mem_unchanged_code_range_bigstep_aux: "(\<forall> t' < t. is_interrupt_free (BigStep d t') crange arange)
                                                                   \<longrightarrow> (\<forall> t' \<le> t. mem_unchanged_word (mm d) (mm (BigStep d t')) (fst crange) (snd crange))"
apply (induct_tac t)
 apply (simp add: mem_unchanged_word_def)
apply clarsimp
apply (case_tac "t' < Suc n")
 apply clarsimp
apply clarsimp
apply (erule_tac x="n" in allE)
apply (erule_tac x="n" in allE)
apply clarsimp
apply (drule is_interrupt_free_impl_mem_unchanged_code_range)
apply (simp add: mem_unchanged_word_def)
apply (simp add: Step_BigStep_swap)
done

lemma is_interrupt_free_impl_mem_unchanged_code_range_bigstep: 
  assumes "\<forall> t' < t. is_interrupt_free (BigStep d t') crange arange"
  shows "mem_unchanged_word (mm d) (mm (BigStep d t)) (fst crange) (snd crange)"
proof -
  from assms show ?thesis
    by (simp add: is_interrupt_free_impl_mem_unchanged_code_range_bigstep_aux)
qed

lemma asm_executes_woi_impl_mem_unchanged_code_range:
  assumes "asm_executes_woi d rangee address_range t dest d'"
  shows "mem_unchanged_word (mm d) (mm d') (fst rangee) (snd rangee)"
proof -
  from assms show ?thesis
    apply -
    apply (simp add: asm_executes_woi_def)
    apply clarsimp
    by (rule_tac arange="address_range" in is_interrupt_free_impl_mem_unchanged_code_range_bigstep, simp+)
qed

lemma asm_executes_woi_impl_mem_unchanged_code_range':
  assumes "asm_executes_woi d rangee address_range t dest d'"
  shows "mem_unchanged (mm d) (mm d') (4 * fst rangee) (4 * snd rangee)"
proof -
  from assms asm_executes_woi_impl_mem_unchanged_code_range[OF assms] show ?thesis
    by (simp add: mem_unchanged_def)
qed

lemma not_is_load_store_is_interrupt_free[rule_format]: "\<not> (is_load_store (current_instr d) \<or> is_Imovi2s (current_instr d) \<or> is_Itrap (current_instr d))
                                                          \<longrightarrow> 4 dvd dpc d
                                                          \<longrightarrow> inside_range (word_range_to_byte rangee) (dpc d)
                                                          \<longrightarrow> is_interrupt_free d rangee address_range"
apply clarsimp
apply (simp add: is_interrupt_free_def)
apply (simp add: not_imal_in_ASM_def not_dmal_in_ASM_def mem_access_inside_range_def no_mem_write_access_inside_code_def)
apply (simp add: is_load_store_def is_load_store_word_def is_load_store_hword_def is_load_store_byte_def is_store_def)
done

lemma is_not_branch_and_mem_access_is_interrupt_free_BigStep[rule_format]: 
      "\<forall> d. asm_nat (dpc d + 4 * n + 4)
             \<longrightarrow> 4 dvd dpc d
             \<longrightarrow> inside_range (word_range_to_byte rangee) (dpc d)
             \<longrightarrow> inside_range (word_range_to_byte rangee) (dpc d + 4 * n - 1)
             \<longrightarrow> pcp d = dpc d + 4
             \<longrightarrow> list_all (\<lambda> i. is_not_branch_and_mem_access i \<and> \<not> is_Imovi2s i \<and> \<not> is_Itrap i) (get_instr_list (mm d) (dpc d) n)
             \<longrightarrow> (\<forall> t < n. is_interrupt_free (BigStep d t) rangee address_range)"
apply (induct_tac n)
 apply clarsimp
apply clarsimp
apply (simp add: is_not_branch_and_mem_access_def)
apply (simp add: list_all_iff)
apply (simp add: get_instr_list_def)
apply clarsimp
apply (erule_tac x="Step d" in allE)
apply (subgoal_tac "asm_nat (8 + dpc d)")
 apply (frule_tac is_not_branch_and_store_Step, simp)
  apply (simp add: instr_mem_read_def)
 apply clarsimp
 apply (simp add: dvd_add)
 apply (case_tac n)
  apply clarsimp
  apply (rule not_is_load_store_is_interrupt_free)
    apply (simp add: current_instr_def)
    apply (simp add: instr_mem_read_def)
   apply simp
  apply simp
 apply clarsimp
 apply (subgoal_tac "(dpc d + 4) div 4 = Suc (dpc d div 4)")
  apply simp
  apply (subgoal_tac "inside_range (word_range_to_byte rangee) (dpc d + 4)")
   apply simp
   apply (erule_tac x="t - 1" in allE)
   apply clarsimp
   apply (case_tac "t")
    apply clarsimp
    apply (rule not_is_load_store_is_interrupt_free)
      apply (simp add: current_instr_def)
      apply (simp add: instr_mem_read_def)
     apply simp
    apply simp
   apply force
  apply (simp add: inside_range_def)
 apply arith
apply (simp add: asm_nat_def)
done

lemma is_not_branch_and_mem_access_same_memory[rule_format]: 
      "\<forall> d. asm_nat (dpc d + 4 * n + 4)
             \<longrightarrow> 4 dvd dpc d
             \<longrightarrow> inside_range (word_range_to_byte rangee) (dpc d)
             \<longrightarrow> inside_range (word_range_to_byte rangee) (dpc d + 4 * n - 1)
             \<longrightarrow> pcp d = dpc d + 4
             \<longrightarrow> list_all (\<lambda> i. is_not_branch_and_mem_access i \<and> \<not> is_Imovi2s i \<and> \<not> is_Itrap i) (get_instr_list (mm d) (dpc d) n)
             \<longrightarrow> (\<forall> t < n. mm (BigStep d t) = mm d)"
apply (induct_tac n)
 apply clarsimp
apply clarsimp
apply (simp add: is_not_branch_and_mem_access_def)
apply (simp add: list_all_iff)
apply (simp add: get_instr_list_def)
apply clarsimp
apply (erule_tac x="Step d" in allE)
apply (subgoal_tac "asm_nat (8 + dpc d)")
 apply (frule_tac is_not_branch_and_store_Step, simp)
  apply (simp add: instr_mem_read_def)
 apply clarsimp
 apply (simp add: dvd_add)
 apply (case_tac n, simp)
 apply clarsimp
 apply (subgoal_tac "(dpc d + 4) div 4 = Suc (dpc d div 4)")
  apply simp
  apply (subgoal_tac "inside_range (word_range_to_byte rangee) (dpc d + 4)")
   apply simp
   apply (erule_tac x="t - 1" in allE)
   apply clarsimp
   apply (case_tac "t")
    apply clarsimp
   apply clarsimp
  apply (simp add: inside_range_def)
 apply arith
apply (simp add: asm_nat_def)
done

lemma is_not_branch_and_mem_access_mem_unchanged[rule_format]: 
      "\<forall> d. asm_nat (dpc d + 4 * n + 4)
             \<longrightarrow> 4 dvd dpc d
             \<longrightarrow> inside_range (word_range_to_byte rangee) (dpc d)
             \<longrightarrow> inside_range (word_range_to_byte rangee) (dpc d + 4 * n - 1)
             \<longrightarrow> pcp d = dpc d + 4
             \<longrightarrow> list_all (\<lambda> i. is_not_branch_and_mem_access i \<and> \<not> is_Imovi2s i \<and> \<not> is_Itrap i) (get_instr_list (mm d) (dpc d) n)
             \<longrightarrow> (\<forall> t < n. mem_unchanged (mm d) (mm (BigStep d t)) a b)"
apply clarsimp
apply (simp add: mem_unchanged_def)
apply (simp add: mem_unchanged_word_def)
apply clarsimp
apply (simp add: is_not_branch_and_mem_access_same_memory)
done

lemma asm_executes_woi_append[rule_format]: "asm_executes_woi d rangee address_range ta x d'
                                         \<longrightarrow> asm_executes_woi d' rangee address_range tb dest d''
                                         \<longrightarrow> asm_executes_woi d rangee address_range (ta+tb) dest d''"
apply clarsimp
apply (simp add: asm_executes_woi_def)
apply clarsimp
apply (simp add: BigStep_add)
apply clarsimp
apply (case_tac "t' < ta")
 apply force
apply (erule_tac x="t' - ta" in allE)+
apply (subgoal_tac "t' - ta < tb")
 apply clarsimp
 apply (simp add: BigStep_add[symmetric])
apply arith
done

lemma asm_exec_precond_woi_append[rule_format]: "asm_executes_precondition_woi d rangee (a@b) 
                                              \<longrightarrow> asm_executes_woi d rangee address_range t (dpc d + 4 * length a) d'
                                              \<longrightarrow> asm_executes_precondition_woi d' rangee b"
apply clarsimp
apply (simp add: asm_executes_precondition_woi_def)
apply (frule asm_executes_woi_impl_mem_unchanged_code_range)
apply (simp add: asm_executes_woi_def)
apply clarsimp
apply (case_tac "a@b=[]")
 apply clarsimp
 apply (simp add: get_instr_list_def)
apply clarsimp
apply (frule get_instr_list_append2)
apply (rule conjI)
 apply (simp add: dvd_add)
apply (rule conjI)
 apply (simp add: inside_range_def)
 apply (cut_tac base="dpc d + 4 * length a" and l="length b" and a="fst (word_range_to_byte rangee)" and b="snd (word_range_to_byte rangee)" in mem_unchanged_get_instr_list_same)
    apply (simp add: mem_unchanged_def)
    apply (simp add: word_range_to_byte_def)
   apply simp
  apply arith
 apply simp
apply (rule conjI)
 apply clarsimp
 apply (simp add: inside_range_def)
 apply clarsimp
 apply (case_tac b, simp)
 apply clarsimp
apply clarsimp
apply (simp add: inside_range_def)
apply clarsimp
apply (case_tac b, simp)
apply clarsimp
done

lemma asm_executes_woi_dpc[rule_format]: "asm_executes_woi d rangee address_range t dest d' \<longrightarrow> dpc d' = dest"
apply (simp add: asm_executes_woi_def)
done

lemma asm_executes_woi_pcp[rule_format]: "asm_executes_woi d rangee address_range t dest d' \<longrightarrow> pcp d' = dpc d' + 4"
apply clarsimp
apply (simp add: asm_executes_woi_def)
done

lemma asm_exec_precond_woi_append2[rule_format]: "asm_executes_precondition_woi d rangee (a@b) \<longrightarrow> asm_executes_precondition_woi d rangee a"
apply clarsimp
apply (simp add: asm_executes_precondition_woi_def)
apply clarsimp
apply (simp add: get_instr_list_append1)
apply clarsimp
apply (frule_tac a="dpc d" and b="dpc d + (4* length a + 4* length b) - 1" and x="dpc d + 4 * length a - 1" in inside_range_interval, simp+)
  apply (simp add: inside_range_def)
  apply (case_tac a, simp)
  apply clarsimp
 apply (simp add: inside_range_def)
 apply clarsimp
 apply (case_tac b, simp)
 apply clarsimp
 apply arith
apply simp
done

lemma asm_exec_precond_woi_hd[rule_format]: "asm_executes_precondition_woi d rangee (a#b) \<longrightarrow> asm_executes_precondition_woi d rangee [a]"
apply clarsimp
apply (simp add: asm_executes_precondition_woi_def)
apply clarsimp
apply (frule get_instr_list_head)
apply clarsimp
apply (frule_tac a="dpc d" and b="dpc d + (4* length [a] + 4* length b) - 1" and x="dpc d + 4 - 1" in inside_range_interval, simp+)
done

lemma asm_exec_precond_woi_tl[rule_format]: "asm_executes_precondition_woi d rangee (a#b) 
                                              \<longrightarrow> asm_executes_woi d rangee address_range t (dpc d + 4) d'
                                              \<longrightarrow> asm_executes_precondition_woi d' rangee b"
apply clarsimp
apply (frule asm_executes_woi_impl_mem_unchanged_code_range)
apply (simp add: asm_executes_precondition_woi_def)
apply (simp add: asm_executes_woi_def)
apply clarsimp
apply (frule get_instr_list_tail)
apply clarsimp
apply (simp add: inside_range_def)
apply (cut_tac base="dpc d + 4" and l="length b" and a="fst (word_range_to_byte rangee)" and b="snd (word_range_to_byte rangee)" in mem_unchanged_get_instr_list_same)
   apply (simp add: mem_unchanged_def)
   apply (simp add: word_range_to_byte_def)
  apply simp
 apply arith
apply (simp add: dvd_add)
apply clarsimp
apply (case_tac b, simp)
apply simp
done

lemma asm_exec_precond_woi_take[rule_format]: "asm_executes_precondition_woi d rangee l \<longrightarrow> n \<le> length l \<longrightarrow> asm_executes_precondition_woi d rangee (take n l)"
apply clarsimp
apply (simp add: asm_executes_precondition_woi_def)
apply clarsimp
apply (simp add: list_all_take)
apply (simp add: min_def)
apply (rule conjI)
 apply clarsimp
apply clarsimp
apply (simp add: get_instr_list_take2)
apply clarsimp
apply (frule_tac a="dpc d" and b="dpc d + 4* length l - 1" and x="dpc d + 4 * n - 1" in inside_range_interval, simp+)
  apply arith
 apply arith
apply simp
done

lemma asm_executes_woi_gprs_length[rule_format]: "asm_executes_woi d rangee addr_range t dest d' \<longrightarrow> length (gprs d') = 32"
apply (simp add: asm_executes_woi_def is_ASMcore_def)
done

lemma asm_precondition_woi_gprs_length[rule_format]: "asm_executes_precondition_woi d rangee ecode \<longrightarrow> length (gprs d) = 32"
apply (simp add: asm_executes_precondition_woi_def is_ASMcore_def)
done

lemma asm_executes_woi_impl_is_ASMcore[rule_format]: "asm_executes_woi d rangee address_range t dest d' \<longrightarrow> is_ASMcore d'"
apply clarsimp
apply (simp add: asm_executes_woi_def)
done

lemma asm_executes_woi_asm_int[rule_format]: "asm_executes_woi d rangee address_range t dest d' \<longrightarrow> r < 32 \<longrightarrow> asm_int (reg (gprs d') r)"
apply clarsimp
apply (frule asm_executes_woi_impl_is_ASMcore) 
apply (simp add: is_ASMcore_def)
done

lemma asm_executes_precondition_woi_is_ASMcore[rule_format]: "asm_executes_precondition_woi d rangee il \<longrightarrow> is_ASMcore d"
apply clarsimp
apply (simp add: asm_executes_precondition_woi_def)
done

lemma asm_executes_precondition_woi_asm_int[rule_format]: "asm_executes_precondition_woi d rangee il \<longrightarrow> r < 32 \<longrightarrow> asm_int (reg (gprs d) r)"
apply clarsimp
apply (frule asm_executes_precondition_woi_is_ASMcore) 
apply (simp add: is_ASMcore_def)
done

lemma asm_executes_precondition_woi_snd_range_asm_nat[rule_format]: "asm_executes_precondition_woi d rangee il \<longrightarrow> asm_nat (4 * snd rangee + 4)"
apply (simp add: asm_executes_precondition_woi_def)
done

lemma asm_executes_precondition_woi_pcp[rule_format]: "asm_executes_precondition_woi d rangee il \<longrightarrow> pcp d = dpc d + 4"
apply clarsimp
apply (simp add: asm_executes_precondition_woi_def)
done

lemma asm_execute_precondition_woi_inside_range1[rule_format]: "asm_executes_precondition_woi d rangee il \<longrightarrow> il \<noteq> [] \<longrightarrow> inside_range (word_range_to_byte rangee) (dpc d)"
apply (simp add: asm_executes_precondition_woi_def)
done

lemma asm_execute_precondition_woi_inside_range2[rule_format]: "asm_executes_precondition_woi d rangee il \<longrightarrow> il \<noteq> [] \<longrightarrow> inside_range (word_range_to_byte rangee) (dpc d + 4 * length il - 1)"
apply (simp add: asm_executes_precondition_woi_def)
done

(*
  Execution of certain assembler instruction or combinations of assembler instructions
*)

declare intwd_as_nat_0[simp];
declare intwd_as_nat_4[simp];
declare intwd_as_nat_8[simp];
declare intwd_as_nat_12[simp];

declare is_load_store_word_def[simp]
declare is_load_store_hword_def[simp]
declare is_load_store_byte_def[simp]
declare is_load_store_def[simp]
declare load_store_access_width_def[simp]

lemma beqz_nop_execution1_woi[rule_format]: "asm_executes_precondition_woi d rangee [Ibeqz r dist, Inop] 
                                         \<longrightarrow> reg (gprs d) r \<noteq> 0
                                         \<longrightarrow> asm_nat (add_pc (pcp d) 8)
                                         \<longrightarrow> asm_executes_woi d rangee address_range 2 (pcp d + 4) (d \<lparr> dpc := pcp d + 4, pcp := pcp d + 8 \<rparr>)"
apply clarsimp
apply (simp add: asm_executes_precondition_woi_def)
apply (simp add: asm_executes_woi_def)
apply clarsimp
apply (simp add: BigStep_decompose)
apply (subgoal_tac "current_instr d = Ibeqz r dist")
 apply (frule_tac d="d" in ASMcore_consis_current_instr, simp)
 apply (insert beqz_execution1 [where d="d" and r="r" and dist="dist"])
 apply clarsimp
 apply (simp add: add_pc_plus)
 apply (insert asm_nat_monotonic [where x="8 + dpc d" and n="12 + dpc d"])
 apply (subgoal_tac "inside_range (word_range_to_byte rangee) (7 + dpc d)")
  prefer 2
  apply (simp add: nat_add_commute)
 apply clarsimp
 apply (subgoal_tac "current_instr (Step d) = Inop")
  apply (frule_tac d="d\<lparr>dpc := dpc d + 4, pcp := 8 + dpc d\<rparr>" in ASMcore_consis_current_instr)
   apply (simp add: nop_is_instr)
  apply clarsimp
  apply (insert nop_execution [where d="Step d"])
  apply simp
  apply (simp add: add_pc_plus)
  apply clarsimp
  apply (case_tac "t'=0")
   apply clarsimp
   apply (rule not_is_load_store_is_interrupt_free)
     apply (simp add: current_instr_def is_Itrap_def)
    apply simp
   apply simp
  apply (subgoal_tac "t'=1")
   apply clarsimp
   apply (rule conjI)
    apply (rule not_is_load_store_is_interrupt_free)
      apply (simp add: current_instr_def is_Itrap_def)
      apply (simp add: Inop_def)
     apply (simp add: dvd_add)
    apply (simp add: inside_range_def)
   apply (rule not_is_jump_branch_system_is_advancing_instr)
    apply (simp add: Inop_def)
   apply (simp add: Inop_def is_system_instr_def is_Itrap_def is_Irfe_def)
  apply clarsimp
 apply (insert instr_list_content [where i="1" and l="Suc (Suc 0)" and ad="dpc d" and d="Step d"])
 apply clarsimp
apply clarsimp
apply (insert instr_list_content [where i="0" and l="Suc (Suc 0)" and ad="dpc d" and d="d"])
apply clarsimp
done

lemma bnez_nop_execution1_woi[rule_format]: "asm_executes_precondition_woi d rangee [Ibnez r dist, Inop] 
                                         \<longrightarrow> reg (gprs d) r = 0
                                         \<longrightarrow> asm_nat (add_pc (pcp d) 8)
                                         \<longrightarrow> asm_executes_woi d rangee address_range 2 (pcp d + 4) (d \<lparr> dpc := pcp d + 4, pcp := pcp d + 8 \<rparr>)"
apply clarsimp
apply (simp add: asm_executes_precondition_woi_def)
apply (simp add: asm_executes_woi_def)
apply clarsimp
apply (simp add: BigStep_decompose)
apply (subgoal_tac "current_instr d = Ibnez r dist")
 apply (frule_tac d="d" in ASMcore_consis_current_instr, simp)
 apply (insert bnez_execution1 [where d="d" and r="r" and dist="dist"])
 apply clarsimp
 apply (simp add: add_pc_plus)
 apply (insert asm_nat_monotonic [where x="8 + dpc d" and n="12 + dpc d"])
 apply clarsimp
 apply (simp add: nat_add_commute)
 apply (subgoal_tac "current_instr (Step d) = Inop")
  apply (frule_tac d="d\<lparr>dpc := dpc d + 4, pcp := dpc d + 8\<rparr>" in ASMcore_consis_current_instr)
   apply (simp add: nop_is_instr)
  apply clarsimp
  apply (insert nop_execution [where d="Step d"])
  apply simp
  apply (simp add: add_pc_plus nat_add_commute)
  apply clarsimp
  apply (case_tac "t'=0")
   apply clarsimp
   apply (rule not_is_load_store_is_interrupt_free)
     apply (simp add: current_instr_def is_Itrap_def)
    apply simp
   apply simp
  apply (subgoal_tac "t'=1")
   apply clarsimp
   apply (rule conjI)
    apply (rule not_is_load_store_is_interrupt_free)
      apply (simp add: current_instr_def is_Itrap_def)
      apply (simp add: Inop_def)
     apply (simp add: dvd_add)
    apply (simp add: inside_range_def)
   apply (rule not_is_jump_branch_system_is_advancing_instr)
    apply (simp add: Inop_def)
   apply (simp add: Inop_def is_system_instr_def is_Itrap_def is_Irfe_def)
  apply clarsimp
 apply (insert instr_list_content [where i="1" and l="Suc (Suc 0)" and ad="dpc d" and d="Step d"])
 apply clarsimp
apply clarsimp
apply (insert instr_list_content [where i="0" and l="Suc (Suc 0)" and ad="dpc d" and d="d"])
apply clarsimp
done

lemma jump_nop_execution_woi[rule_format]: "asm_executes_precondition_woi d rangee [Ij dist, Inop]
                                        \<longrightarrow> asm_nat ((add_pc (dpc d + 4) dist) + 4) 
                                        \<longrightarrow> asm_int dist
                                        \<longrightarrow> 0 \<le> int (dpc d) + 4 + dist
                                        \<longrightarrow> asm_executes_woi d rangee address_range 2 (add_pc (pcp d) dist) (d \<lparr> dpc := (add_pc (pcp d) dist), pcp := (add_pc (pcp d) dist) + 4 \<rparr>)"
apply clarsimp
apply (simp add: asm_executes_precondition_woi_def)
apply (simp add: asm_executes_woi_def)
apply clarsimp
apply (simp add: BigStep_decompose)
apply (subgoal_tac "current_instr d = Ij dist")
 apply (frule_tac d="d" in ASMcore_consis_current_instr, simp)
 apply (insert jump_execution [where d="d" and dist="dist"])
 apply clarsimp
 apply (insert asm_nat_monotonic [where x="add_pc (dpc d + 4) dist" and n="add_pc (dpc d + 4) dist + 4"])
 apply simp
 apply (subgoal_tac "current_instr (Step d) = Inop")
  apply (frule_tac d="d\<lparr>dpc := dpc d + 4, pcp := add_pc (dpc d + 4) dist\<rparr>" in ASMcore_consis_current_instr, simp)
  apply (simp add: nop_is_instr)
  apply (frule_tac d="d" in ASMcore_consis_current_instr, simp)
  apply (insert nop_execution [where d="Step d"])
  apply clarsimp
  apply (simp add: add_pc_plus)
  apply clarsimp
  apply (case_tac "t'=0")
   apply clarsimp
   apply (rule not_is_load_store_is_interrupt_free)
     apply (simp add: current_instr_def is_Itrap_def)
    apply simp
   apply simp
  apply (subgoal_tac "t'=1")
   apply clarsimp
   apply (rule conjI)
    apply (rule not_is_load_store_is_interrupt_free)
      apply (simp add: current_instr_def is_Itrap_def)
      apply (simp add: Inop_def)
     apply (simp add: dvd_add)
    apply (simp add: inside_range_def)
   apply (rule not_is_jump_branch_system_is_advancing_instr)
    apply (simp add: Inop_def)
   apply (simp add: Inop_def is_system_instr_def is_Itrap_def is_Irfe_def)
  apply clarsimp
 apply clarsimp
 apply (insert instr_list_content [where i="1" and l="Suc (Suc 0)" and ad="dpc d" and d="Step d"])
 apply clarsimp
apply clarsimp
apply (insert instr_list_content [where i="0" and l="Suc (Suc 0)" and ad="dpc d" and d="d"])
apply clarsimp
done

lemma beqz_nop_execution2_woi[rule_format]: "asm_executes_precondition_woi d rangee [ Ibeqz r dist, Inop ]
                                        \<longrightarrow> reg (gprs d) r = 0
                                        \<longrightarrow> asm_nat ((add_pc (dpc d + 4) dist) + 4) \<longrightarrow> asm_int dist \<longrightarrow> 0 \<le> int (dpc d) + 4 + dist
                                        \<longrightarrow> asm_executes_woi d rangee address_range 2 (add_pc (pcp d) dist) (d \<lparr> dpc := (add_pc (pcp d) dist), pcp := (add_pc (pcp d) dist) + 4 \<rparr>)"
apply clarsimp
apply (simp add: asm_executes_precondition_woi_def)
apply (simp add: asm_executes_woi_def)
apply clarsimp
apply (simp add: BigStep_decompose)
apply (subgoal_tac "current_instr d = Ibeqz r dist")
 apply (frule_tac d="d" in ASMcore_consis_current_instr, simp)
 apply (insert beqz_execution2 [where d="d" and r="r" and dist="dist"])
 apply clarsimp
 apply (insert asm_nat_monotonic [where x="add_pc (dpc d + 4) dist" and n="add_pc (dpc d + 4) dist + 4"])
 apply simp
 apply (subgoal_tac "current_instr (Step d) = Inop")
  apply (frule_tac d="d\<lparr>dpc := dpc d + 4, pcp := add_pc (dpc d + 4) dist\<rparr>" in ASMcore_consis_current_instr, simp)
  apply (simp add: nop_is_instr)
  apply (frule_tac d="d"  in ASMcore_consis_current_instr, simp)
  apply (insert nop_execution [where d="Step d" ])
  apply clarsimp
  apply (simp add: add_pc_plus)
  apply clarsimp
  apply (case_tac "t'=0")
   apply clarsimp
   apply (rule not_is_load_store_is_interrupt_free)
     apply (simp add: current_instr_def is_Itrap_def)
    apply simp
   apply simp
  apply (subgoal_tac "t'=1")
   apply clarsimp
   apply (rule conjI)
    apply (rule not_is_load_store_is_interrupt_free)
      apply (simp add: current_instr_def is_Itrap_def)
      apply (simp add: Inop_def)
     apply (simp add: dvd_add)
    apply (simp add: inside_range_def)
   apply (rule not_is_jump_branch_system_is_advancing_instr)
    apply (simp add: Inop_def)
   apply (simp add: Inop_def is_system_instr_def is_Itrap_def is_Irfe_def)
  apply clarsimp
 apply clarsimp
 apply (insert instr_list_content [where i="1" and l="Suc (Suc 0)" and ad="dpc d" and d="Step d"])
 apply clarsimp
apply clarsimp
apply (insert instr_list_content [where i="0" and l="Suc (Suc 0)" and ad="dpc d" and d="d"])
apply clarsimp
done

lemma bnez_nop_execution2_woi[rule_format]: "asm_executes_precondition_woi d rangee [ Ibnez r dist, Inop ]
                                        \<longrightarrow> reg (gprs d) r \<noteq> 0
                                        \<longrightarrow> asm_nat ((add_pc (dpc d + 4) dist) + 4) \<longrightarrow> asm_int dist \<longrightarrow> 0 \<le> int (dpc d) + 4 + dist
                                        \<longrightarrow> asm_executes_woi d rangee address_range 2 (add_pc (pcp d) dist) (d \<lparr> dpc := (add_pc (pcp d) dist), pcp := (add_pc (pcp d) dist) + 4 \<rparr>)"
apply clarsimp
apply (simp add: asm_executes_precondition_woi_def)
apply (simp add: asm_executes_woi_def)
apply clarsimp
apply (simp add: BigStep_decompose)
apply (subgoal_tac "current_instr d = Ibnez r dist")
 apply (frule_tac d="d"  in ASMcore_consis_current_instr, simp)
 apply (insert bnez_execution2 [where d="d"  and r="r" and dist="dist"])
 apply clarsimp
 apply (insert asm_nat_monotonic [where x="add_pc (dpc d + 4) dist" and n="add_pc (dpc d + 4) dist + 4"])
 apply simp
 apply (subgoal_tac "current_instr (Step d) = Inop")
  apply (frule_tac d="d\<lparr>dpc := dpc d + 4, pcp := add_pc (dpc d + 4) dist\<rparr>"  in ASMcore_consis_current_instr, simp)
  apply (simp add: nop_is_instr)
  apply (frule_tac d="d"  in ASMcore_consis_current_instr, simp)
  apply (insert nop_execution [where d="Step d " ])
  apply clarsimp
  apply (simp add: add_pc_plus)
  apply clarsimp
  apply (case_tac "t'=0")
   apply clarsimp
   apply (rule not_is_load_store_is_interrupt_free)
     apply (simp add: current_instr_def is_Itrap_def)
    apply simp
   apply simp
  apply (subgoal_tac "t'=1")
   apply clarsimp
   apply (rule conjI)
    apply (rule not_is_load_store_is_interrupt_free)
      apply (simp add: current_instr_def is_Itrap_def)
      apply (simp add: Inop_def)
     apply (simp add: dvd_add)
    apply (simp add: inside_range_def)
   apply (rule not_is_jump_branch_system_is_advancing_instr)
    apply (simp add: Inop_def)
   apply (simp add: Inop_def is_system_instr_def is_Itrap_def is_Irfe_def)
  apply clarsimp
 apply clarsimp
 apply (insert instr_list_content [where i="1" and l="Suc (Suc 0)" and ad="dpc d" and d="Step d"])
 apply clarsimp
apply clarsimp
apply (insert instr_list_content [where i="0" and l="Suc (Suc 0)" and ad="dpc d" and d="d"])
apply clarsimp
done

lemma is_not_branch_and_store_asm_executes_woi[rule_format]: "asm_executes_precondition_woi d rangee il
                                                             \<longrightarrow> il \<noteq> []
                                                             \<longrightarrow> list_all (\<lambda> i. is_not_branch_and_mem_access i \<and> \<not> is_Imovi2s i \<and> \<not> is_Itrap i) il
                                                             \<longrightarrow> list_all (\<lambda> i. \<not> is_system_instr i) il
                                                             \<longrightarrow> (\<exists> d'. asm_executes_woi d rangee address_range (length il) (dpc d + 4 * length il) d' \<and> mm d' = mm d)"
apply clarsimp
apply (simp add: asm_executes_precondition_woi_def)
apply clarsimp
apply (simp add: asm_executes_woi_def)
apply (subgoal_tac "asm_nat (dpc d + 4 * length il + 4)")
 apply (subgoal_tac "list_all is_not_branch_and_store il")
  apply (frule_tac n="length il"  in ASMcore_consis_BigStep, simp, simp)
   apply (simp add: list_all_iff)
  apply (frule_tac dpc_pcp_BigStep, simp, simp)
    apply (simp add: is_not_branch_and_store_list_def)
   apply simp
  apply clarsimp
  apply (rule conjI)
   (* is_interrupt_free *)
   apply (rule_tac n="length il" and t="t'"  in is_not_branch_and_mem_access_is_interrupt_free_BigStep, simp, simp, simp)
      apply (simp add: asm_execute_precondition_woi_inside_range2)
     apply (simp add: asm_execute_precondition_woi_inside_range1)
    apply (simp add: list_all_iff)
   apply simp
  (* advancing_instr *)
  apply (rule_tac n="length il" and t="t'"  in not_is_jump_branch_system_store_is_advancing_instr_BigStep, simp+)
   apply (simp add: list_all_iff)
  apply simp
 apply (simp add: is_not_branch_and_mem_access_def)
 apply (simp add: list_all_iff) 
apply (simp add: inside_range_def)
apply (simp add: asm_nat_def)
apply (simp add: word_range_to_byte_def)
apply arith
done

lemma add_execution_woi[rule_format]: "asm_executes_precondition_woi d rangee [Iadd dr sr1 sr2] 
                                         \<longrightarrow> asm_executes_woi d rangee address_range 1 (dpc d + 4) (d \<lparr> dpc := dpc d + 4,
                                                                                     pcp := pcp d + 4,
                                                                                     gprs := (gprs d) [ dr := int_add (reg (gprs d) sr1) (reg (gprs d) sr2)] \<rparr>)"
apply clarsimp
apply (simp add: asm_executes_precondition_woi_def)
apply (simp add: asm_executes_woi_def)
apply clarsimp
apply (subgoal_tac "current_instr d = Iadd dr sr1 sr2")
 apply (subgoal_tac "Step d = d\<lparr>dpc := dpc d + 4, pcp := 8 + dpc d, gprs := gprs d[dr := int_add (reg (gprs d) sr1) (reg (gprs d) sr2)]\<rparr>")
  apply (frule_tac d="d"  in ASMcore_consis_current_instr, simp)
  apply clarsimp
  apply (simp add: not_is_load_store_is_interrupt_free is_Itrap_def)
 apply (simp add: Step_def)
 apply (simp add: current_instr_def)
 apply (simp add: arith_exec_def)
 apply (simp add: inc_pcs_st_def)
 apply (subgoal_tac "inc_pcp_by (dpc d + 4) (int wlen_byte) =  8 + dpc d")
  apply simp
 apply (simp add: word_range_to_byte_def)
 apply (subgoal_tac "0 \<le> wlen_byte")
  apply (frule_tac a="dpc d + 4" in inc_pcp_by_is_plus_positive2)
    apply (simp add: wlen_byte_def wlen_bit_def)
   apply (simp add: inside_range_def asm_nat_def)
   apply (simp add: wlen_byte_def)
  apply (simp add: wlen_byte_def)
 apply (simp add: wlen_byte_def)
apply (simp add: current_instr_def)
apply (simp add: get_instr_list_def instr_mem_read_def)
done

lemma sw_execution_woi[rule_format]: "asm_executes_precondition_woi d rangee [Isw RD rs imm] 
                                         \<longrightarrow> RD < 32
                                         \<longrightarrow> 4 dvd (intwd_as_nat (reg (gprs d) rs) + intwd_as_nat imm)
                                         \<longrightarrow> asm_nat (intwd_as_nat (reg (gprs d) rs) + intwd_as_nat imm)
                                         \<longrightarrow> range_contains address_range (intwd_as_nat (reg (gprs d) rs) + intwd_as_nat imm, 4)
                                         \<longrightarrow> \<not> inside_range (word_range_to_byte rangee) (intwd_as_nat (reg (gprs d) rs) + intwd_as_nat imm)
                                         \<longrightarrow> asm_executes_woi d rangee address_range 1 (dpc d + 4) (d 
                                                                               \<lparr> dpc := dpc d + 4,
                                                                                 pcp := pcp d + 4,
                                                                                 mm := data_mem_write (mm d) (intwd_as_nat (reg (gprs d) rs) + intwd_as_nat imm)
                                                                                                       (reg (gprs d) RD) \<rparr>)"
apply clarsimp
apply (simp add: asm_executes_precondition_woi_def asm_executes_woi_def)
apply clarsimp
apply (subgoal_tac "current_instr d = Isw RD rs imm")
 apply (subgoal_tac "Step d = d\<lparr>dpc := dpc d + 4, pcp := 8 + dpc d, mm := data_mem_write (mm d) (intwd_as_nat (reg (gprs d) rs) + intwd_as_nat imm) (reg (gprs d) RD)\<rparr>")
  apply (frule_tac d="d"  in ASMcore_consis_current_instr, simp)
  apply clarsimp
  apply (subgoal_tac "\<not> inside_range (fst (word_range_to_byte rangee), snd (word_range_to_byte rangee)) (intwd_as_nat (reg (gprs d) rs) + intwd_as_nat imm)")
   apply (frule_tac m="mm d" and d="reg (gprs d) RD" in data_mem_write_mem_unchanged2, (simp add: word_range_to_byte_def)+)
   apply (simp add: is_interrupt_free_def)
   apply (rule conjI)
    (* no instruction misalignment *)
    apply (simp add: not_imal_in_ASM_def)
   apply (rule conjI)
    (* no data misalignment *)
    apply (simp add: not_dmal_in_ASM_def)
    apply (simp add: load_store_target_def)
    apply (simp add: asm_nat_impl_fit_nat)
   apply (rule conjI)
    (* no access out of range *)
    apply (simp add: mem_access_inside_range_def)
    apply (simp add: range_contains_def)
    apply (clarsimp simp add: load_store_target_def)
    apply (simp add: asm_nat_impl_fit_nat)
   (* no write access to the code *)
   apply (simp add: is_Itrap_def)
   apply (simp add: no_mem_write_access_inside_code_def)
   using load_store_target_def[where d=d,symmetric, simplified]
   apply (simp add: asm_nat_impl_fit_nat)
   apply (simp add: inside_range_def)
   apply (simp add: is_store_def)
   apply (simp add: word_range_to_byte_def)
   apply clarsimp
   apply (simp add: dvd_def)
   apply clarsimp
  apply (simp add: inside_range_def)
 apply (simp add: Step_def)
 apply (simp add: current_instr_def)
 apply (simp add: store_exec_def)
 apply (simp add: asm_nat_impl_fit_nat)
 apply (simp add: inc_pcs_st_def)
 apply (frule_tac y="RD" and x="intwd_as_nat (reg (gprs d) rs) + intwd_as_nat imm" in correct_store_to_mem_word2, simp)
 apply (subgoal_tac "(intwd_as_nat (reg (gprs d) rs) + intwd_as_nat imm) mod 4 = 0")
  apply clarsimp
  apply (rename_tac q)
  apply (simp add: data_mem_write_def)
  apply (subgoal_tac "inc_pcp_by (dpc d + 4) (int wlen_byte) =  8 + dpc d")
   apply simp
  apply (simp add: word_range_to_byte_def)
  apply (subgoal_tac "0 \<le> wlen_byte")
   apply (frule_tac a="dpc d + 4" in inc_pcp_by_is_plus_positive2)
     apply (simp add: wlen_byte_def wlen_bit_def)
    apply (simp add: inside_range_def asm_nat_def)
    apply (simp add: wlen_byte_def)
   apply (simp add: wlen_byte_def)
  apply (simp add: wlen_byte_def)
 apply (simp add: dvd_impl_mod_zero)
apply (simp add: current_instr_def)
apply (simp add: get_instr_list_def instr_mem_read_def)
done

lemma jal_sw_execution_woi[rule_format]: "asm_executes_precondition_woi d rangee [Ijal dist, Isw GPR_ret rs imm]
                                       \<longrightarrow> rs \<noteq> GPR_ret
                                       \<longrightarrow> 4 dvd (intwd_as_nat (reg (gprs d) rs) + intwd_as_nat imm)
                                       \<longrightarrow> asm_nat (intwd_as_nat (reg (gprs d) rs) + intwd_as_nat imm)
                                       \<longrightarrow> range_contains address_range (intwd_as_nat (reg (gprs d) rs) + intwd_as_nat imm, 4)
                                       \<longrightarrow> \<not> inside_range (word_range_to_byte rangee) (intwd_as_nat (reg (gprs d) rs) + intwd_as_nat imm)
                                       \<longrightarrow> 0 \<le> int (dpc d) + dist + 4
                                       \<longrightarrow> inside_range (word_range_to_byte rangee) (add_pc (dpc d + 4) dist)
                                       \<longrightarrow> asm_nat ((add_pc (dpc d + 4) dist) + 4)
                                       \<longrightarrow> asm_executes_woi d rangee address_range 2 (add_pc (dpc d + 4) dist) (d 
                                                                               \<lparr> dpc := add_pc (dpc d + 4) dist,
                                                                                 pcp := add_pc (pcp d + 4) dist,
                                                                                 gprs := gprs d [ GPR_ret := natwd_as_int (dpc d + 8)],
                                                                                 mm := data_mem_write (mm d) (intwd_as_nat (reg (gprs d) rs) + intwd_as_nat imm)
                                                                                                                      (natwd_as_int (dpc d + 8)) \<rparr>)"
apply clarsimp
apply (simp add: asm_executes_precondition_woi_def asm_executes_woi_def)
apply clarsimp
apply (simp add: BigStep_diff_1)
apply (subgoal_tac "add_pc (8 + dpc d) dist = add_pc (dpc d + 4) dist + 4")
 apply clarsimp
 apply (subgoal_tac "current_instr d = Ijal dist")
  apply (subgoal_tac "current_instr (Step d) = Isw GPR_ret rs imm")
   apply (subgoal_tac "is_interrupt_free (Step d) rangee address_range")
    apply (subgoal_tac "Step (Step d) = d
       \<lparr>dpc := add_pc (dpc d + 4) dist, pcp := add_pc (dpc d + 4) dist + 4, gprs := gprs d[GPR_ret := natwd_as_int (dpc d + 8)],
          mm := data_mem_write (mm d) (intwd_as_nat (reg (gprs d) rs) + intwd_as_nat imm) (natwd_as_int (dpc d + 8))\<rparr>")
     apply clarsimp
     apply (frule_tac d="d"  in ASMcore_consis_current_instr, simp)
     apply (frule_tac d="Step d"  in ASMcore_consis_current_instr, simp)
     apply clarsimp
     apply (subgoal_tac "\<not> inside_range (fst (word_range_to_byte rangee), snd (word_range_to_byte rangee)) (intwd_as_nat (reg (gprs d) rs) + intwd_as_nat imm)")
      apply (frule_tac m="mm d" and d="natwd_as_int (dpc d + 8)" in data_mem_write_mem_unchanged2)
         apply (simp add: word_range_to_byte_def)
        apply (simp add: word_range_to_byte_def)
       apply simp
      apply (case_tac "t'=0")
       apply clarsimp
       apply (rule not_is_load_store_is_interrupt_free)
         apply (simp add: current_instr_def is_Itrap_def)
        apply simp
       apply simp
      apply (subgoal_tac "t'=1")
       apply clarsimp
      apply clarsimp
     apply (simp add: inside_range_def)
    apply (frule_tac d="d"  in ASMcore_consis_current_instr, simp)
    apply (simp add: Step_def)
    apply (simp add: current_instr_def)
    apply (simp add: store_exec_def)
    apply (subgoal_tac "reg (gprs d[GPR_ret := natwd_as_int (inc_pcp_by (dpc d + 4) 4)]) rs = reg (gprs d) rs")
     apply (simp add: asm_nat_impl_fit_nat)
     apply (simp add: inc_pcs_st_def)
     apply (frule_tac d="d\<lparr>dpc := dpc d + 4, pcp := inc_pcp_by (dpc d + 4) dist, gprs := gprs d[GPR_ret := natwd_as_int (inc_pcp_by (dpc d + 4) 4)]\<rparr>" and y="GPR_ret" and x="intwd_as_nat (reg (gprs d) rs) + intwd_as_nat imm" in correct_store_to_mem_word)
      apply (simp add: GPR_ret_def)
     apply (subgoal_tac "(intwd_as_nat (reg (gprs d) rs) + intwd_as_nat imm) mod 4 = 0")
      apply clarsimp
      apply (rename_tac q)
      apply (simp add: GPR_ret_def)
      apply (simp add: data_mem_write_def)
      apply (subgoal_tac "inc_pcp_by (dpc d + 4) 4 = dpc d + 8")
       apply simp
       apply (subgoal_tac "inc_pcp_by (dpc d + 4) dist = add_pc (dpc d + 4) dist")
        apply clarsimp
        apply (subgoal_tac "inc_pcp_by (add_pc (dpc d + 4) dist) (int wlen_byte) = add_pc (dpc d + 4) dist + 4")
         apply clarsimp
         apply (simp add: is_ASMcore_def)
        apply (subgoal_tac "0 \<le> wlen_byte")
         apply (frule_tac a="add_pc (dpc d + 4) dist" in inc_pcp_by_is_plus_positive2)
           apply (simp add: wlen_byte_def wlen_bit_def)
          apply (simp add: inside_range_def asm_nat_def)
          apply (simp add: wlen_byte_def)
         apply (simp add: wlen_byte_def)
        apply (simp add: wlen_byte_def)
       apply (subgoal_tac "asm_int dist")
        apply (frule_tac x="dist" and p="dpc d + 4" in  inc_pcp_by_is_add_pc)
           apply (simp add: is_ASMcore_def)
          apply simp
         apply (simp add: inside_range_def asm_nat_def)
        apply simp
       apply (simp add: is_instr_def)
       apply clarsimp
       apply (simp add: asm_imm26_impl_asm_int)
      apply (subgoal_tac "0 \<le> (4::nat)")
       apply (frule_tac a="dpc d + 4" in inc_pcp_by_is_plus_positive2)
         apply (simp add: wlen_bit_def)
        apply clarsimp
        apply (simp add: inside_range_def asm_nat_def)
        apply (simp add: word_range_to_byte_def)
       apply simp
      apply simp
     apply (simp add: dvd_impl_mod_zero)
    apply (case_tac rs)
     apply simp
    apply simp
   apply (simp add: Step_def)
   apply (simp add: is_interrupt_free_def)
   apply (subgoal_tac "reg (gprs d[GPR_ret := natwd_as_int (inc_pcp_by (dpc d + 4) 4)]) rs = reg (gprs d) rs")
    apply (rule conjI)
     (* no instruction misalignment *)
     apply (simp add: not_imal_in_ASM_def)
     apply (simp add: dvd_add)
    apply (rule conjI)
     (* no data misalignment *)
     apply (simp add: not_dmal_in_ASM_def)
     apply (simp add: load_store_target_def)
     apply (simp add: asm_nat_impl_fit_nat)
    apply (rule conjI)
     (* no access out of range *)
     apply (simp add: mem_access_inside_range_def)
     apply (simp add: load_store_target_def)
     apply (simp add: range_contains_def)
     apply (simp add: asm_nat_impl_fit_nat)
    apply (rule conjI)
     (* no write access to the code *)
    apply (simp add: no_mem_write_access_inside_code_def)
    apply (simp add: load_store_target_def)
    apply (simp add: asm_nat_impl_fit_nat)
    apply (simp add: inside_range_def)
    apply (simp add: is_store_def)
    apply (simp add: word_range_to_byte_def)
    apply clarsimp
    apply (simp add: dvd_def)
    apply clarsimp+
    (* dpc is in range *)
    apply (simp add: inside_range_def is_Itrap_def)
   apply (simp add: reg_def)
  apply (simp add: Step_def)
  apply (simp add: current_instr_def)
  apply (simp add: get_instr_list_def instr_mem_read_def)
  apply (subgoal_tac "(dpc d + 4) div 4 = dpc d div 4 + 1")
   apply simp
  apply simp
  apply arith
 apply (simp add: current_instr_def)
 apply (simp add: get_instr_list_def instr_mem_read_def)
apply (case_tac "dist < 0")
 apply (simp add: add_pc_minus)
 apply arith+
apply (simp add: add_pc_plus)
sorry

declare word_range_to_byte_def[simp]

lemma lw_execution_woi[rule_format]: "asm_executes_precondition_woi d rangee [Ilw RD rs imm] 
                                         \<longrightarrow> 4 dvd (intwd_as_nat (reg (gprs d) rs) + intwd_as_nat imm)
                                         \<longrightarrow> asm_nat (intwd_as_nat (reg (gprs d) rs) + intwd_as_nat imm)
                                         \<longrightarrow> range_contains address_range (intwd_as_nat (reg (gprs d) rs) + intwd_as_nat imm, 4)
                                         \<longrightarrow> asm_executes_woi d rangee address_range 1 (dpc d + 4) (d 
                                                                               \<lparr> dpc := dpc d + 4,
                                                                                 pcp := pcp d + 4,
                                                                                 gprs := gprs d [ RD := data_mem_read (mm d) (intwd_as_nat (reg (gprs d) rs) + intwd_as_nat imm)]
                                                                               \<rparr>)"
apply clarsimp
apply (simp add: asm_executes_precondition_woi_def asm_executes_woi_def)
apply clarsimp
apply (subgoal_tac "current_instr d = Ilw RD rs imm")
 apply (subgoal_tac "Step d = d\<lparr>dpc := dpc d + 4, pcp := 8 + dpc d, gprs := gprs d [ RD := data_mem_read (mm d) (intwd_as_nat (reg (gprs d) rs) + intwd_as_nat imm)]\<rparr>")
  apply (frule_tac d="d"  in ASMcore_consis_current_instr, simp)
  apply clarsimp
  apply (simp add: is_interrupt_free_def)
  apply (rule conjI)
   (* no instruction misalignment *)
   apply (simp add: not_imal_in_ASM_def)
  apply (rule conjI)
   (* no data misalignment *)
   apply (simp add: not_dmal_in_ASM_def)
   apply (simp add: load_store_target_def)
   apply (simp add: asm_nat_impl_fit_nat)
  apply (rule conjI)
   (* no access out of range *)
   apply (simp add: mem_access_inside_range_def)
   apply (simp add: range_contains_def)
   apply (clarsimp simp add: load_store_target_def)
   apply (simp add: asm_nat_impl_fit_nat)
  apply (simp add: no_mem_write_access_inside_code_def)
  apply (simp add: is_store_def is_Itrap_def)
 apply (simp add: Step_def)
 apply (simp add: current_instr_def)
 apply (simp add: load_exec_def)
 apply (simp add: asm_nat_impl_fit_nat)
 apply (simp add: inc_pcs_st_def)
 apply (frule_tac x="intwd_as_nat (reg (gprs d) rs) + intwd_as_nat imm" in correct_load_from_mem_word)
 apply (subgoal_tac "(intwd_as_nat (reg (gprs d) rs) + intwd_as_nat imm) mod 4 = 0")
  apply clarsimp
  apply (rename_tac q)
  apply (simp add: data_mem_read_def)
  apply (subgoal_tac "inc_pcp_by (dpc d + 4) (int wlen_byte) =  8 + dpc d")
   apply simp
  apply (subgoal_tac "0 \<le> wlen_byte")
   apply (frule_tac a="dpc d + 4" in inc_pcp_by_is_plus_positive2)
     apply (simp add: wlen_byte_def wlen_bit_def)
    apply (simp add: inside_range_def asm_nat_def)
    apply (simp add: wlen_byte_def)
   apply (simp add: wlen_byte_def)
  apply (simp add: wlen_byte_def)
 apply (simp add: dvd_impl_mod_zero)
apply (simp add: current_instr_def)
apply (simp add: get_instr_list_def instr_mem_read_def)
sorry

lemma jr_nop_execution_woi[rule_format]: "asm_executes_precondition_woi d rangee [Ijr r, Inop]
                                        \<longrightarrow> asm_nat (intwd_as_nat (reg (gprs d) r) + 4)
                                        \<longrightarrow> asm_executes_woi d rangee address_range 2 (intwd_as_nat (reg (gprs d) r)) (d \<lparr> dpc := intwd_as_nat (reg (gprs d) r), pcp := intwd_as_nat (reg (gprs d) r) + 4 \<rparr>)"
apply clarsimp
apply (simp add: asm_executes_precondition_woi_def)
apply (simp add: asm_executes_woi_def)
apply clarsimp
apply (simp add: BigStep_decompose)
apply (subgoal_tac "current_instr d = Ijr r")
 apply (frule_tac d="d"  in ASMcore_consis_current_instr, simp)
 apply (insert jr_execution [where d="d"  and r="r"])
 apply clarsimp
 apply (subgoal_tac "current_instr (Step d) = Inop")
  apply (frule_tac d="d\<lparr>dpc := dpc d + 4, pcp := intwd_as_nat (reg (gprs d) r)\<rparr>"  in ASMcore_consis_current_instr, simp)
  apply (simp add: nop_is_instr)
  apply (frule_tac d="d"  in ASMcore_consis_current_instr, simp)
  apply (insert nop_execution [where d="Step d" ])
  apply clarsimp
  apply (simp add: add_pc_plus)
  apply clarsimp
  apply (case_tac "t'=0")
   apply clarsimp
   apply (rule not_is_load_store_is_interrupt_free)
     apply (simp add: current_instr_def is_Itrap_def)
    apply simp
   apply simp
  apply (subgoal_tac "t'=1")
   apply clarsimp
   apply (rule conjI)
    apply (rule not_is_load_store_is_interrupt_free)
      apply (simp add: current_instr_def is_Itrap_def)
      apply (simp add: Inop_def)
     apply (simp add: dvd_add)
    apply (simp add: inside_range_def)
   apply (rule not_is_jump_branch_system_is_advancing_instr)
    apply (simp add: Inop_def)
   apply (simp add: Inop_def is_system_instr_def is_Itrap_def is_Irfe_def)
  apply simp
 apply clarsimp
 apply (insert instr_list_content [where i="1" and l="Suc (Suc 0)" and ad="dpc d" and d="Step d"])
 apply clarsimp
apply clarsimp
apply (insert instr_list_content [where i="0" and l="Suc (Suc 0)" and ad="dpc d" and d="d"])
apply clarsimp
done

lemma addi_execution_woi[rule_format]: "asm_executes_precondition_woi d rangee [Iaddi dr sr i] 
                                         \<longrightarrow> asm_executes_woi d rangee address_range 1 (dpc d + 4) (d \<lparr> dpc := dpc d + 4,
                                                                                     pcp := pcp d + 4,
                                                                                     gprs := (gprs d) [ dr := int_add (reg (gprs d) sr) i] \<rparr>)"
apply clarsimp
apply (simp add: asm_executes_precondition_woi_def)
apply (simp add: asm_executes_woi_def)
apply clarsimp
apply (subgoal_tac "current_instr d = Iaddi dr sr i")
 apply (subgoal_tac "Step d = d\<lparr>dpc := dpc d + 4, pcp := 8 + dpc d, gprs := gprs d[dr := int_add (reg (gprs d) sr) i]\<rparr>")
  apply (frule_tac d="d"  in ASMcore_consis_current_instr, simp)
  apply clarsimp
  apply (rule not_is_load_store_is_interrupt_free)
    apply (simp add: current_instr_def is_Itrap_def)
   apply simp
  apply simp
 apply (simp add: Step_def)
 apply (simp add: current_instr_def)
 apply (simp add: arith_exec_def)
 apply (simp add: inc_pcs_st_def)
 apply (subgoal_tac "inc_pcp_by (dpc d + 4) (int wlen_byte) =  8 + dpc d")
  apply simp
 apply (subgoal_tac "0 \<le> wlen_byte")
  apply (frule_tac a="dpc d + 4" in inc_pcp_by_is_plus_positive2)
    apply (simp add: wlen_byte_def wlen_bit_def)
   apply (simp add: inside_range_def asm_nat_def)
   apply (simp add: wlen_byte_def)
  apply (simp add: wlen_byte_def)
 apply (simp add: wlen_byte_def)
apply (simp add: current_instr_def)
apply (simp add: get_instr_list_def instr_mem_read_def)
done

lemma subi_execution_woi[rule_format]: "asm_executes_precondition_woi d rangee [Isubi dr sr i] 
                                         \<longrightarrow> asm_executes_woi d rangee addr_range 1 (dpc d + 4) (d \<lparr> dpc := dpc d + 4,
                                                                                     pcp := pcp d + 4,
                                                                                     gprs := (gprs d) [ dr := int_sub (reg (gprs d) sr) i] \<rparr>)"
apply clarsimp
apply (simp add: asm_executes_precondition_woi_def)
apply (simp add: asm_executes_woi_def)
apply clarsimp
apply (subgoal_tac "current_instr d = Isubi dr sr i")
 apply (subgoal_tac "Step d = d\<lparr>dpc := dpc d + 4, pcp := 8 + dpc d, gprs := gprs d[dr := int_sub (reg (gprs d) sr) i]\<rparr>")
  apply (frule_tac d="d"  in ASMcore_consis_current_instr, simp)
  apply clarsimp
  apply (rule not_is_load_store_is_interrupt_free)
    apply (simp add: current_instr_def is_Itrap_def)
   apply simp
  apply simp
 apply (simp add: Step_def)
 apply (simp add: current_instr_def)
 apply (simp add: arith_exec_def)
 apply (simp add: inc_pcs_st_def)
 apply (subgoal_tac "inc_pcp_by (dpc d + 4) (int wlen_byte) =  8 + dpc d")
  apply simp
 apply (subgoal_tac "0 \<le> wlen_byte")
  apply (frule_tac a="dpc d + 4" in inc_pcp_by_is_plus_positive2)
    apply (simp add: wlen_byte_def wlen_bit_def)
   apply (simp add: inside_range_def asm_nat_def)
   apply (simp add: wlen_byte_def)
  apply (simp add: wlen_byte_def)
 apply (simp add: wlen_byte_def)
apply (simp add: current_instr_def)
apply (simp add: get_instr_list_def instr_mem_read_def)
done

lemma beqz_addi_execution1_woi[rule_format]: "asm_executes_precondition_woi d rangee [Ibeqz r dist, Iaddi dr sr i]
                                            \<longrightarrow> reg (gprs d) r \<noteq> 0
                                            \<longrightarrow> asm_nat (add_pc (pcp d) 8)
                                            \<longrightarrow> asm_executes_woi d rangee address_range 2 (pcp d + 4) (d \<lparr> dpc := pcp d + 4,
                                                                                        pcp := pcp d + 8,
                                                                                        gprs := (gprs d) [ dr := int_add (reg (gprs d) sr) i]
                                                                                      \<rparr> )"
apply clarsimp
apply (simp add: asm_executes_precondition_woi_def)
apply (simp add: asm_executes_woi_def)
apply clarsimp
 apply (simp add: BigStep_decompose)
apply (subgoal_tac "current_instr d = Ibeqz r dist")
 apply (frule_tac d="d"  in ASMcore_consis_current_instr, simp)
 apply (insert beqz_execution1 [where d="d"  and r="r" and dist="dist"])
 apply clarsimp
 apply (simp add: add_pc_plus)
 apply (insert asm_nat_monotonic [where x="8 + dpc d" and n="12 + dpc d"])
 apply (simp add: nat_add_commute)
 apply (subgoal_tac "current_instr (Step d) = Iaddi dr sr i")
  apply (subgoal_tac "is_interrupt_free (Step d) rangee address_range")
   apply (frule_tac d="d\<lparr>dpc := dpc d + 4, pcp := dpc d + 8\<rparr>"  in ASMcore_consis_current_instr)
    apply (simp add: asm_executes_precondition_woi_def)
   apply clarsimp
   apply (simp add: Step_def)
   apply (simp add: arith_exec_def)
   apply (simp add: inc_pcs_st_def)
   apply (subgoal_tac "inc_pcp_by (8 + dpc d) (int wlen_byte) = 12 + dpc d")
    apply (simp add: nat_add_commute)
    apply clarsimp
    apply (case_tac "t'=0")
     apply clarsimp
     apply (rule not_is_load_store_is_interrupt_free)
       apply (simp add: is_Itrap_def)
      apply simp
     apply simp
    apply clarsimp
    apply (subgoal_tac "t'=1")
     apply clarsimp
     apply (simp add: Step_def)
     apply (simp add: inc_pcs_st_def)
    apply simp
   apply (subgoal_tac "0 \<le> wlen_byte")
    apply (frule_tac a="8 + dpc d" in inc_pcp_by_is_plus_positive2)
      apply (simp add: wlen_byte_def wlen_bit_def)
     apply (simp add: inside_range_def asm_nat_def)
     apply (simp add: wlen_byte_def)
    apply (simp add: wlen_byte_def)
   apply (simp add: wlen_byte_def)
  apply (rule not_is_load_store_is_interrupt_free, simp add: is_Itrap_def)
   apply (simp add: dvd_add)
  apply (simp add: inside_range_def)
 apply (insert instr_list_content [where i="1" and l="Suc (Suc 0)" and ad="dpc d" and d="Step d"])
 apply clarsimp
apply clarsimp
apply (insert instr_list_content [where i="0" and l="Suc (Suc 0)" and ad="dpc d" and d="d"])
apply clarsimp
done

lemma beqz_addi_execution2_woi[rule_format]: "asm_executes_precondition_woi d rangee [Ibeqz r dist, Iaddi dr sr i]
                                            \<longrightarrow> reg (gprs d) r = 0
                                            \<longrightarrow> asm_nat ((add_pc (dpc d + 4) dist) + 4)
                                            \<longrightarrow> asm_int dist
                                            \<longrightarrow> 0 \<le> int (dpc d) + 4 + dist
                                            \<longrightarrow> asm_executes_woi d rangee address_range 2 (add_pc (pcp d) dist) (d \<lparr> dpc := add_pc (pcp d) dist,
                                                                                        pcp := (add_pc (pcp d) dist) + 4,
                                                                                        gprs := (gprs d) [ dr := int_add (reg (gprs d) sr) i]
                                                                                      \<rparr> )"
apply clarsimp
apply (simp add: asm_executes_precondition_woi_def)
apply (simp add: asm_executes_woi_def)
apply clarsimp
apply (simp add: BigStep_decompose)
apply (subgoal_tac "current_instr d = Ibeqz r dist")
 apply (frule_tac d="d"  in ASMcore_consis_current_instr, simp)
 apply (insert beqz_execution2 [where d="d"  and r="r" and dist="dist"])
 apply clarsimp
 apply (insert asm_nat_monotonic [where x="add_pc (dpc d + 4) dist" and n="add_pc (dpc d + 4) dist + 4"])
 apply simp
 apply (subgoal_tac "current_instr (Step d) = Iaddi dr sr i")
  apply (frule_tac d="d\<lparr>dpc := dpc d + 4, pcp := add_pc (dpc d + 4) dist\<rparr>"  in ASMcore_consis_current_instr, simp)
  apply (frule_tac d="d"  in ASMcore_consis_current_instr, simp)
  apply (simp add: Step_def)
  apply (simp add: arith_exec_def)
  apply (simp add: inc_pcs_st_def)
  apply (subgoal_tac "inc_pcp_by (add_pc (dpc d + 4) dist) (int wlen_byte) = add_pc (dpc d + 4) dist + 4")
   apply clarsimp
   apply (case_tac "t'=0")
    apply clarsimp
    apply (rule not_is_load_store_is_interrupt_free)
      apply (simp add: is_Itrap_def)
     apply simp
    apply simp
   apply clarsimp
   apply (subgoal_tac "t'=1")
    apply clarsimp
    apply (simp add: Step_def)
    apply (rule not_is_load_store_is_interrupt_free)
      apply (simp add: current_instr_def is_Itrap_def)
     apply (simp add: dvd_add)
    apply (simp add: inside_range_def)
   apply simp
  apply (subgoal_tac "0 \<le> wlen_byte")
   apply (frule_tac a="add_pc (dpc d + 4) dist" in inc_pcp_by_is_plus_positive2)
     apply (simp add: wlen_byte_def wlen_bit_def)
    apply (simp add: inside_range_def asm_nat_def)
    apply (simp add: wlen_byte_def)
   apply (simp add: wlen_byte_def)
  apply (simp add: wlen_byte_def)
 apply clarsimp
 apply (insert instr_list_content [where i="1" and l="Suc (Suc 0)" and ad="dpc d" and d="Step d"])
 apply clarsimp
apply clarsimp
apply (insert instr_list_content [where i="0" and l="Suc (Suc 0)" and ad="dpc d" and d="d"])
apply clarsimp
done

lemma bnez_addi_execution1_woi[rule_format]: "asm_executes_precondition_woi d rangee [Ibnez r dist, Iaddi dr sr i]
                                            \<longrightarrow> reg (gprs d) r = 0
                                            \<longrightarrow> inside_range (word_range_to_byte rangee) (add_pc (dpc d) 4)
                                            \<longrightarrow> asm_nat (add_pc (pcp d) 8)
                                            \<longrightarrow> asm_executes_woi d rangee address_range 2 (pcp d + 4) (d \<lparr> dpc := pcp d + 4,
                                                                                        pcp := pcp d + 8,
                                                                                        gprs := (gprs d) [ dr := int_add (reg (gprs d) sr) i]
                                                                                      \<rparr> )"
apply clarsimp
apply (simp add: asm_executes_precondition_woi_def)
apply (simp add: asm_executes_woi_def)
apply clarsimp
 apply (simp add: BigStep_decompose)
apply (subgoal_tac "current_instr d = Ibnez r dist")
 apply (frule_tac d="d"  in ASMcore_consis_current_instr, simp)
 apply (insert bnez_execution1 [where d="d"  and r="r" and dist="dist"])
 apply clarsimp
 apply (simp add: add_pc_plus)
 apply (insert asm_nat_monotonic [where x="8 + dpc d" and n="12 + dpc d"])
 apply clarsimp
 apply (simp add: nat_add_commute)
 apply (subgoal_tac "current_instr (Step d) = Iaddi dr sr i")
  apply (frule_tac d="d\<lparr>dpc := dpc d + 4, pcp := dpc d + 8\<rparr>"  in ASMcore_consis_current_instr)
   apply (simp add: asm_executes_precondition_woi_def)
  apply clarsimp
  apply (simp add: Step_def)
  apply (simp add: arith_exec_def)
  apply (simp add: inc_pcs_st_def)
  apply (subgoal_tac "inc_pcp_by (8 + dpc d) (int wlen_byte) = 12 + dpc d")
  apply (simp add: nat_add_commute)
   apply clarsimp
   apply (case_tac "t'=0")
    apply clarsimp
    apply (rule not_is_load_store_is_interrupt_free)
      apply (simp add: is_Itrap_def)
     apply simp
    apply simp
   apply clarsimp
   apply (subgoal_tac "t'=1")
    apply clarsimp
    apply (simp add: Step_def)
    apply (simp add: inc_pcs_st_def)
    apply (rule not_is_load_store_is_interrupt_free)
      apply (simp add: current_instr_def is_Itrap_def)
     apply (simp add: dvd_add)
    apply (simp add: inside_range_def)
   apply simp
  apply (subgoal_tac "0 \<le> wlen_byte")
   apply (frule_tac a="8 + dpc d" in inc_pcp_by_is_plus_positive2)
     apply (simp add: wlen_byte_def wlen_bit_def)
    apply (simp add: inside_range_def asm_nat_def)
    apply (simp add: wlen_byte_def)
   apply (simp add: wlen_byte_def)
  apply (simp add: wlen_byte_def)
 apply (insert instr_list_content [where i="1" and l="Suc (Suc 0)" and ad="dpc d" and d="Step d"])
 apply clarsimp
apply clarsimp
apply (insert instr_list_content [where i="0" and l="Suc (Suc 0)" and ad="dpc d" and d="d"])
apply clarsimp
done

lemma bnez_addi_execution2_woi[rule_format]: "asm_executes_precondition_woi d rangee [Ibnez r dist, Iaddi dr sr i]
                                            \<longrightarrow> reg (gprs d) r \<noteq> 0
                                            \<longrightarrow> asm_nat ((add_pc (dpc d + 4) dist) + 4)
                                            \<longrightarrow> asm_int dist
                                            \<longrightarrow> 0 \<le> int (dpc d) + 4 + dist
                                            \<longrightarrow> asm_executes_woi d rangee address_range 2 (add_pc (pcp d) dist) (d \<lparr> dpc := add_pc (pcp d) dist,
                                                                                        pcp := (add_pc (pcp d) dist) + 4,
                                                                                        gprs := (gprs d) [ dr := int_add (reg (gprs d) sr) i]
                                                                                      \<rparr> )"
apply clarsimp
apply (simp add: asm_executes_precondition_woi_def)
apply (simp add: asm_executes_woi_def)
apply clarsimp
apply (simp add: BigStep_decompose)
apply (subgoal_tac "current_instr d = Ibnez r dist")
 apply (frule_tac d="d"  in ASMcore_consis_current_instr, simp)
 apply (insert bnez_execution2 [where d="d"  and r="r" and dist="dist"])
 apply clarsimp
 apply (insert asm_nat_monotonic [where x="add_pc (dpc d + 4) dist" and n="add_pc (dpc d + 4) dist + 4"])
 apply simp
 apply (subgoal_tac "current_instr (Step d) = Iaddi dr sr i")
  apply (frule_tac d="d\<lparr>dpc := dpc d + 4, pcp := add_pc (dpc d + 4) dist\<rparr>"  in ASMcore_consis_current_instr, simp)
  apply (frule_tac d="d"  in ASMcore_consis_current_instr, simp)
  apply (simp add: Step_def)
  apply (simp add: arith_exec_def)
  apply (simp add: inc_pcs_st_def)
  apply (subgoal_tac "inc_pcp_by (add_pc (dpc d + 4) dist) (int wlen_byte) = add_pc (dpc d + 4) dist + 4")
   apply clarsimp
   apply (case_tac "t'=0")
    apply clarsimp
    apply (rule not_is_load_store_is_interrupt_free)
      apply (simp add: is_Itrap_def)
     apply simp
    apply simp
   apply (subgoal_tac "t'=1")
    apply clarsimp
    apply (simp add: Step_def)
    apply (rule not_is_load_store_is_interrupt_free)
      apply (simp add: current_instr_def is_Itrap_def)
     apply (simp add: dvd_add)
    apply (simp add: inside_range_def)
   apply simp
  apply (subgoal_tac "0 \<le> wlen_byte")
   apply (frule_tac a="add_pc (dpc d + 4) dist" in inc_pcp_by_is_plus_positive2)
     apply (simp add: wlen_byte_def wlen_bit_def)
    apply (simp add: inside_range_def asm_nat_def)
    apply (simp add: wlen_byte_def)
   apply (simp add: wlen_byte_def)
  apply (simp add: wlen_byte_def)
 apply clarsimp
 apply (insert instr_list_content [where i="1" and l="Suc (Suc 0)" and ad="dpc d" and d="Step d"])
 apply clarsimp
apply clarsimp
apply (insert instr_list_content [where i="0" and l="Suc (Suc 0)" and ad="dpc d" and d="d"])
apply clarsimp
done

lemma andi_execution_woi[rule_format]: "asm_executes_precondition_woi d rangee [Iandi dr sr i]
                                         \<longrightarrow> asm_executes_woi d rangee address_range 1 (dpc d + 4) (d \<lparr> dpc := dpc d + 4,
                                                                                     pcp := pcp d + 4,
                                                                                     gprs := (gprs d) [ dr := s_and (reg (gprs d) sr) i ] \<rparr>)"
apply clarsimp
apply (simp add: asm_executes_precondition_woi_def)
apply (simp add: asm_executes_woi_def)
apply clarsimp
apply (subgoal_tac "current_instr d = Iandi dr sr i")
 apply (subgoal_tac "Step d = d\<lparr>dpc := dpc d + 4, pcp := 8 + dpc d, gprs := gprs d[dr := s_and (reg (gprs d) sr) i]\<rparr>")
  apply (frule_tac d="d"  in ASMcore_consis_current_instr, simp)
  apply clarsimp
  apply (simp add: not_is_load_store_is_interrupt_free is_Itrap_def)
 apply (simp add: Step_def)
 apply (simp add: arith_exec_def)
 apply (simp add: inc_pcs_st_def)
 apply (subgoal_tac "inc_pcp_by (dpc d + 4) (int wlen_byte) =  8 + dpc d")
  apply simp
 apply (subgoal_tac "0 \<le> wlen_byte")
  apply (frule_tac a="dpc d + 4" in inc_pcp_by_is_plus_positive2)
    apply (simp add: wlen_byte_def wlen_bit_def)
   apply (simp add: inside_range_def asm_nat_def)
   apply (simp add: wlen_byte_def)
  apply (simp add: wlen_byte_def)
 apply (simp add: wlen_byte_def)
apply (simp add: current_instr_def)
apply (simp add: get_instr_list_def instr_mem_read_def)
done

declare intwd_as_nat_0[simp del];
declare intwd_as_nat_4[simp del];
declare intwd_as_nat_8[simp del];
declare intwd_as_nat_12[simp del];

lemma xor_execution_woi[rule_format]: "asm_executes_precondition_woi d rangee [Ixor dr sr srr] 
                                         \<longrightarrow> asm_executes_woi d rangee address_range 1 (dpc d + 4) (d \<lparr> dpc := dpc d + 4,
                                                                                     pcp := pcp d + 4,
                                                                                     gprs := (gprs d) [dr := s_xor (reg (gprs d) sr) (reg (gprs d) srr)]\<rparr>)"
apply clarsimp
apply (simp add: asm_executes_precondition_woi_def)
apply (simp add: asm_executes_woi_def)
apply clarsimp
apply (subgoal_tac "current_instr d = Ixor dr sr srr")
  prefer 2
  apply (simp add: current_instr_def)
  apply (simp add: get_instr_list_def instr_mem_read_def)
apply (subgoal_tac "Step d = d\<lparr>dpc := dpc d + 4, pcp := 8 + dpc d, gprs := gprs d[dr := s_xor (reg (gprs d) sr) (reg (gprs d) srr)]\<rparr>")
  prefer 2
  apply (simp add: Step_def)
  apply (simp add: arith_exec_def)
  apply (simp add: inc_pcs_st_def)
  apply (subgoal_tac "inc_pcp_by (dpc d + 4) (int wlen_byte) =  8 + dpc d")
    prefer 2
    apply (subgoal_tac "0 \<le> wlen_byte")
      prefer 2
      apply (simp add: wlen_byte_def wlen_bit_def)
    apply (frule_tac a="dpc d + 4" in inc_pcp_by_is_plus_positive2)
      apply (simp add: inside_range_def asm_nat_def)
      apply (simp add: wlen_byte_def wlen_bit_def)
      apply (simp add: wlen_byte_def wlen_bit_def inside_range_def asm_nat_def)
    apply (simp add: wlen_byte_def)
  apply simp 
apply (frule_tac d="d"  in ASMcore_consis_current_instr, simp)
apply clarsimp
apply (simp add: not_is_load_store_is_interrupt_free is_Itrap_def)
done

lemma slli_execution_woi[rule_format]: "asm_executes_precondition_woi d rangee [Islli dr sr i]
  \<longrightarrow> asm_executes_woi d rangee address_range 1 (dpc d + 4) (d \<lparr> dpc := dpc d + 4, pcp := pcp d + 4, gprs := (gprs d) [dr := sllog (reg (gprs d) sr) (int i)]\<rparr>) "
apply clarsimp
apply (simp add: asm_executes_precondition_woi_def)
apply (simp add: asm_executes_woi_def)
apply clarsimp
apply (subgoal_tac "current_instr d = Islli dr sr i")
  prefer 2
  apply (simp add: current_instr_def)
  apply (simp add: get_instr_list_def instr_mem_read_def)
apply (subgoal_tac "Step d = d\<lparr>dpc := dpc d + 4, pcp := 8 + dpc d, gprs := gprs d[dr := sllog (reg (gprs d) sr) (int i)]\<rparr>")
  prefer 2
  apply (simp add: Step_def)
  apply (simp add: arith_exec_def)
  apply (simp add: inc_pcs_st_def)
  apply (subgoal_tac "inc_pcp_by (dpc d + 4) (int wlen_byte) =  8 + dpc d")
    prefer 2
    apply (subgoal_tac "0 \<le> wlen_byte")
      prefer 2
      apply (simp add: wlen_byte_def wlen_bit_def)
    apply (frule_tac a="dpc d + 4" in inc_pcp_by_is_plus_positive2)
      apply (simp add: inside_range_def asm_nat_def)
      apply (simp add: wlen_byte_def wlen_bit_def)
      apply (simp add: wlen_byte_def wlen_bit_def inside_range_def asm_nat_def)
    apply (simp add: wlen_byte_def)
  apply simp 
apply (frule_tac d="d"  in ASMcore_consis_current_instr, simp)
apply clarsimp
apply (simp add: not_is_load_store_is_interrupt_free is_Itrap_def)
done

lemma srl_execution_woi[rule_format]: "asm_executes_precondition_woi d rangee [Isrl dr srl srr]
  \<longrightarrow> asm_executes_woi d rangee addr_range 1 (dpc d + 4) (d \<lparr> dpc := dpc d + 4, pcp := pcp d + 4, gprs := (gprs d) [dr := srlog (reg (gprs d) srl) (reg (gprs d) srr)]\<rparr>)"
apply clarify
apply (simp add: asm_executes_precondition_woi_def)
apply (simp add: asm_executes_woi_def)
apply clarsimp
apply (subgoal_tac "current_instr d = (Isrl dr srl srr)")
  prefer 2
  apply (simp add: current_instr_def)
  apply (simp add: get_instr_list_def instr_mem_read_def)
apply (frule_tac d="d"  in ASMcore_consis_current_instr, simp)
apply (simp add: Step_def)
apply (simp add: arith_exec_def)
apply (simp add: inc_pcs_st_def)
apply (subgoal_tac "inc_pcp_by (dpc d + 4) (int wlen_byte) =  8 + dpc d")
  prefer 2
  apply (subgoal_tac "0 \<le> wlen_byte")
    prefer 2
    apply (simp add: wlen_byte_def wlen_bit_def)
  apply (frule_tac a="dpc d + 4" in inc_pcp_by_is_plus_positive2)
    apply (simp add: inside_range_def asm_nat_def)
    apply (simp add: wlen_byte_def wlen_bit_def)
    apply (simp add: wlen_byte_def wlen_bit_def inside_range_def asm_nat_def)
  apply (simp add: wlen_byte_def)
apply simp
apply (rule not_is_load_store_is_interrupt_free) 
 apply (simp add: current_instr_def is_Itrap_def)
apply simp
apply (simp add: inside_range_def)
done

lemma srli_execution_woi[rule_format]: "asm_executes_precondition_woi d rangee [Isrli dr sr i]
  \<longrightarrow> asm_executes_woi d rangee address_range 1 (dpc d + 4) (d \<lparr> dpc := dpc d + 4, pcp := pcp d + 4, gprs := (gprs d) [dr := srlog (reg (gprs d) sr) (int i)]\<rparr>) "
apply clarsimp
apply (simp add: asm_executes_precondition_woi_def)
apply (simp add: asm_executes_woi_def)
apply clarsimp
apply (subgoal_tac "current_instr d = Isrli dr sr i")
  prefer 2
  apply (simp add: current_instr_def)
  apply (simp add: get_instr_list_def instr_mem_read_def)
apply (subgoal_tac "Step d = d\<lparr>dpc := dpc d + 4, pcp := 8 + dpc d, gprs := gprs d[dr := srlog (reg (gprs d) sr) (int i)]\<rparr>")
  prefer 2
  apply (simp add: Step_def)
  apply (simp add: arith_exec_def)
  apply (simp add: inc_pcs_st_def)
  apply (subgoal_tac "inc_pcp_by (dpc d + 4) (int wlen_byte) =  8 + dpc d")
    prefer 2
    apply (subgoal_tac "0 \<le> wlen_byte")
      prefer 2
      apply (simp add: wlen_byte_def wlen_bit_def)
    apply (frule_tac a="dpc d + 4" in inc_pcp_by_is_plus_positive2)
      apply (simp add: inside_range_def asm_nat_def)
      apply (simp add: wlen_byte_def wlen_bit_def)
      apply (simp add: wlen_byte_def wlen_bit_def inside_range_def asm_nat_def)
    apply (simp add: wlen_byte_def)
  apply simp 
apply (frule_tac d="d"  in ASMcore_consis_current_instr, simp)
apply clarsimp
apply (simp add: not_is_load_store_is_interrupt_free is_Itrap_def)
done

lemma and_execution_woi[rule_format]: "asm_executes_precondition_woi d rangee [Iand dr srl srr]
                                         \<longrightarrow> asm_executes_woi d rangee address_range 1 (dpc d + 4) (d \<lparr> dpc := dpc d + 4,
                                                                                     pcp := pcp d + 4,
                                                                                     gprs := (gprs d)[dr := s_and (reg (gprs d) srl) (reg (gprs d) srr)]\<rparr>)"
apply clarify
apply (simp add: asm_executes_precondition_woi_def)
apply (simp add: asm_executes_woi_def)
apply clarsimp
apply (subgoal_tac "current_instr d = (Iand dr srl srr)")
  prefer 2
  apply (simp add: current_instr_def)
  apply (simp add: get_instr_list_def instr_mem_read_def)
apply (frule_tac d="d"  in ASMcore_consis_current_instr, simp)
apply (simp add: Step_def)
apply (simp add: arith_exec_def)
apply (simp add: inc_pcs_st_def)
apply (subgoal_tac "inc_pcp_by (dpc d + 4) (int wlen_byte) =  8 + dpc d")
  prefer 2
  apply (subgoal_tac "0 \<le> wlen_byte")
    prefer 2
    apply (simp add: wlen_byte_def wlen_bit_def)
  apply (frule_tac a="dpc d + 4" in inc_pcp_by_is_plus_positive2)
    apply (simp add: inside_range_def asm_nat_def)
    apply (simp add: wlen_byte_def wlen_bit_def)
    apply (simp add: wlen_byte_def wlen_bit_def inside_range_def asm_nat_def)
  apply (simp add: wlen_byte_def)
apply simp
apply (rule not_is_load_store_is_interrupt_free)
 apply (simp add: current_instr_def is_Itrap_def)
apply simp
apply (simp add: inside_range_def)
done

lemma or_execution_woi[rule_format]: "asm_executes_precondition_woi d rangee [Ior dr srl srr]
                                         \<longrightarrow> asm_executes_woi d rangee address_range 1 (dpc d + 4) (d \<lparr> dpc := dpc d + 4,
                                                                                     pcp := pcp d + 4,
                                                                                     gprs := (gprs d)[dr := s_or (reg (gprs d) srl) (reg (gprs d) srr)] \<rparr>)"
apply clarify
apply (simp add: asm_executes_precondition_woi_def)
apply (simp add: asm_executes_woi_def)
apply clarsimp
apply (subgoal_tac "current_instr d = (Ior dr srl srr)")
  prefer 2
  apply (simp add: current_instr_def)
  apply (simp add: get_instr_list_def instr_mem_read_def)
apply (frule_tac d="d"  in ASMcore_consis_current_instr, simp)
apply (simp add: Step_def)
apply (simp add: arith_exec_def)
apply (simp add: inc_pcs_st_def)
apply (subgoal_tac "inc_pcp_by (dpc d + 4) (int wlen_byte) =  8 + dpc d")
  prefer 2
  apply (subgoal_tac "0 \<le> wlen_byte")
    prefer 2
    apply (simp add: wlen_byte_def wlen_bit_def)
  apply (frule_tac a="dpc d + 4" in inc_pcp_by_is_plus_positive2)
    apply (simp add: inside_range_def asm_nat_def)
    apply (simp add: wlen_byte_def wlen_bit_def)
    apply (simp add: wlen_byte_def wlen_bit_def inside_range_def asm_nat_def)
  apply (simp add: wlen_byte_def)
apply simp
apply (rule not_is_load_store_is_interrupt_free)
 apply (simp add: current_instr_def is_Itrap_def)
apply simp
apply (simp add: inside_range_def)
done

lemma sll_execution_woi[rule_format]: "asm_executes_precondition_woi d rangee [Isll dr srl srr]
  \<longrightarrow> asm_executes_woi d rangee address_range 1 (dpc d + 4) (d \<lparr> dpc := dpc d + 4, pcp := pcp d + 4, gprs := (gprs d) [dr := sllog (reg (gprs d) srl) (reg (gprs d) srr)]\<rparr>) "
apply clarify
apply (simp add: asm_executes_precondition_woi_def)
apply (simp add: asm_executes_woi_def)
apply clarsimp
apply (subgoal_tac "current_instr d = (Isll dr srl srr)")
  prefer 2
  apply (simp add: current_instr_def)
  apply (simp add: get_instr_list_def instr_mem_read_def)
apply (frule_tac d="d"  in ASMcore_consis_current_instr, simp)
apply (simp add: Step_def)
apply (simp add: arith_exec_def)
apply (simp add: inc_pcs_st_def)
apply (subgoal_tac "inc_pcp_by (dpc d + 4) (int wlen_byte) =  8 + dpc d")
  prefer 2
  apply (subgoal_tac "0 \<le> wlen_byte")
    prefer 2
    apply (simp add: wlen_byte_def wlen_bit_def)
  apply (frule_tac a="dpc d + 4" in inc_pcp_by_is_plus_positive2)
    apply (simp add: inside_range_def asm_nat_def)
    apply (simp add: wlen_byte_def wlen_bit_def)
    apply (simp add: wlen_byte_def wlen_bit_def inside_range_def asm_nat_def)
  apply (simp add: wlen_byte_def)
apply simp
apply (rule not_is_load_store_is_interrupt_free) 
 apply (simp add: current_instr_def is_Itrap_def)
apply simp
apply (simp add: inside_range_def)
done

lemma sls_execution_1_woi[rule_format]: "asm_executes_precondition_woi d rangee [Isls dr srl srr]
\<longrightarrow> reg (gprs d) srl < reg (gprs d) srr 
\<longrightarrow> asm_executes_woi d rangee address_range 1 (dpc d + 4) (d \<lparr> dpc := dpc d + 4, pcp := pcp d + 4, gprs := (gprs d)[dr := 1]\<rparr>) "
apply clarify
apply (simp add: asm_executes_precondition_woi_def)
apply (simp add: asm_executes_woi_def)
apply clarsimp
apply (subgoal_tac "current_instr d = (Isls dr srl srr)")
  prefer 2
  apply (simp add: current_instr_def)
  apply (simp add: get_instr_list_def instr_mem_read_def)
apply (frule_tac d="d"  in ASMcore_consis_current_instr, simp)
apply (simp add: Step_def)
apply (simp add: comp_exec_def)  
apply (simp add: inc_pcs_st_def)
apply (subgoal_tac "inc_pcp_by (dpc d + 4) (int wlen_byte) =  8 + dpc d")
  prefer 2
  apply (subgoal_tac "0 \<le> wlen_byte")
    prefer 2
    apply (simp add: wlen_byte_def wlen_bit_def)
  apply (frule_tac a="dpc d + 4" in inc_pcp_by_is_plus_positive2)
    apply (simp add: inside_range_def asm_nat_def)
    apply (simp add: wlen_byte_def wlen_bit_def)
    apply (simp add: wlen_byte_def wlen_bit_def inside_range_def asm_nat_def)
  apply (simp add: wlen_byte_def)
apply simp
apply (rule not_is_load_store_is_interrupt_free) 
 apply (simp add: current_instr_def is_Itrap_def)
apply simp
apply (simp add: inside_range_def)
done

lemma sls_execution_0_woi[rule_format]: "asm_executes_precondition_woi d rangee [Isls dr srl srr]
\<longrightarrow> reg (gprs d) srl \<ge> reg (gprs d) srr 
\<longrightarrow> asm_executes_woi d rangee address_range 1 (dpc d + 4) (d \<lparr> dpc := dpc d + 4, pcp := pcp d + 4, gprs := (gprs d)[dr := 0]\<rparr>) "
apply clarify
apply (simp add: asm_executes_precondition_woi_def)
apply (simp add: asm_executes_woi_def)
apply clarsimp
apply (subgoal_tac "current_instr d = (Isls dr srl srr)")
  prefer 2
  apply (simp add: current_instr_def)
  apply (simp add: get_instr_list_def instr_mem_read_def)
apply (frule_tac d="d"  in ASMcore_consis_current_instr, simp)
apply (simp add: Step_def)
apply (simp add: comp_exec_def)  
apply (simp add: inc_pcs_st_def)
apply (subgoal_tac "inc_pcp_by (dpc d + 4) (int wlen_byte) =  8 + dpc d")
  prefer 2
  apply (subgoal_tac "0 \<le> wlen_byte")
    prefer 2
    apply (simp add: wlen_byte_def wlen_bit_def)
  apply (frule_tac a="dpc d + 4" in inc_pcp_by_is_plus_positive2)
    apply (simp add: inside_range_def asm_nat_def)
    apply (simp add: wlen_byte_def wlen_bit_def)
    apply (simp add: wlen_byte_def wlen_bit_def inside_range_def asm_nat_def)
  apply (simp add: wlen_byte_def)
apply simp
apply (rule not_is_load_store_is_interrupt_free) 
 apply (simp add: current_instr_def is_Itrap_def)
apply simp
apply (simp add: inside_range_def)
done

lemma sgei_execution_1_woi[rule_format]: "asm_executes_precondition_woi d rangee [Isgei dr sr i]
\<longrightarrow> reg (gprs d) sr \<ge> i
\<longrightarrow> asm_executes_woi d rangee address_range 1 (dpc d + 4) (d \<lparr> dpc := dpc d + 4, pcp := pcp d + 4, gprs := (gprs d)[dr := 1]\<rparr>) "
apply clarify
apply (simp add: asm_executes_precondition_woi_def)
apply (simp add: asm_executes_woi_def)
apply clarsimp
apply (subgoal_tac "current_instr d = (Isgei dr sr i)")
  prefer 2
  apply (simp add: current_instr_def)
  apply (simp add: get_instr_list_def instr_mem_read_def)
apply (frule_tac d="d"  in ASMcore_consis_current_instr, simp)
apply (simp add: Step_def)
apply (simp add: comp_exec_def)  
apply (simp add: inc_pcs_st_def)
apply (subgoal_tac "inc_pcp_by (dpc d + 4) (int wlen_byte) =  8 + dpc d")
  prefer 2
  apply (subgoal_tac "0 \<le> wlen_byte")
    prefer 2
    apply (simp add: wlen_byte_def wlen_bit_def)
  apply (frule_tac a="dpc d + 4" in inc_pcp_by_is_plus_positive2)
    apply (simp add: inside_range_def asm_nat_def)
    apply (simp add: wlen_byte_def wlen_bit_def)
    apply (simp add: wlen_byte_def wlen_bit_def inside_range_def asm_nat_def)
  apply (simp add: wlen_byte_def)
apply simp
apply (rule not_is_load_store_is_interrupt_free) 
 apply (simp add: current_instr_def is_Itrap_def)
apply simp
apply (simp add: inside_range_def)
done

declare split_if[split del]

lemma sgei_execution_0_woi[rule_format]: "asm_executes_precondition_woi d rangee [Isgei dr sr i]
\<longrightarrow> reg (gprs d) sr < i 
\<longrightarrow> asm_executes_woi d rangee address_range 1 (dpc d + 4) (d \<lparr> dpc := dpc d + 4, pcp := pcp d + 4, gprs := (gprs d)[dr := 0]\<rparr>) "
apply clarify
apply (simp add: asm_executes_precondition_woi_def)
apply (simp add: asm_executes_woi_def)
apply clarsimp
apply (subgoal_tac "current_instr d = (Isgei dr sr i)")
  prefer 2
  apply (simp add: current_instr_def)
  apply (simp add: get_instr_list_def instr_mem_read_def)
apply (frule_tac d="d"  in ASMcore_consis_current_instr, simp)
apply (simp add: Step_def)
apply (simp add: comp_exec_def)  
apply (simp add: inc_pcs_st_def)
apply (subgoal_tac "inc_pcp_by (dpc d + 4) (int wlen_byte) =  8 + dpc d")
  prefer 2
  apply (subgoal_tac "0 \<le> wlen_byte")
    prefer 2
    apply (simp add: wlen_byte_def wlen_bit_def)
  apply (frule_tac a="dpc d + 4" in inc_pcp_by_is_plus_positive2)
    apply (simp add: inside_range_def asm_nat_def)
    apply (simp add: wlen_byte_def wlen_bit_def)
    apply (simp add: wlen_byte_def wlen_bit_def inside_range_def asm_nat_def)
  apply (simp add: wlen_byte_def)
apply simp
apply (rule not_is_load_store_is_interrupt_free)
 apply (simp add: current_instr_def is_Itrap_def)
apply simp
apply (simp add: inside_range_def)
done

lemma seq_execution_woi[rule_format]: "asm_executes_precondition_woi d rangee [Iseq dr lr rr] 
                                    \<longrightarrow> asm_executes_woi d rangee address_range 1 (dpc d + 4) (d \<lparr> dpc := dpc d + 4,
                                                                                pcp := pcp d + 4,
                                                                                gprs := (gprs d) [dr := if (reg (gprs d) lr) = (reg (gprs d) rr) then 1 else 0]\<rparr>)"
apply clarsimp
apply (simp add: asm_executes_precondition_woi_def)
apply (simp add: asm_executes_woi_def)
apply clarsimp
apply (subgoal_tac "current_instr d = Iseq dr lr rr")
 prefer 2
 apply (simp add: current_instr_def)
 apply (simp add: get_instr_list_def instr_mem_read_def)
apply (subgoal_tac "Step d = d\<lparr>dpc := dpc d + 4, pcp := 8 + dpc d, gprs := gprs d[dr := if reg (gprs d) lr = reg (gprs d) rr then 1 else 0]\<rparr> ")
 prefer 2
 apply (simp add: Step_def)
 apply (simp add: comp_exec_def)
 apply (simp add: inc_pcs_st_def)
 apply (subgoal_tac "inc_pcp_by (dpc d + 4) (int wlen_byte) =  8 + dpc d")
  prefer 2
  apply (subgoal_tac "0 \<le> wlen_byte")
   prefer 2
   apply (simp add: wlen_byte_def wlen_bit_def)
  apply (frule_tac a="dpc d + 4" in inc_pcp_by_is_plus_positive2)
   apply (simp add: inside_range_def asm_nat_def)
   apply (simp add: wlen_byte_def wlen_bit_def)
   apply (simp add: wlen_byte_def wlen_bit_def inside_range_def asm_nat_def)
  apply (simp add: wlen_byte_def)
 apply clarsimp
apply (frule_tac d="d"  in ASMcore_consis_current_instr, simp)
apply clarsimp
apply (simp add: not_is_load_store_is_interrupt_free is_Itrap_def)
done

lemma sne_execution_woi[rule_format]: "asm_executes_precondition_woi d rangee [Isne dr lr rr] 
                                    \<longrightarrow> asm_executes_woi d rangee address_range 1 (dpc d + 4) (d \<lparr> dpc := dpc d + 4,
                                                                                pcp := pcp d + 4,
                                                                                gprs := (gprs d) [dr := if (reg (gprs d) lr) \<noteq> (reg (gprs d) rr) then 1 else 0]\<rparr>)"
apply clarsimp
apply (simp add: asm_executes_precondition_woi_def)
apply (simp add: asm_executes_woi_def)
apply clarsimp
apply (subgoal_tac "current_instr d = Isne dr lr rr")
 prefer 2
 apply (simp add: current_instr_def)
 apply (simp add: get_instr_list_def instr_mem_read_def)
apply (subgoal_tac "Step d = d\<lparr>dpc := dpc d + 4, pcp := 8 + dpc d, gprs := gprs d[dr := if reg (gprs d) lr \<noteq> reg (gprs d) rr then 1 else 0]\<rparr> ")
 prefer 2
 apply (simp add: Step_def)
 apply (simp add: comp_exec_def)
 apply (simp add: inc_pcs_st_def)
 apply (subgoal_tac "inc_pcp_by (dpc d + 4) (int wlen_byte) =  8 + dpc d")
  prefer 2
  apply (subgoal_tac "0 \<le> wlen_byte")
   prefer 2
   apply (simp add: wlen_byte_def wlen_bit_def)
  apply (frule_tac a="dpc d + 4" in inc_pcp_by_is_plus_positive2)
   apply (simp add: inside_range_def asm_nat_def)
   apply (simp add: wlen_byte_def wlen_bit_def)
   apply (simp add: wlen_byte_def wlen_bit_def inside_range_def asm_nat_def)
  apply (simp add: wlen_byte_def)
 apply clarsimp
apply (frule_tac d="d"  in ASMcore_consis_current_instr, simp)
apply clarsimp+
apply (simp add: not_is_load_store_is_interrupt_free is_Itrap_def)
sorry

lemma sle_execution_woi[rule_format]: "asm_executes_precondition_woi d rangee [Isle dr lr rr] 
                                    \<longrightarrow> asm_executes_woi d rangee address_range 1 (dpc d + 4) (d \<lparr> dpc := dpc d + 4,
                                                                                pcp := pcp d + 4,
                                                                                gprs := (gprs d) [dr := if (reg (gprs d) lr) \<le> (reg (gprs d) rr) then 1 else 0]\<rparr>)"
apply clarsimp
apply (simp add: asm_executes_precondition_woi_def)
apply (simp add: asm_executes_woi_def)
apply clarsimp
apply (subgoal_tac "current_instr d = Isle dr lr rr")
 prefer 2
 apply (simp add: current_instr_def)
 apply (simp add: get_instr_list_def instr_mem_read_def)
apply (subgoal_tac "Step d = d\<lparr>dpc := dpc d + 4, pcp := 8 + dpc d, gprs := gprs d[dr := if reg (gprs d) lr \<le> reg (gprs d) rr then 1 else 0]\<rparr> ")
 prefer 2
 apply (simp add: Step_def)
 apply (simp add: comp_exec_def)
 apply (simp add: inc_pcs_st_def)
 apply (subgoal_tac "inc_pcp_by (dpc d + 4) (int wlen_byte) =  8 + dpc d")
  prefer 2
  apply (subgoal_tac "0 \<le> wlen_byte")
   prefer 2
   apply (simp add: wlen_byte_def wlen_bit_def)
  apply (frule_tac a="dpc d + 4" in inc_pcp_by_is_plus_positive2)
   apply (simp add: inside_range_def asm_nat_def)
   apply (simp add: wlen_byte_def wlen_bit_def)
   apply (simp add: wlen_byte_def wlen_bit_def inside_range_def asm_nat_def)
  apply (simp add: wlen_byte_def)
 apply clarsimp
apply (frule_tac d="d"  in ASMcore_consis_current_instr, simp)
apply clarsimp
apply (simp add: not_is_load_store_is_interrupt_free is_Itrap_def)
done

lemma sls_execution_woi[rule_format]: "asm_executes_precondition_woi d rangee [Isls dr lr rr] 
                                    \<longrightarrow> asm_executes_woi d rangee address_range 1 (dpc d + 4) (d \<lparr> dpc := dpc d + 4,
                                                                                pcp := pcp d + 4,
                                                                                gprs := (gprs d) [dr := if (reg (gprs d) lr) < (reg (gprs d) rr) then 1 else 0]\<rparr>)"
apply clarsimp
apply (simp add: asm_executes_precondition_woi_def)
apply (simp add: asm_executes_woi_def)
apply clarsimp
apply (subgoal_tac "current_instr d = Isls dr lr rr")
 prefer 2
 apply (simp add: current_instr_def)
 apply (simp add: get_instr_list_def instr_mem_read_def)
apply (subgoal_tac "Step d = d\<lparr>dpc := dpc d + 4, pcp := 8 + dpc d, gprs := gprs d[dr := if reg (gprs d) lr < reg (gprs d) rr then 1 else 0]\<rparr> ")
 prefer 2
 apply (simp add: Step_def)
 apply (simp add: comp_exec_def)
 apply (simp add: inc_pcs_st_def)
 apply (subgoal_tac "inc_pcp_by (dpc d + 4) (int wlen_byte) =  8 + dpc d")
  prefer 2
  apply (subgoal_tac "0 \<le> wlen_byte")
   prefer 2
   apply (simp add: wlen_byte_def wlen_bit_def)
  apply (frule_tac a="dpc d + 4" in inc_pcp_by_is_plus_positive2)
   apply (simp add: inside_range_def asm_nat_def)
   apply (simp add: wlen_byte_def wlen_bit_def)
   apply (simp add: wlen_byte_def wlen_bit_def inside_range_def asm_nat_def)
  apply (simp add: wlen_byte_def)
 apply clarsimp
apply (frule_tac d="d"  in ASMcore_consis_current_instr, simp)
apply clarsimp
apply (simp add: not_is_load_store_is_interrupt_free is_Itrap_def)
done

lemma xori_execution_woi[rule_format]: "asm_executes_precondition_woi d rangee [Ixori dr sr i] 
                                     \<longrightarrow> asm_executes_woi d rangee addr_range 1 (dpc d + 4) (d \<lparr> dpc := dpc d + 4,
                                                                                            pcp := pcp d + 4,
                                                                                            gprs := (gprs d) [ dr := s_xor (reg (gprs d) sr) i] \<rparr>)"
apply clarsimp
apply (simp add: asm_executes_precondition_woi_def)
apply (simp add: asm_executes_woi_def)
apply clarsimp
apply (subgoal_tac "current_instr d = Ixori dr sr i")
 apply (subgoal_tac "Step d = d\<lparr>dpc := dpc d + 4, pcp := 8 + dpc d, gprs := gprs d[dr := s_xor (reg (gprs d) sr) i]\<rparr>")
  apply (frule_tac d="d"  in ASMcore_consis_current_instr, simp)
  apply clarsimp
  apply (rule not_is_load_store_is_interrupt_free)
    apply (simp add: current_instr_def is_Itrap_def)
   apply simp
  apply simp
 apply (simp add: Step_def)
 apply (simp add: arith_exec_def)
 apply (simp add: inc_pcs_st_def)
 apply (subgoal_tac "inc_pcp_by (dpc d + 4) (int wlen_byte) =  8 + dpc d")
  apply simp
 apply (subgoal_tac "0 \<le> wlen_byte")
  apply (frule_tac a="dpc d + 4" in inc_pcp_by_is_plus_positive2)
    apply (simp add: wlen_byte_def wlen_bit_def)
   apply (simp add: inside_range_def asm_nat_def)
   apply (simp add: wlen_byte_def)
  apply (simp add: wlen_byte_def)
 apply (simp add: wlen_byte_def)
apply (simp add: current_instr_def)
apply (simp add: get_instr_list_def instr_mem_read_def)
done

lemma ori_execution_woi[rule_format]: "asm_executes_precondition_woi d rangee [Iori dr sr i] 
                                     \<longrightarrow> asm_executes_woi d rangee addr_range 1 (dpc d + 4) (d \<lparr> dpc := dpc d + 4,
                                                                                            pcp := pcp d + 4,
                                                                                            gprs := (gprs d) [ dr := s_or (reg (gprs d) sr) i] \<rparr>)"
apply clarsimp
apply (simp add: asm_executes_precondition_woi_def)
apply (simp add: asm_executes_woi_def)
apply clarsimp
apply (subgoal_tac "current_instr d = Iori dr sr i")
 apply (subgoal_tac "Step d = d\<lparr>dpc := dpc d + 4, pcp := 8 + dpc d, gprs := gprs d[dr := s_or (reg (gprs d) sr) i]\<rparr>")
  apply (frule_tac d="d"  in ASMcore_consis_current_instr, simp)
  apply clarsimp
  apply (rule not_is_load_store_is_interrupt_free)
    apply (simp add: current_instr_def is_Itrap_def)
   apply simp
  apply simp
 apply (simp add: Step_def)
 apply (simp add: arith_exec_def)
 apply (simp add: inc_pcs_st_def)
 apply (subgoal_tac "inc_pcp_by (dpc d + 4) (int wlen_byte) =  8 + dpc d")
  apply simp
 apply (subgoal_tac "0 \<le> wlen_byte")
  apply (frule_tac a="dpc d + 4" in inc_pcp_by_is_plus_positive2)
    apply (simp add: wlen_byte_def wlen_bit_def)
   apply (simp add: inside_range_def asm_nat_def)
   apply (simp add: wlen_byte_def)
  apply (simp add: wlen_byte_def)
 apply (simp add: wlen_byte_def)
apply (simp add: current_instr_def)
apply (simp add: get_instr_list_def instr_mem_read_def)
done

lemma lhgi_execution_woi[rule_format]: "asm_executes_precondition_woi d rangee [Ilhgi dr i] 
                                     \<longrightarrow> asm_executes_woi d rangee addr_range 1 (dpc d + 4) (d \<lparr> dpc := dpc d + 4,
                                                                                            pcp := pcp d + 4,
                                                                                            gprs := (gprs d) [ dr := const_load_imm 0 i] \<rparr>)"
apply clarsimp
apply (simp add: asm_executes_precondition_woi_def)
apply (simp add: asm_executes_woi_def)
apply clarsimp
apply (subgoal_tac "current_instr d = Ilhgi dr i")
 apply (subgoal_tac "Step d = d\<lparr>dpc := dpc d + 4, pcp := 8 + dpc d, gprs := gprs d[dr := const_load_imm 0 i]\<rparr>")
  apply (frule_tac d="d"  in ASMcore_consis_current_instr, simp)
  apply clarsimp
  apply (rule not_is_load_store_is_interrupt_free)
    apply (simp add: current_instr_def is_Itrap_def)
   apply simp
  apply simp
 apply (simp add: Step_def)
 apply (simp add: arith_exec_def)
 apply (simp add: inc_pcs_st_def)
 apply (subgoal_tac "inc_pcp_by (dpc d + 4) (int wlen_byte) =  8 + dpc d")
  apply simp
 apply (subgoal_tac "0 \<le> wlen_byte")
  apply (frule_tac a="dpc d + 4" in inc_pcp_by_is_plus_positive2)
    apply (simp add: wlen_byte_def wlen_bit_def)
   apply (simp add: inside_range_def asm_nat_def)
   apply (simp add: wlen_byte_def)
  apply (simp add: wlen_byte_def)
 apply (simp add: wlen_byte_def)
apply (simp add: current_instr_def)
apply (simp add: get_instr_list_def instr_mem_read_def)
done

declare split_if[split]

lemma bnez_sll_execution1_woi[rule_format]: "asm_executes_precondition_woi d rangee [Ibnez r dist, Isll lr lr rr]
                                            \<longrightarrow> reg (gprs d) r \<noteq> 0
                                            \<longrightarrow> asm_nat ((add_pc (dpc d + 4) dist) + 4)
                                            \<longrightarrow> asm_int dist
                                            \<longrightarrow> 0 \<le> int (dpc d) + 4 + dist
                                            \<longrightarrow> asm_executes_woi d rangee addr_range 2 (add_pc (pcp d) dist) (d \<lparr> dpc := add_pc (pcp d) dist,
                                                                                        pcp := (add_pc (pcp d) dist) + 4,
                                                                                        gprs := (gprs d) [ lr := sllog (reg (gprs d) lr) (reg (gprs d) rr)]\<rparr>)"
apply clarsimp
apply (simp add: asm_executes_precondition_woi_def)
apply (simp add: asm_executes_woi_def)
apply clarsimp
apply (simp add: BigStep_decompose)
apply (subgoal_tac "current_instr d = Ibnez r dist")
  prefer 2
  apply (insert instr_list_content [where i="0" and l="Suc (Suc 0)" and ad="dpc d" and d="d"])
  apply clarsimp
apply (frule_tac d="d"  in ASMcore_consis_current_instr, simp)
apply (insert bnez_execution2 [where d="d"  and r="r" and dist="dist"])
apply clarsimp
apply (insert asm_nat_monotonic [where x="add_pc (dpc d + 4) dist" and n="add_pc (dpc d + 4) dist + 4"])
apply simp
apply (subgoal_tac "current_instr (Step d) = (Isll lr lr rr)")
  prefer 2
  apply clarsimp
  apply (insert instr_list_content [where i="1" and l="Suc (Suc 0)" and ad="dpc d" and d="Step d"])
  apply clarsimp
apply (frule_tac d="d\<lparr>dpc := dpc d + 4, pcp := add_pc (dpc d + 4) dist\<rparr>"  in ASMcore_consis_current_instr, simp)
apply (frule_tac d="d"  in ASMcore_consis_current_instr, simp)
apply (simp add: Step_def)
apply (simp add: arith_exec_def)
apply (simp add: inc_pcs_st_def)
apply (subgoal_tac "inc_pcp_by (add_pc (dpc d + 4) dist) (int wlen_byte) = add_pc (dpc d + 4) dist + 4")
  prefer 2 
  apply (subgoal_tac "0 \<le> wlen_byte")
    prefer 2  
    apply (simp add: wlen_byte_def)
  apply (frule_tac a="add_pc (dpc d + 4) dist" in inc_pcp_by_is_plus_positive2)
      apply (simp add: wlen_byte_def wlen_bit_def)
     apply (simp add: inside_range_def asm_nat_def)
     apply (simp add: wlen_byte_def)
  apply (simp add: wlen_byte_def)
apply clarsimp
apply (case_tac "t'=0")
 apply clarsimp
 apply (rule not_is_load_store_is_interrupt_free)
   apply (simp add: current_instr_def is_Itrap_def)
  apply simp
 apply simp
apply (subgoal_tac "t'=1")
 apply (simp add: Step_def)
 apply (rule not_is_load_store_is_interrupt_free)
   apply (simp add: current_instr_def is_Itrap_def)
  apply (simp add: dvd_add)
 apply (simp add: inside_range_def)
apply simp
done

lemma sub_execution_woi[rule_format]: "asm_executes_precondition_woi d rangee [Isub dr sr1 sr2] 
                                         \<longrightarrow> asm_executes_woi d rangee addr_range 1 (dpc d + 4) (d \<lparr> dpc := dpc d + 4,
                                                                                     pcp := pcp d + 4,
                                                                                     gprs := (gprs d) [ dr := int_sub (reg (gprs d) sr1) (reg (gprs d) sr2)] \<rparr>)"
apply clarsimp
apply (simp add: asm_executes_precondition_woi_def)
apply (simp add: asm_executes_woi_def)
apply clarsimp
apply (subgoal_tac "current_instr d = Isub dr sr1 sr2")
 apply (subgoal_tac "Step d = d\<lparr>dpc := dpc d + 4, pcp := 8 + dpc d, gprs := gprs d[dr := int_sub (reg (gprs d) sr1) (reg (gprs d) sr2)]\<rparr>")
  apply (frule_tac d="d"  in ASMcore_consis_current_instr, simp)
  apply clarsimp
  apply (rule not_is_load_store_is_interrupt_free)
    apply (simp add: current_instr_def is_Itrap_def)
   apply simp
  apply simp
 apply (simp add: Step_def)
 apply (simp add: arith_exec_def)
 apply (simp add: inc_pcs_st_def)
 apply (subgoal_tac "inc_pcp_by (dpc d + 4) (int wlen_byte) =  8 + dpc d")
  apply clarsimp
 apply (subgoal_tac "0 \<le> wlen_byte")
  apply (frule_tac a="dpc d + 4" in inc_pcp_by_is_plus_positive2)
    apply (simp add: wlen_byte_def wlen_bit_def)
   apply (simp add: inside_range_def asm_nat_def)
   apply (simp add: wlen_byte_def)
  apply (simp add: wlen_byte_def)
 apply (simp add: wlen_byte_def)
apply (simp add: current_instr_def)
apply (simp add: get_instr_list_def instr_mem_read_def)
done

lemma bnez_sub_execution1_woi[rule_format]: "asm_executes_precondition_woi d rangee [Ibnez r dist, Isub dr sr1 sr2]
                                            \<longrightarrow> reg (gprs d) r = 0
                                            \<longrightarrow> asm_nat (add_pc (pcp d) 8)
                                            \<longrightarrow> asm_executes_woi d rangee addr_range 2 (pcp d + 4) (d \<lparr> dpc := pcp d + 4,
                                                                                        pcp := pcp d + 8,
                                                                                        gprs := (gprs d) [ dr := int_sub (reg (gprs d) sr1) (reg (gprs d) sr2)]
                                                                                      \<rparr> )"
apply clarsimp
apply (simp add: asm_executes_precondition_woi_def)
apply (simp add: asm_executes_woi_def)
apply clarsimp
 apply (simp add: BigStep_decompose)
apply (subgoal_tac "current_instr d = Ibnez r dist")
 apply (frule_tac d="d"  in ASMcore_consis_current_instr, simp)
 apply (insert bnez_execution1 [where d="d"  and r="r" and dist="dist"])
 apply clarsimp
 apply (simp add: add_pc_plus)
 apply (insert asm_nat_monotonic [where x="8 + dpc d" and n="12 + dpc d"])
 apply clarsimp
 apply (simp add: nat_add_commute)
 apply (subgoal_tac "current_instr (Step d) = Isub dr sr1 sr2")
  apply (frule_tac d="d\<lparr>dpc := dpc d + 4, pcp := dpc d + 8\<rparr>"  in ASMcore_consis_current_instr)
   apply (simp add: asm_executes_precondition_woi_def)
  apply clarsimp
  apply (simp add: Step_def)
  apply (simp add: arith_exec_def)
  apply (simp add: inc_pcs_st_def)
  apply (subgoal_tac "inc_pcp_by (8 + dpc d) (int wlen_byte) = 12 + dpc d")
   apply (simp add: nat_add_commute)
   apply clarsimp
   apply (case_tac "t'=0")
    apply clarsimp
    apply (rule not_is_load_store_is_interrupt_free)
      apply (simp add: current_instr_def is_Itrap_def)
     apply simp
    apply simp
   apply (subgoal_tac "t'=1")
    apply (simp add: Step_def)
    apply (simp add: inc_pcs_st_def)
    apply (rule not_is_load_store_is_interrupt_free)
      apply (simp add: current_instr_def is_Itrap_def)
     apply (simp add: dvd_add)
    apply (simp add: inside_range_def)
   apply simp   
  apply (subgoal_tac "0 \<le> wlen_byte")
   apply (frule_tac a="8 + dpc d" in inc_pcp_by_is_plus_positive2)
     apply (simp add: wlen_byte_def wlen_bit_def)
    apply (simp add: inside_range_def asm_nat_def)
    apply (simp add: wlen_byte_def)
   apply (simp add: wlen_byte_def)
  apply (simp add: wlen_byte_def)
 apply (insert instr_list_content [where i="1" and l="Suc (Suc 0)" and ad="dpc d" and d="Step d"])
 apply clarsimp
apply clarsimp
apply (insert instr_list_content [where i="0" and l="Suc (Suc 0)" and ad="dpc d" and d="d"])
apply clarsimp
done

lemma bnez_sub_execution2_woi[rule_format]: "asm_executes_precondition_woi d rangee [Ibnez r dist, Isub dr sr1 sr2]
                                            \<longrightarrow> reg (gprs d) r \<noteq> 0
                                            \<longrightarrow> asm_nat ((add_pc (dpc d + 4) dist) + 4)
                                            \<longrightarrow> asm_int dist
                                            \<longrightarrow> 0 \<le> int (dpc d) + 4 + dist
                                            \<longrightarrow> asm_executes_woi d rangee addr_range 2 (add_pc (pcp d) dist) (d \<lparr> dpc := add_pc (pcp d) dist,
                                                                                        pcp := (add_pc (pcp d) dist) + 4,
                                                                                        gprs := (gprs d) [ dr := int_sub (reg (gprs d) sr1) (reg (gprs d) sr2)]
                                                                                      \<rparr> )"
apply clarsimp
apply (simp add: asm_executes_precondition_woi_def)
apply (simp add: asm_executes_woi_def)
apply clarsimp
apply (simp add: BigStep_decompose)
apply (subgoal_tac "current_instr d = Ibnez r dist")
 apply (frule_tac d="d"  in ASMcore_consis_current_instr, simp)
 apply (insert bnez_execution2 [where d="d"  and r="r" and dist="dist"])
 apply clarsimp
 apply (insert asm_nat_monotonic [where x="add_pc (dpc d + 4) dist" and n="add_pc (dpc d + 4) dist + 4"])
 apply simp
 apply (subgoal_tac "current_instr (Step d) = Isub dr sr1 sr2")
  apply (frule_tac d="d\<lparr>dpc := dpc d + 4, pcp := add_pc (dpc d + 4) dist\<rparr>"  in ASMcore_consis_current_instr, simp)
  apply (frule_tac d="d"  in ASMcore_consis_current_instr, simp)
  apply (simp add: Step_def)
  apply (simp add: arith_exec_def)
  apply (simp add: inc_pcs_st_def)
  apply (subgoal_tac "inc_pcp_by (add_pc (dpc d + 4) dist) (int wlen_byte) = add_pc (dpc d + 4) dist + 4")
   apply clarsimp
   apply (case_tac "t'=0")
    apply clarsimp
    apply (rule not_is_load_store_is_interrupt_free)
      apply (simp add: current_instr_def is_Itrap_def)
     apply simp
    apply simp
   apply (subgoal_tac "t'=1")
    apply (simp add: Step_def)
    apply (rule not_is_load_store_is_interrupt_free)
      apply (simp add: current_instr_def is_Itrap_def)
     apply (simp add: dvd_add)
    apply (simp add: inside_range_def)
   apply simp
  apply (subgoal_tac "0 \<le> wlen_byte")
   apply (frule_tac a="add_pc (dpc d + 4) dist" in inc_pcp_by_is_plus_positive2)
     apply (simp add: wlen_byte_def wlen_bit_def)
    apply (simp add: inside_range_def asm_nat_def)
    apply (simp add: wlen_byte_def)
   apply (simp add: wlen_byte_def)
  apply (simp add: wlen_byte_def)
 apply clarsimp
 apply (insert instr_list_content [where i="1" and l="Suc (Suc 0)" and ad="dpc d" and d="Step d"])
 apply clarsimp
apply clarsimp
apply (insert instr_list_content [where i="0" and l="Suc (Suc 0)" and ad="dpc d" and d="d"])
apply clarsimp
done

lemma srai_execution_woi[rule_format]: "asm_executes_precondition_woi d rangee [Israi dr sr i]
  \<longrightarrow> asm_executes_woi d rangee addr_range 1 (dpc d + 4) (d \<lparr> dpc := dpc d + 4, pcp := pcp d + 4, gprs := (gprs d) [dr := srath (reg (gprs d) sr) (int i)]\<rparr>) "
apply clarsimp
apply (simp add: asm_executes_precondition_woi_def)
apply (simp add: asm_executes_woi_def)
apply clarsimp
apply (subgoal_tac "current_instr d = Israi dr sr i")
 prefer 2
 apply (simp add: current_instr_def)
 apply (simp add: get_instr_list_def instr_mem_read_def)
apply (subgoal_tac "Step d = d\<lparr>dpc := dpc d + 4, pcp := 8 + dpc d, gprs := gprs d[dr := srath (reg (gprs d) sr) (int i)]\<rparr>")
 prefer 2
 apply (simp add: Step_def)
 apply (simp add: arith_exec_def)
 apply (simp add: inc_pcs_st_def)
 apply (subgoal_tac "inc_pcp_by (dpc d + 4) (int wlen_byte) =  8 + dpc d")
  prefer 2
  apply (subgoal_tac "0 \<le> wlen_byte")
   prefer 2
   apply (simp add: wlen_byte_def wlen_bit_def)
  apply (frule_tac a="dpc d + 4" in inc_pcp_by_is_plus_positive2)
    apply (simp add: inside_range_def asm_nat_def)
    apply (simp add: wlen_byte_def wlen_bit_def)
   apply (simp add: wlen_byte_def wlen_bit_def inside_range_def asm_nat_def)
  apply (simp add: wlen_byte_def)
 apply simp
apply (frule_tac d="d"  in ASMcore_consis_current_instr, simp)
apply clarsimp
apply (simp add: not_is_load_store_is_interrupt_free is_Itrap_def)
sorry

lemma jump_addi_execution_woi[rule_format]: "asm_executes_precondition_woi d rangee [Ij dist, Iaddi dr sr i]
                                        \<longrightarrow> asm_nat ((add_pc (dpc d + 4) dist) + 4) 
                                        \<longrightarrow> asm_int dist
                                        \<longrightarrow> 0 \<le> int (dpc d) + 4 + dist
                                        \<longrightarrow> asm_executes_woi d rangee addr_range 2 (add_pc (pcp d) dist) (d \<lparr> dpc := (add_pc (pcp d) dist), 
                                                                                                                pcp := (add_pc (pcp d) dist) + 4,
                                                                                                                gprs := (gprs d) [ dr := int_add (reg (gprs d) sr) i] \<rparr>)"
apply clarsimp
apply (simp add: asm_executes_precondition_woi_def)
apply (simp add: asm_executes_woi_def)
apply clarsimp
apply (simp add: BigStep_decompose)
apply (subgoal_tac "current_instr d = Ij dist")
 apply (frule_tac d="d" in ASMcore_consis_current_instr, simp)
 apply (insert jump_execution [where d="d" and dist="dist"])
 apply clarsimp
 apply (insert asm_nat_monotonic [where x="add_pc (dpc d + 4) dist" and n="add_pc (dpc d + 4) dist + 4"])
 apply simp
 apply (subgoal_tac "current_instr (Step d) = Iaddi dr sr i")
  apply (subgoal_tac "is_interrupt_free (Step d) rangee addr_range")
   apply (frule_tac d="d\<lparr>dpc := dpc d + 4, pcp := add_pc (dpc d + 4) dist\<rparr>"  in ASMcore_consis_current_instr)
    apply (simp add: asm_executes_precondition_woi_def)
   apply clarsimp
   apply (simp add: Step_def)
   apply (simp add: arith_exec_def)
   apply (simp add: inc_pcs_st_def)
   apply (subgoal_tac "inc_pcp_by (add_pc (dpc d + 4) dist) (int wlen_byte) = add_pc (dpc d + 4) dist + 4")
    apply clarsimp
    apply (case_tac "t'=0")
     apply clarsimp
     apply (rule not_is_load_store_is_interrupt_free)
       apply (simp add: current_instr_def is_Itrap_def)
      apply simp
     apply simp
    apply (subgoal_tac "t'=1")
     apply clarsimp
     apply (simp add: Step_def)
    apply clarsimp
   apply (subgoal_tac "0 \<le> wlen_byte")
    apply (frule_tac a="add_pc (dpc d + 4) dist" in inc_pcp_by_is_plus_positive2)
      apply (simp add: wlen_byte_def wlen_bit_def)
     apply (simp add: inside_range_def asm_nat_def)
     apply (simp add: wlen_byte_def)
    apply (simp add: wlen_byte_def)
   apply (simp add: wlen_byte_def)
  apply (rule not_is_load_store_is_interrupt_free, simp add: is_Itrap_def)
   apply (simp add: dvd_add)
  apply (simp add: inside_range_def)
 apply clarsimp
 apply (insert instr_list_content [where i="1" and l="Suc (Suc 0)" and ad="dpc d" and d="Step d"])
 apply clarsimp
apply clarsimp
apply (insert instr_list_content [where i="0" and l="Suc (Suc 0)" and ad="dpc d" and d="d"])
apply clarsimp
done

lemma beqz_sw_execution1_woi[rule_format]: "asm_executes_precondition_woi d rangee [Ibeqz r dist, Isw dr sr i]
                                            \<longrightarrow> reg (gprs d) r \<noteq> 0
                                            \<longrightarrow> asm_nat (add_pc (pcp d) 8)
                                            \<longrightarrow> 4 dvd (intwd_as_nat (reg (gprs d) sr) + intwd_as_nat i)
                                            \<longrightarrow> dr < 32
                                            \<longrightarrow> asm_nat (intwd_as_nat (reg (gprs d) sr) + intwd_as_nat i)
                                            \<longrightarrow> range_contains addr_range (intwd_as_nat (reg (gprs d) sr) + intwd_as_nat i, 4)
                                            \<longrightarrow> \<not> inside_range (word_range_to_byte rangee) (intwd_as_nat (reg (gprs d) sr) + intwd_as_nat i)
                                            \<longrightarrow> asm_executes_woi d rangee addr_range 2 (pcp d + 4) (d \<lparr> dpc := pcp d + 4,
                                                                                                       pcp := pcp d + 8,
                                                                                                       mm := data_mem_write (mm d) (intwd_as_nat (reg (gprs d) sr) + intwd_as_nat i) (reg (gprs d) dr)
                                                                                                     \<rparr> )"
apply clarsimp
apply (simp add: asm_executes_precondition_woi_def)
apply (simp add: asm_executes_woi_def)
apply clarsimp
 apply (simp add: BigStep_decompose)
apply (subgoal_tac "current_instr d = Ibeqz r dist")
 apply (frule_tac d="d"  in ASMcore_consis_current_instr, simp)
 apply (insert beqz_execution1 [where d="d"  and r="r" and dist="dist"])
 apply clarsimp
 apply (simp add: add_pc_plus)
 apply (insert asm_nat_monotonic [where x="8 + dpc d" and n="12 + dpc d"])
 apply (simp add: nat_add_commute)
 apply (subgoal_tac "current_instr (Step d) = Isw dr sr i")
  apply (subgoal_tac "Step (Step d) = d\<lparr>dpc := dpc (Step d) + 4, pcp := 8 + dpc (Step d), mm := data_mem_write (mm d) (intwd_as_nat (reg (gprs (Step d)) sr) + intwd_as_nat i) (reg (gprs (Step d)) dr)\<rparr>")
   apply clarsimp
   apply (frule_tac d="d\<lparr>dpc := dpc d + 4, pcp := dpc d + 8\<rparr>" in ASMcore_consis_current_instr, simp)
   apply clarsimp
   apply (subgoal_tac "\<not> inside_range (fst (word_range_to_byte rangee), snd (word_range_to_byte rangee)) (intwd_as_nat (reg (gprs d) sr) + intwd_as_nat i)")
    apply (frule_tac m="mm d" and d="reg (gprs d) dr" in data_mem_write_mem_unchanged2, simp+)
     apply (simp add: nat_add_commute)
    apply (simp add: nat_add_commute)
    apply clarsimp
    apply (case_tac t')
     (* t'=0 *)
     apply simp
     apply (rule not_is_load_store_is_interrupt_free)
       apply (simp add: is_Itrap_def)
      apply simp
     apply simp
    apply clarsimp
    (* t' = 1 *)
    apply (simp add: is_interrupt_free_def)
    apply (rule conjI)
     (* no instruction misalignment *)
     apply (simp add: not_imal_in_ASM_def)
     apply (simp add: dvd_add)
    apply (rule conjI)
     (* no data misalignment *)
     apply (simp add: not_dmal_in_ASM_def)
     apply (simp add: load_store_target_def)
     apply (simp add: nat_add_commute)
     apply (simp add: asm_nat_impl_fit_nat)
    apply (rule conjI)
     (* no access out of range *)
     apply (simp add: mem_access_inside_range_def)
     apply (simp add: range_contains_def)
     apply (clarsimp simp add: load_store_target_def)
     apply (simp add: nat_add_commute)
     apply (simp add: asm_nat_impl_fit_nat)
    (* no write access to the code *)
    apply (simp add: is_Itrap_def)
    apply (simp add: no_mem_write_access_inside_code_def)
    apply (simp add: load_store_target_def)
    apply (simp add: nat_add_commute)
    apply (simp add: asm_nat_impl_fit_nat)
    apply (simp add: inside_range_def)
    apply (simp add: is_store_def)
    apply (simp add: dvd_def)
    apply clarsimp
   apply (simp add: nat_add_commute)
  apply (simp add: Step_def)
  apply (simp add: store_exec_def)
  apply (simp add: nat_add_commute)
  apply (simp add: asm_nat_impl_fit_nat)
  apply (simp add: inc_pcs_st_def)
  apply (frule_tac y="dr" and x="intwd_as_nat (reg (gprs d) sr) + intwd_as_nat i" in correct_store_to_mem_word2, simp)
  apply (simp add: nat_add_commute)
  apply (subgoal_tac "(intwd_as_nat i + intwd_as_nat (reg (gprs d) sr)) mod 4 = 0")
   apply clarsimp
   apply (rename_tac q)
   apply (simp add: data_mem_write_def)
   apply (subgoal_tac "inc_pcp_by (dpc d + 8) (int wlen_byte) =  dpc d + 12")
    apply simp
   apply (subgoal_tac "0 \<le> wlen_byte")
    apply (frule_tac a="dpc d + 8" in inc_pcp_by_is_plus_positive2)
      apply (simp add: wlen_byte_def wlen_bit_def)
     apply (simp add: inside_range_def asm_nat_def)
     apply (simp add: wlen_byte_def)
    apply (simp add: wlen_byte_def)
   apply (simp add: wlen_byte_def)
  apply (simp add: dvd_impl_mod_zero)
 apply (simp add: current_instr_def)
 apply (simp add: get_instr_list_def instr_mem_read_def)
 apply clarsimp
 apply (subgoal_tac "(dpc d + 4) div 4 = dpc d div 4 + 1")
  apply simp
 apply simp
 apply arith
apply (simp add: current_instr_def)
apply (simp add: get_instr_list_def instr_mem_read_def)
sorry

lemma beqz_sw_execution2_woi[rule_format]: "asm_executes_precondition_woi d rangee [Ibeqz r dist, Isw dr sr i]
                                            \<longrightarrow> reg (gprs d) r = 0
                                            \<longrightarrow> asm_nat ((add_pc (dpc d + 4) dist) + 4)
                                            \<longrightarrow> asm_int dist
                                            \<longrightarrow> 0 \<le> int (dpc d) + 4 + dist
                                            \<longrightarrow> 4 dvd (intwd_as_nat (reg (gprs d) sr) + intwd_as_nat i)
                                            \<longrightarrow> dr < 32
                                            \<longrightarrow> asm_nat (intwd_as_nat (reg (gprs d) sr) + intwd_as_nat i)
                                            \<longrightarrow> range_contains addr_range (intwd_as_nat (reg (gprs d) sr) + intwd_as_nat i, 4)
                                            \<longrightarrow> \<not> inside_range (word_range_to_byte rangee) (intwd_as_nat (reg (gprs d) sr) + intwd_as_nat i)
                                            \<longrightarrow> asm_executes_woi d rangee addr_range 2 (add_pc (pcp d) dist) (d \<lparr> dpc := add_pc (pcp d) dist,
                                                                                                       pcp := (add_pc (pcp d) dist) + 4,
                                                                                                       mm := data_mem_write (mm d) (intwd_as_nat (reg (gprs d) sr) + intwd_as_nat i) (reg (gprs d) dr)
                                                                                                     \<rparr> )"
apply clarsimp
apply (simp add: asm_executes_precondition_woi_def)
apply (simp add: asm_executes_woi_def)
apply clarsimp
 apply (simp add: BigStep_decompose)
apply (subgoal_tac "current_instr d = Ibeqz r dist")
 apply (frule_tac d="d"  in ASMcore_consis_current_instr, simp)
 apply (insert beqz_execution2 [where d="d" and r="r" and dist="dist"])
 apply clarsimp
 apply (insert asm_nat_monotonic [where x="add_pc (dpc d + 4) dist" and n="add_pc (dpc d + 4) dist + 4"])
 apply simp
 apply (subgoal_tac "current_instr (Step d) = Isw dr sr i")
  apply (subgoal_tac "Step (Step d) = d \<lparr>dpc := add_pc (dpc d + 4) dist, pcp := add_pc (dpc d + 4) dist + 4, mm := data_mem_write (mm d) (intwd_as_nat (reg (gprs d) sr) + intwd_as_nat i) (reg (gprs d) dr)\<rparr>")
   apply clarsimp
   apply (frule_tac d="d\<lparr>dpc := dpc d + 4, pcp := add_pc (dpc d + 4) dist\<rparr>" in ASMcore_consis_current_instr, simp)
   apply clarsimp
   apply (subgoal_tac "\<not> inside_range (fst (word_range_to_byte rangee), snd (word_range_to_byte rangee)) (intwd_as_nat (reg (gprs d) sr) + intwd_as_nat i)")
    apply (frule_tac m="mm d" and d="reg (gprs d) dr" in data_mem_write_mem_unchanged2, simp+)
    apply (case_tac t')
     (* t'=0 *)
     apply simp
     apply (rule not_is_load_store_is_interrupt_free)
       apply (simp add: is_Itrap_def)
      apply simp
     apply simp
    apply clarsimp
    (* t' = 1 *)
    apply (simp add: is_interrupt_free_def)
    apply (rule conjI)
     (* no instruction misalignment *)
     apply (simp add: not_imal_in_ASM_def)
     apply (simp add: dvd_add)
    apply (rule conjI)
     (* no data misalignment *)
     apply (simp add: not_dmal_in_ASM_def)
     apply (simp add: load_store_target_def)
     apply (simp add: nat_add_commute)
     apply (simp add: asm_nat_impl_fit_nat)
    apply (rule conjI)
     (* no access out of range *)
     apply (simp add: mem_access_inside_range_def)
     apply (simp add: load_store_target_def)
     apply (simp add: range_contains_def)
     apply clarsimp
     apply (simp add: nat_add_commute)
     apply (simp add: asm_nat_impl_fit_nat)
    (* no write access to the code *)
    apply (simp add: is_Itrap_def)
    apply (simp add: no_mem_write_access_inside_code_def)
    apply (simp add: load_store_target_def)
    apply (simp add: nat_add_commute)
    apply (simp add: asm_nat_impl_fit_nat)
    apply (simp add: inside_range_def)
    apply (simp add: is_store_def)
    apply (simp add: dvd_def)
    apply clarsimp
   apply (simp add: nat_add_commute)
  apply (simp add: Step_def)
  apply (simp add: store_exec_def)
  apply (simp add: nat_add_commute)
  apply (simp add: asm_nat_impl_fit_nat)
  apply (simp add: inc_pcs_st_def)
  apply (frule_tac y="dr" and x="intwd_as_nat i + intwd_as_nat (reg (gprs d) sr)" in correct_store_to_mem_word2, simp)
  apply (subgoal_tac "(intwd_as_nat i + intwd_as_nat (reg (gprs d) sr)) mod 4 = 0")
   apply clarsimp
   apply (rename_tac q)
   apply (simp add: data_mem_write_def)
   apply (subgoal_tac "inc_pcp_by (add_pc (dpc d + 4) dist) (int wlen_byte) =  4 + add_pc (dpc d + 4) dist")
    apply simp
   apply (subgoal_tac "0 \<le> wlen_byte")
    apply (frule_tac a="add_pc (dpc d + 4) dist" in inc_pcp_by_is_plus_positive2)
      apply (simp add: wlen_byte_def wlen_bit_def)
     apply (simp add: inside_range_def asm_nat_def)
     apply (simp add: wlen_byte_def)
    apply (simp add: wlen_byte_def)
   apply (simp add: wlen_byte_def)
  apply (simp add: dvd_impl_mod_zero)
 apply (simp add: current_instr_def)
 apply (simp add: get_instr_list_def instr_mem_read_def)
 apply clarsimp
 apply (subgoal_tac "(dpc d + 4) div 4 = dpc d div 4 + 1")
  apply simp
 apply simp
 apply arith
apply (simp add: current_instr_def)
apply (simp add: get_instr_list_def instr_mem_read_def)
sorry

declare Let_def[simp del]
declare word_range_to_byte_def[simp del]

end
