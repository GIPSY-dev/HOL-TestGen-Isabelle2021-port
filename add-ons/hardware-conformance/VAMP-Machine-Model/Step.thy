(**
 * Copyright (c) 2004-2009 Matthias Daum, Thomas In der Rieden,
 * Dirk Leinenbach, Alexandra Tsyban.
 * Some rights reserved, Saarland University.
 *
 * This work is licensed under the German-Jurisdiction Creative Commons
 * Attribution Non-commercial Share Alike 2.0 License.
 * See the file LIZENZ for a full copy of the license.
**)
(* $Id: Step.thy 29816 2009-11-24 12:55:59Z DirkLeinenbach $ *)
chapter {* Step function for the assembler machine *}

theory Step imports Exec begin

definition Step :: "ASMcore_t \<Rightarrow> ASMcore_t"
where     "Step st == exec_instr st (current_instr st)"

primrec BigStep :: "[ASMcore_t, nat] \<Rightarrow> ASMcore_t"
where  "BigStep st 0 = st"
     | "BigStep st (Suc n) = BigStep (Step st) n"


definition BigStepSwap :: "[PhysMach_t, nat] \<Rightarrow> PhysMach_t"
where     "BigStepSwap phm n == phm \<lparr> ASMcore := BigStep (ASMcore phm) n \<rparr>"

lemma usermode_sprs_Step:
  "sprs C ! SPR_MODE \<noteq> 0 \<Longrightarrow> i\<noteq>SPR_RM \<Longrightarrow> i\<noteq>SPR_IEEEF \<Longrightarrow> i\<noteq>SPR_FCC
   \<Longrightarrow> sprs (Step C) ! i = sprs C ! i"
  by (cases "current_instr C") (simp_all add: Step_def load_exec_def Let_def
    store_exec_def arith_exec_def is_system_mode_def comp_exec_def)

lemma usermode_pages_used_Step:
 "\<not> is_system_mode s \<Longrightarrow> pages_used (Step s) = pages_used s"
by (simp add: is_system_mode_def pages_used_def usermode_sprs_Step
              SPR_PTL_def SPR_MODE_def SPR_RM_def SPR_IEEEF_def SPR_FCC_def)

lemma Step_BigStep[rule_format]: "!d. Step (BigStep d n) = BigStep d (Suc n)"
by (induct_tac n) simp_all

lemma BigStep_Step: "BigStep (Step d) n = BigStep d (Suc n)"
by simp

lemma BigStep_add[rule_format]: "! d. BigStep d (n + m) = BigStep (BigStep d n) m"
by (induct_tac n) simp_all

lemma BigStep_diff_1[rule_format]: "0 < n \<longrightarrow> BigStep d n = BigStep (Step d) (n - 1)"
by (case_tac n) simp_all

lemma Step_Step: "Step (Step d) = BigStep d 2"
by (simp add:eval_nat_numeral)

lemma Step_BigStep_swap[rule_format]: "\<forall> d. BigStep (Step d) n = Step (BigStep d n)"
apply (induct_tac n)
  apply simp
apply simp
done

lemma BigStep_suc[rule_format]: "BigStep d (Suc n) = Step (BigStep d n)"
apply (simp add: Step_BigStep_swap)
done

lemma Step_BigStep_combine[rule_format]: "Step (BigStep d n) = BigStep d (Suc n)"
apply (simp add: Step_BigStep_swap)
done

lemma BigStep_comp[rule_format]: "\<forall> d. BigStep d (a + b) = BigStep (BigStep d a) b"
apply (induct_tac a)
  apply simp
apply clarsimp
done

lemma BigStep_add_symm[rule_format]: "\<forall> d. BigStep (BigStep d a) b = BigStep d (a + b)"
apply (induct_tac a)
  apply simp
apply clarsimp
done

lemma BigStep_swap[rule_format]: "BigStep (BigStep d a) b = BigStep (BigStep d b) a"
apply (induct_tac a)
  apply simp
apply clarsimp
apply (simp add: Step_BigStep_swap)
done

lemma Step_is_BigStep[rule_format]: "Step d = BigStep d 1"
apply simp
done

lemma BigStep_decompose[rule_format]: "0 < n \<longrightarrow> BigStep d n = Step (BigStep d (n - 1))"
apply (case_tac n)
  apply simp
apply (simp add: Step_BigStep_swap)
done

text {* function gives the value dpc and pcp after the given number of steps *}

definition pcs_after :: "[ASMcore_t, nat] \<Rightarrow> (nat \<times> nat)"
where     "pcs_after d n \<equiv>  let  dp = BigStep d n
                             in  (dpc dp, pcp dp)"

text {* @{text "in_range_exec d range n len"} says that during the @{text n} steps the program 
        from address @{text "dpc d"} till @{text "dpc d + 4 * len"} is executed. No other instruction 
        is executed. After that, @{text dpc} is at the end of code, @{text pcp} is incremented by 4 *}


definition in_range_exec :: "[ASMcore_t, nat, nat] \<Rightarrow> bool"
where
  "in_range_exec d n len \<equiv> pcs_after d n = (dpc d + 4 * len, dpc d + 4 * len + 4) \<and>
                                 (\<forall> k < n. dpc d \<le> dpc (BigStep d k) \<and> dpc (BigStep d k) < dpc d + 4 * len)"

text{* the next function counts the number of steps for the  arbitrary assembler program *}

definition  prog_steps :: "[ASMcore_t, nat] \<Rightarrow> nat option"
where      "prog_steps d code_len \<equiv> if  \<exists> n. in_range_exec d n code_len
                                     then Some (THE n. in_range_exec d n code_len)
                                     else None"


lemma prog_stepsI: "in_range_exec d n l \<Longrightarrow> prog_steps d l = Some n"
apply (simp add: prog_steps_def Let_def)
apply (intro conjI impI)
 apply (thin_tac "\<exists>n. in_range_exec d n l")
 apply (rule the_equality)
  apply assumption
 apply (simp add: in_range_exec_def)
 apply (elim conjE)
 apply (case_tac "na < n")
  apply (erule_tac x = "na" in allE)
  apply (drule mp, assumption)
  apply (simp add: pcs_after_def Let_def)
 apply (rotate_tac 2)
 apply (case_tac "n < na")
  apply (erule_tac x = "n" in allE)
  apply (drule mp, assumption)
  apply (simp add: pcs_after_def Let_def)
 apply simp
apply fastforce
done

end
