(**
 * Copyright (c) 2004-2007 Mark Hillebrand, Dirk Leinenbach, Hristo Pentchev,
 * Alexandra Tsyban.
 * Some rights reserved, Saarland University.
 *
 * This work is licensed under the German-Jurisdiction Creative Commons
 * Attribution Non-commercial Share Alike 2.0 License.
 * See the file LIZENZ for a full copy of the license.
**)
(* $Id: asm_execution.thy 23152 2008-04-16 07:25:27Z AlexandraTsyban $ *)
theory asm_execution imports asm_execution_common begin

declare Let_def[simp]

(* Observe: The definitions in this theory do NOT ensure that the executed assembler code doesn't generate interrupts on the lower system layers.
   Thus, DON'T use this theory for proofs which will later have to be translated to the VAMP ISA level; use theory asm_execution_without_interrupt.thy instead.
*)


inductive_set   asm_executes_in_t_steps :: "(ASMcore_t \<times> instr list \<times> nat \<times> ASMcore_t) set"
where
  AEITSintro[intro] : "\<lbrakk>

                  get_instr_list (mm c) a (length q) = q;
                  dpc c = a;
                  pcp c = a + 4;
                  dpc c' = a + 4 * length q;
                  pcp c' = dpc c' + 4;
                  BigStep c k = c'
                 (* \<forall> k'. k' < k \<longrightarrow> a \<le> dpc (BigStep c k') \<and> dpc (BigStep c k') < a + 4 * length q *)
                \<rbrakk>
                \<Longrightarrow> (c,q,k,c') \<in> asm_executes_in_t_steps"

definition asm_executes_precondition :: "ASMcore_t \<Rightarrow> (nat \<times> nat) \<Rightarrow> instr list \<Rightarrow> bool"
where
  "asm_executes_precondition d rangee il \<equiv> 
   (
     is_ASMcore d
     \<and> pcp d= dpc d + 4
     \<and> get_instr_list (mm d) (dpc d) (length il) = il
     \<and> list_all is_instr il
     \<and> (il \<noteq> [] \<longrightarrow> inside_range rangee (dpc d))
     \<and> (il \<noteq> [] \<longrightarrow> inside_range rangee (dpc d + 4 * length il - 1))
     \<and> asm_nat (snd rangee + 4)
   )
  "

definition asm_executes :: "ASMcore_t \<Rightarrow> (nat \<times> nat) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> ASMcore_t \<Rightarrow> bool"
where
  "asm_executes d rangee t dest d' \<equiv> 
   (
     (
        dpc d' = dest
        \<and> pcp d' = dpc d' + 4
        \<and> BigStep d t = d'
        \<and> is_ASMcore d'
        \<and> mem_unchanged (mm d) (mm d') (fst rangee) (snd rangee) (* no self-modifying code; *)
     )
   )
  "

lemma asm_executes_append[rule_format]: "asm_executes d rangee ta x d'
                                         \<longrightarrow> asm_executes d' rangee tb dest d''
                                         \<longrightarrow> asm_executes d rangee (ta+tb) dest d''"
apply clarsimp
apply (simp add: asm_executes_def)
apply clarsimp
apply (simp add: BigStep_add)
apply (frule mem_unchanged_transitive, simp)
apply simp
done

lemma asm_exec_precond_append[rule_format]: "asm_executes_precondition d rangee (a@b)
                                              \<longrightarrow> asm_executes d rangee t (dpc d + 4 * length a) d'
                                              \<longrightarrow> asm_executes_precondition d' rangee b"
apply clarsimp
apply (simp add: asm_executes_precondition_def)
apply (simp add: asm_executes_def)
apply clarsimp
apply (case_tac "a@b=[]")
 apply clarsimp
 apply (simp add: get_instr_list_def)
apply clarsimp
apply (frule get_instr_list_append2)
apply (rule conjI)
 apply (simp add: inside_range_def)
 apply (frule_tac base="dpc d + 4 * length a" and l="length b" in mem_unchanged_get_instr_list_same, simp+)
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

lemma asm_executes_dpc[rule_format]: "asm_executes d rangee t dest d' \<longrightarrow> dpc d' = dest"
apply (simp add: asm_executes_def)
done

lemma asm_executes_pcp[rule_format]: "asm_executes d rangee t dest d' \<longrightarrow> pcp d' = dpc d' + 4"
apply clarsimp
apply (simp add: asm_executes_def)
done

lemma asm_exec_precond_append2[rule_format]: "asm_executes_precondition d rangee (a@b) \<longrightarrow> asm_executes_precondition d rangee a"
apply clarsimp
apply (simp add: asm_executes_precondition_def)
apply clarsimp
apply (simp add: get_instr_list_append1)
apply clarsimp
apply (frule_tac a="dpc d" and b="dpc d + (4* length a + 4* length b) - 1" and x="dpc d + 4 * length a - 1" in inside_range_interval, simp+)
  apply (simp add: inside_range_def)
  apply (case_tac a, simp)
  apply clarsimp
 apply (simp add: inside_range_def)
 apply clarsimp

done

lemma asm_exec_precond_hd[rule_format]: "asm_executes_precondition d rangee (a#b) \<longrightarrow> asm_executes_precondition d rangee [a]"
apply clarsimp
apply (simp add: asm_executes_precondition_def)
apply clarsimp
apply (frule get_instr_list_head)
apply clarsimp
apply (frule_tac a="dpc d" and b="dpc d + (4* length [a] + 4* length b) - 1" and x="dpc d + 4 - 1" in inside_range_interval, simp+)
done

lemma asm_exec_precond_take[rule_format]: "asm_executes_precondition d rangee l \<longrightarrow> n \<le> length l \<longrightarrow> asm_executes_precondition d rangee (take n l)"
apply clarsimp
apply (simp add: asm_executes_precondition_def)
apply clarsimp
apply (simp add: list_all_take)
apply (simp add: min_def)
apply (rule conjI)
 apply clarsimp
apply clarsimp
apply (simp add: get_instr_list_take2)
apply clarsimp
apply (frule_tac a="dpc d" and b="dpc d + 4* length l - 1" and x="dpc d + 4 * n - 1" in inside_range_interval, simp+)

done

lemma asm_executes_gprs_length[rule_format]: "asm_executes d rangee t dest d' \<longrightarrow> length (gprs d') = 32"
apply (simp add: asm_executes_def is_ASMcore_def)
done

lemma asm_precondition_gprs_length[rule_format]: "asm_executes_precondition d rangee ecode \<longrightarrow> length (gprs d) = 32"
apply (simp add: asm_executes_precondition_def is_ASMcore_def)
done

lemma asm_executes_impl_is_ASMcore[rule_format]: "asm_executes d rangee t dest d' \<longrightarrow> is_ASMcore d'"
apply clarsimp
apply (simp add: asm_executes_def)
done

lemma asm_executes_asm_int[rule_format]: "asm_executes d rangee t dest d' \<longrightarrow> r < 32 \<longrightarrow> asm_int (reg (gprs d') r)"
apply clarsimp
apply (frule asm_executes_impl_is_ASMcore) 
apply (simp add: is_ASMcore_def)
done

lemma asm_executes_precondition_is_ASMcore[rule_format]: "asm_executes_precondition d rangee il \<longrightarrow> is_ASMcore d"
apply clarsimp
apply (simp add: asm_executes_precondition_def)
done

lemma asm_executes_precondition_asm_int[rule_format]: "asm_executes_precondition d rangee il \<longrightarrow> r < 32 \<longrightarrow> asm_int (reg (gprs d) r)"
apply clarsimp
apply (frule asm_executes_precondition_is_ASMcore) 
apply (simp add: is_ASMcore_def)
done

lemma asm_executes_precondition_snd_range_asm_nat[rule_format]: "asm_executes_precondition d rangee il \<longrightarrow> asm_nat (snd rangee + 4)"
apply (simp add: asm_executes_precondition_def)
done

lemma asm_executes_precondition_pcp[rule_format]: "asm_executes_precondition d rangee il \<longrightarrow> pcp d = dpc d + 4"
apply clarsimp
apply (simp add: asm_executes_precondition_def)
done

lemma asm_execute_precondition_inside_range1[rule_format]: "asm_executes_precondition d rangee il \<longrightarrow> il \<noteq> [] \<longrightarrow> inside_range rangee (dpc d)"
apply (simp add: asm_executes_precondition_def)
done

lemma asm_execute_precondition_inside_range2[rule_format]: "asm_executes_precondition d rangee il \<longrightarrow> il \<noteq> [] \<longrightarrow> inside_range rangee (dpc d + 4 * length il - 1)"
apply (simp add: asm_executes_precondition_def)
done

(*
  Execution of certain assembler instruction or combinations of assembler instructions
*)

declare intwd_as_nat_0[simp];
declare intwd_as_nat_4[simp];
declare intwd_as_nat_8[simp];
declare intwd_as_nat_12[simp];

lemma beqz_nop_execution1[rule_format]: "asm_executes_precondition d rangee [Ibeqz r dist, Inop] 
                                         \<longrightarrow> reg (gprs d) r \<noteq> 0
                                         \<longrightarrow> asm_nat (add_pc (pcp d) 8)
                                         \<longrightarrow> asm_executes d rangee 2 (pcp d + 4) (d \<lparr> dpc := pcp d + 4, pcp := pcp d + 8 \<rparr>)"
apply clarsimp
apply (simp add: asm_executes_precondition_def)
apply (simp add: asm_executes_def)
apply clarsimp
 apply (simp add: BigStep_decompose)
apply (subgoal_tac "current_instr d = Ibeqz r dist")
  apply (frule_tac d="d" in ASMcore_consis_current_instr, simp)
  apply (insert beqz_execution1 [where d="d" and r="r" and dist="dist"])
  apply clarsimp
  apply (simp add: add_pc_plus)
  apply (insert asm_nat_monotonic [where x="8 + dpc d" and n="12 + dpc d"])
  apply clarsimp
  apply (subgoal_tac "current_instr (Step d) = Inop")
    apply (frule_tac d="d\<lparr>dpc := dpc d + 4, pcp := 8 + dpc d\<rparr>" in ASMcore_consis_current_instr)
      apply (simp add: nop_is_instr)
    apply clarsimp
    apply (insert nop_execution [where d="Step d"])
    apply simp
    apply (simp add: add_pc_plus)
  apply clarsimp
  apply (insert instr_list_content [where i="1" and l="Suc (Suc 0)" and ad="dpc d" and d="Step d "])
  apply clarsimp
apply clarsimp
apply (insert instr_list_content [where i="0" and l="Suc (Suc 0)" and ad="dpc d" and d="d"])
apply clarsimp
done

lemma jump_nop_execution[rule_format]: "asm_executes_precondition d rangee [Ij dist, Inop]
                                        \<longrightarrow> asm_nat ((add_pc (dpc d + 4) dist) + 4) 
                                        \<longrightarrow> asm_int dist
                                        \<longrightarrow> 0 \<le> int (dpc d) + 4 + dist
                                        \<longrightarrow> asm_executes d rangee 2 (add_pc (pcp d) dist) (d \<lparr> dpc := (add_pc (pcp d) dist), pcp := (add_pc (pcp d) dist) + 4 \<rparr>)"
apply clarsimp
apply (simp add: asm_executes_precondition_def)
apply (simp add: asm_executes_def)
apply clarsimp
apply (simp add: BigStep_decompose)
apply (subgoal_tac "4 \<le> snd rangee")
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
  apply (insert instr_list_content [where i="1" and l="Suc (Suc 0)" and ad="dpc d" and d="Step d"])
  apply clarsimp
 apply clarsimp
 apply (insert instr_list_content [where i="0" and l="Suc (Suc 0)" and ad="dpc d" and d="d"])
 apply clarsimp
apply clarsimp
apply (simp add: inside_range_def)
done

lemma beqz_nop_execution2[rule_format]: "asm_executes_precondition d rangee [ Ibeqz r dist, Inop ]
                                        \<longrightarrow> reg (gprs d) r = 0
                                        \<longrightarrow> asm_nat ((add_pc (dpc d + 4) dist) + 4) \<longrightarrow> asm_int dist \<longrightarrow> 0 \<le> int (dpc d) + 4 + dist
                                        \<longrightarrow> asm_executes d rangee 2 (add_pc (pcp d) dist) (d \<lparr> dpc := (add_pc (pcp d) dist), pcp := (add_pc (pcp d) dist) + 4 \<rparr>)"
apply clarsimp
apply (simp add: asm_executes_precondition_def)
apply (simp add: asm_executes_def)
apply clarsimp
apply (simp add: BigStep_decompose)
apply (subgoal_tac "4 \<le> snd rangee")
 apply (subgoal_tac "current_instr d = Ibeqz r dist")
  apply (frule_tac d="d" in ASMcore_consis_current_instr, simp)
  apply (insert beqz_execution2 [where d="d" and r="r" and dist="dist"])
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
  apply (insert instr_list_content [where i="1" and l="Suc (Suc 0)" and ad="dpc d" and d="Step d"])
  apply clarsimp
 apply clarsimp
 apply (insert instr_list_content [where i="0" and l="Suc (Suc 0)" and ad="dpc d" and d="d"])
 apply clarsimp
apply clarsimp
apply (simp add: inside_range_def)
done

lemma is_not_branch_and_store_asm_executes[rule_format]: "asm_executes_precondition d rangee il
                                                             \<longrightarrow> il \<noteq> []
                                                             \<longrightarrow> list_all (\<lambda> i. is_not_branch_and_store i) il 
                                                             \<longrightarrow> (\<exists> d'. asm_executes d rangee (length il) (dpc d + 4 * length il) d' \<and> mm d' = mm d)"
apply clarsimp
apply (simp add: asm_executes_precondition_def)
apply clarsimp
apply (simp add: asm_executes_def)
apply (subgoal_tac "asm_nat (dpc d + 4 * length il + 4)")
 apply (frule_tac n="length il" in ASMcore_consis_BigStep, simp, simp)
  apply (simp add: list_all_iff)
 apply clarsimp
 apply (frule_tac dpc_pcp_BigStep, simp, simp)
   apply (simp add: is_not_branch_and_store_list_def)
  apply simp
 apply clarsimp
apply (simp add: inside_range_def)
apply (simp add: asm_nat_def)
apply (case_tac il, simp)
apply clarsimp
done

lemma add_execution[rule_format]: "asm_executes_precondition d rangee [Iadd dr sr1 sr2] 
                                         \<longrightarrow> asm_executes d rangee 1 (dpc d + 4) (d \<lparr> dpc := dpc d + 4,
                                                                                     pcp := pcp d + 4,
                                                                                     gprs := (gprs d) [ dr := int_add (reg (gprs d) sr1) (reg (gprs d) sr2)] \<rparr>)"
apply clarsimp
apply (simp add: asm_executes_precondition_def)
apply (simp add: asm_executes_def)
apply clarsimp
apply (subgoal_tac "current_instr d = Iadd dr sr1 sr2")
 apply (subgoal_tac "Step d = d\<lparr>dpc := dpc d + 4, pcp := 8 + dpc d, gprs := gprs d[dr := int_add (reg (gprs d) sr1) (reg (gprs d) sr2)]\<rparr>")
  apply (frule_tac d="d" in ASMcore_consis_current_instr, simp)
  apply clarsimp
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

lemma sw_execution[rule_format]: "asm_executes_precondition d rangee [Isw RD rs imm] 
                                         \<longrightarrow> RD < 32
                                         \<longrightarrow> 4 dvd (intwd_as_nat (reg (gprs d) rs) + intwd_as_nat imm)
                                         \<longrightarrow> 4 dvd (fst rangee)
                                         \<longrightarrow> 4 dvd (snd rangee)
                                         \<longrightarrow> asm_nat (intwd_as_nat (reg (gprs d) rs) + intwd_as_nat imm)
                                         \<longrightarrow> \<not> inside_range (fst rangee, snd rangee) (intwd_as_nat (reg (gprs d) rs) + intwd_as_nat imm)
                                         \<longrightarrow> asm_executes d rangee 1 (dpc d + 4) (d 
                                                                               \<lparr> dpc := dpc d + 4,
                                                                                 pcp := pcp d + 4,
                                                                                 mm := data_mem_write (mm d) (intwd_as_nat (reg (gprs d) rs) + intwd_as_nat imm)
                                                                                                       (reg (gprs d) RD) \<rparr>)"
apply clarsimp
apply (simp add: asm_executes_precondition_def asm_executes_def)
apply clarsimp
apply (subgoal_tac "current_instr d = Isw RD rs imm")
 apply (subgoal_tac "Step d = d\<lparr>dpc := dpc d + 4, pcp := 8 + dpc d, mm := data_mem_write (mm d) (intwd_as_nat (reg (gprs d) rs) + intwd_as_nat imm) (reg (gprs d) RD)\<rparr>")
  apply (frule_tac d="d" in ASMcore_consis_current_instr, simp)
  apply clarsimp
  apply (subgoal_tac "\<not> inside_range (fst (fst rangee, snd rangee), snd (fst rangee, snd rangee)) (intwd_as_nat (reg (gprs d) rs) + intwd_as_nat imm)")
   apply (frule_tac m="mm d" and d="reg (gprs d) RD" in data_mem_write_mem_unchanged2, simp+)
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

lemma jal_sw_execution[rule_format]: "asm_executes_precondition d rangee [Ijal dist, Isw GPR_ret rs imm]
                                       \<longrightarrow> rs \<noteq> GPR_ret
                                       \<longrightarrow> 4 dvd (intwd_as_nat (reg (gprs d) rs) + intwd_as_nat imm)
                                       \<longrightarrow> 4 dvd (fst rangee)
                                       \<longrightarrow> 4 dvd (snd rangee)
                                       \<longrightarrow> asm_nat (intwd_as_nat (reg (gprs d) rs) + intwd_as_nat imm)
                                       \<longrightarrow> \<not> inside_range (fst rangee, snd rangee) (intwd_as_nat (reg (gprs d) rs) + intwd_as_nat imm)
                                       \<longrightarrow> 0 \<le> int (dpc d) + dist + 4
                                       \<longrightarrow> inside_range rangee (add_pc (dpc d + 4) dist)
                                       \<longrightarrow> asm_nat ((add_pc (dpc d + 4) dist) + 4)
                                       \<longrightarrow> asm_executes d rangee 2 (add_pc (dpc d + 4) dist) (d 
                                                                               \<lparr> dpc := add_pc (dpc d + 4) dist,
                                                                                 pcp := add_pc (pcp d + 4) dist,
                                                                                 gprs := gprs d [ GPR_ret := natwd_as_int (dpc d + 8)],
                                                                                 mm := data_mem_write (mm d) (intwd_as_nat (reg (gprs d) rs) + intwd_as_nat imm)
                                                                                                                      (natwd_as_int (dpc d + 8)) \<rparr>)"
apply clarsimp
apply (simp add: asm_executes_precondition_def asm_executes_def)
apply clarsimp
apply (simp add: BigStep_diff_1)
apply (subgoal_tac "add_pc (8 + dpc d) dist = add_pc (dpc d + 4) dist + 4")
 apply clarsimp
 apply (subgoal_tac "current_instr d = Ijal dist")
  apply (subgoal_tac "current_instr (Step d) = Isw GPR_ret rs imm")
   apply (subgoal_tac "Step (Step d) = d
      \<lparr>dpc := add_pc (dpc d + 4) dist, pcp := add_pc (dpc d + 4) dist + 4, gprs := gprs d[GPR_ret := natwd_as_int (dpc d + 8)],
         mm := data_mem_write (mm d) (intwd_as_nat (reg (gprs d) rs) + intwd_as_nat imm) (natwd_as_int (dpc d + 8))\<rparr>")
    apply clarsimp
    apply (frule_tac d="d" in ASMcore_consis_current_instr, simp)
    apply (frule_tac d="Step d" in ASMcore_consis_current_instr, simp)
    apply clarsimp
    apply (subgoal_tac "\<not> inside_range (fst (fst rangee, snd rangee), snd (fst rangee, snd rangee)) (intwd_as_nat (reg (gprs d) rs) + intwd_as_nat imm)")
     apply (frule_tac m="mm d" and d="natwd_as_int (dpc d + 8)" in data_mem_write_mem_unchanged2, simp+)
   apply (frule_tac d="d" in ASMcore_consis_current_instr, simp)
   apply (simp add: Step_def)
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
         apply clarsimp
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
      apply simp
     apply simp
    apply (simp add: dvd_impl_mod_zero)
   apply (case_tac rs)
    apply simp
   apply simp
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
 apply arith
apply (simp add: add_pc_plus)
sorry

lemma lw_execution[rule_format]: "asm_executes_precondition d rangee [Ilw RD rs imm] 
                                         \<longrightarrow> 4 dvd (intwd_as_nat (reg (gprs d) rs) + intwd_as_nat imm)
                                         \<longrightarrow> asm_nat (intwd_as_nat (reg (gprs d) rs) + intwd_as_nat imm)
                                         \<longrightarrow> asm_executes d rangee 1 (dpc d + 4) (d 
                                                                               \<lparr> dpc := dpc d + 4,
                                                                                 pcp := pcp d + 4,
                                                                                 gprs := gprs d [ RD := data_mem_read (mm d) (intwd_as_nat (reg (gprs d) rs) + intwd_as_nat imm)]
                                                                               \<rparr>)"
apply clarsimp
apply (simp add: asm_executes_precondition_def asm_executes_def)
apply clarsimp
apply (subgoal_tac "current_instr d = Ilw RD rs imm")
 apply (subgoal_tac "Step d = d\<lparr>dpc := dpc d + 4, pcp := 8 + dpc d, gprs := gprs d [ RD := data_mem_read (mm d) (intwd_as_nat (reg (gprs d) rs) + intwd_as_nat imm)]\<rparr>")
  apply (frule_tac d="d" in ASMcore_consis_current_instr, simp)
  apply clarsimp
 apply (simp add: Step_def)
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
done

lemma jr_nop_execution[rule_format]: "asm_executes_precondition d rangee [Ijr r, Inop]
                                        \<longrightarrow> asm_nat (intwd_as_nat (reg (gprs d) r) + 4)
                                        \<longrightarrow> asm_executes d rangee 2 (intwd_as_nat (reg (gprs d) r)) (d \<lparr> dpc := intwd_as_nat (reg (gprs d) r), pcp := intwd_as_nat (reg (gprs d) r) + 4 \<rparr>)"
apply clarsimp
apply (simp add: asm_executes_precondition_def)
apply (simp add: asm_executes_def)
apply clarsimp
apply (simp add: BigStep_decompose)
apply (subgoal_tac "current_instr d = Ijr r")
 apply (frule_tac d="d" in ASMcore_consis_current_instr, simp)
 apply (insert jr_execution [where d="d" and r="r"])
 apply clarsimp
 apply (subgoal_tac "current_instr (Step d) = Inop")
  apply (frule_tac d="d\<lparr>dpc := dpc d + 4, pcp := intwd_as_nat (reg (gprs d) r)\<rparr>" in ASMcore_consis_current_instr, simp)
  apply (simp add: nop_is_instr)
  apply (frule_tac d="d" in ASMcore_consis_current_instr, simp)
  apply (insert nop_execution [where d="Step d"])
  apply clarsimp
  apply (simp add: add_pc_plus)
 apply clarsimp
 apply (insert instr_list_content [where i="1" and l="Suc (Suc 0)" and ad="dpc d" and d="Step d"])
 apply clarsimp
apply clarsimp
apply (insert instr_list_content [where i="0" and l="Suc (Suc 0)" and ad="dpc d" and d="d"])
apply clarsimp
done


lemma addi_execution[rule_format]: "asm_executes_precondition d rangee [Iaddi dr sr i] 
                                         \<longrightarrow> asm_executes d rangee 1 (dpc d + 4) (d \<lparr> dpc := dpc d + 4,
                                                                                     pcp := pcp d + 4,
                                                                                     gprs := (gprs d) [ dr := int_add (reg (gprs d) sr) i] \<rparr>)"
apply clarsimp
apply (simp add: asm_executes_precondition_def)
apply (simp add: asm_executes_def)
apply clarsimp
apply (subgoal_tac "current_instr d = Iaddi dr sr i")
 apply (subgoal_tac "Step d = d\<lparr>dpc := dpc d + 4, pcp := 8 + dpc d, gprs := gprs d[dr := int_add (reg (gprs d) sr) i]\<rparr>")
  apply (frule_tac d="d" in ASMcore_consis_current_instr, simp)
  apply clarsimp
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

lemma beqz_addi_execution1[rule_format]: "asm_executes_precondition d rangee [Ibeqz r dist, Iaddi dr sr i]
                                            \<longrightarrow> reg (gprs d) r \<noteq> 0
                                            \<longrightarrow> asm_nat (add_pc (pcp d) 8)
                                            \<longrightarrow> asm_executes d rangee 2 (pcp d + 4) (d \<lparr> dpc := pcp d + 4,
                                                                                        pcp := pcp d + 8,
                                                                                        gprs := (gprs d) [ dr := int_add (reg (gprs d) sr) i]
                                                                                      \<rparr> )"
apply clarsimp
apply (simp add: asm_executes_precondition_def)
apply (simp add: asm_executes_def)
apply clarsimp
 apply (simp add: BigStep_decompose)
apply (subgoal_tac "current_instr d = Ibeqz r dist")
 apply (frule_tac d="d" in ASMcore_consis_current_instr, simp)
 apply (insert beqz_execution1 [where d="d" and r="r" and dist="dist"])
 apply clarsimp
 apply (simp add: add_pc_plus)
 apply (insert asm_nat_monotonic [where x="8 + dpc d" and n="12 + dpc d"])
 apply clarsimp
 apply (subgoal_tac "current_instr (Step d) = Iaddi dr sr i")
  apply (frule_tac d="d\<lparr>dpc := dpc d + 4, pcp := 8 + dpc d\<rparr>" in ASMcore_consis_current_instr)
   apply (simp add: asm_executes_precondition_def)
  apply clarsimp
  apply (simp add: Step_def)
  apply (simp add: arith_exec_def)
  apply (simp add: inc_pcs_st_def)
  apply (subgoal_tac "inc_pcp_by (8 + dpc d) (int wlen_byte) = 12 + dpc d")
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

lemma beqz_addi_execution2[rule_format]: "asm_executes_precondition d rangee [Ibeqz r dist, Iaddi dr sr i]
                                            \<longrightarrow> reg (gprs d) r = 0
                                            \<longrightarrow> asm_nat ((add_pc (dpc d + 4) dist) + 4)
                                            \<longrightarrow> asm_int dist
                                            \<longrightarrow> 0 \<le> int (dpc d) + 4 + dist
                                            \<longrightarrow> asm_executes d rangee 2 (add_pc (pcp d) dist) (d \<lparr> dpc := add_pc (pcp d) dist,
                                                                                        pcp := (add_pc (pcp d) dist) + 4,
                                                                                        gprs := (gprs d) [ dr := int_add (reg (gprs d) sr) i]
                                                                                      \<rparr> )"
apply clarsimp
apply (simp add: asm_executes_precondition_def)
apply (simp add: asm_executes_def)
apply clarsimp
apply (simp add: BigStep_decompose)
apply (subgoal_tac "4 \<le> snd rangee")
 apply (subgoal_tac "current_instr d = Ibeqz r dist")
  apply (frule_tac d="d" in ASMcore_consis_current_instr, simp)
  apply (insert beqz_execution2 [where d="d" and r="r" and dist="dist"])
  apply clarsimp
  apply (insert asm_nat_monotonic [where x="add_pc (dpc d + 4) dist" and n="add_pc (dpc d + 4) dist + 4"])
  apply simp
  apply (subgoal_tac "current_instr (Step d) = Iaddi dr sr i")
   apply (frule_tac d="d\<lparr>dpc := dpc d + 4, pcp := add_pc (dpc d + 4) dist\<rparr>" in ASMcore_consis_current_instr, simp)
   apply (frule_tac d="d" in ASMcore_consis_current_instr, simp)
   apply (simp add: Step_def)
   apply (simp add: arith_exec_def)
   apply (simp add: inc_pcs_st_def)
   apply (subgoal_tac "inc_pcp_by (add_pc (dpc d + 4) dist) (int wlen_byte) = add_pc (dpc d + 4) dist + 4")
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
apply clarsimp
apply (simp add: inside_range_def)
done

lemma bnez_addi_execution1[rule_format]: "asm_executes_precondition d rangee [Ibnez r dist, Iaddi dr sr i]
                                            \<longrightarrow> reg (gprs d) r = 0
                                            \<longrightarrow> asm_nat (add_pc (pcp d) 8)
                                            \<longrightarrow> asm_executes d rangee 2 (pcp d + 4) (d \<lparr> dpc := pcp d + 4,
                                                                                        pcp := pcp d + 8,
                                                                                        gprs := (gprs d) [ dr := int_add (reg (gprs d) sr) i]
                                                                                      \<rparr> )"
apply clarsimp
apply (simp add: asm_executes_precondition_def)
apply (simp add: asm_executes_def)
apply clarsimp
 apply (simp add: BigStep_decompose)
apply (subgoal_tac "current_instr d = Ibnez r dist")
 apply (frule_tac d="d" in ASMcore_consis_current_instr, simp)
 apply (insert bnez_execution1 [where d="d" and r="r" and dist="dist"])
 apply clarsimp
 apply (simp add: add_pc_plus)
 apply (insert asm_nat_monotonic [where x="8 + dpc d" and n="12 + dpc d"])
 apply clarsimp
 apply (subgoal_tac "current_instr (Step d) = Iaddi dr sr i")
  apply (frule_tac d="d\<lparr>dpc := dpc d + 4, pcp := 8 + dpc d\<rparr>" in ASMcore_consis_current_instr)
   apply (simp add: asm_executes_precondition_def)
  apply clarsimp
  apply (simp add: Step_def)
  apply (simp add: arith_exec_def)
  apply (simp add: inc_pcs_st_def)
  apply (subgoal_tac "inc_pcp_by (8 + dpc d) (int wlen_byte) = 12 + dpc d")
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

lemma bnez_addi_execution2[rule_format]: "asm_executes_precondition d rangee [Ibnez r dist, Iaddi dr sr i]
                                            \<longrightarrow> reg (gprs d) r \<noteq> 0
                                            \<longrightarrow> asm_nat ((add_pc (dpc d + 4) dist) + 4)
                                            \<longrightarrow> asm_int dist
                                            \<longrightarrow> 0 \<le> int (dpc d) + 4 + dist
                                            \<longrightarrow> asm_executes d rangee 2 (add_pc (pcp d) dist) (d \<lparr> dpc := add_pc (pcp d) dist,
                                                                                        pcp := (add_pc (pcp d) dist) + 4,
                                                                                        gprs := (gprs d) [ dr := int_add (reg (gprs d) sr) i]
                                                                                      \<rparr> )"
apply clarsimp
apply (simp add: asm_executes_precondition_def)
apply (simp add: asm_executes_def)
apply clarsimp
apply (simp add: BigStep_decompose)
apply (subgoal_tac "4 \<le> snd rangee")
 apply (subgoal_tac "current_instr d = Ibnez r dist")
  apply (frule_tac d="d" in ASMcore_consis_current_instr, simp)
  apply (insert bnez_execution2 [where d="d" and r="r" and dist="dist"])
  apply clarsimp
  apply (insert asm_nat_monotonic [where x="add_pc (dpc d + 4) dist" and n="add_pc (dpc d + 4) dist + 4"])
  apply simp
  apply (subgoal_tac "current_instr (Step d) = Iaddi dr sr i")
   apply (frule_tac d="d\<lparr>dpc := dpc d + 4, pcp := add_pc (dpc d + 4) dist\<rparr>" in ASMcore_consis_current_instr, simp)
   apply (frule_tac d="d" in ASMcore_consis_current_instr, simp)
   apply (simp add: Step_def)
   apply (simp add: arith_exec_def)
   apply (simp add: inc_pcs_st_def)
   apply (subgoal_tac "inc_pcp_by (add_pc (dpc d + 4) dist) (int wlen_byte) = add_pc (dpc d + 4) dist + 4")
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
apply clarsimp
apply (simp add: inside_range_def)
done

lemma andi_execution[rule_format]: "asm_executes_precondition d rangee [Iandi dr sr i]
                                         \<longrightarrow> asm_executes d rangee 1 (dpc d + 4) (d \<lparr> dpc := dpc d + 4,
                                                                                     pcp := pcp d + 4,
                                                                                     gprs := (gprs d) [ dr := s_and (reg (gprs d) sr) i ] \<rparr>)"
apply clarsimp
apply (simp add: asm_executes_precondition_def)
apply (simp add: asm_executes_def)
apply clarsimp
apply (subgoal_tac "current_instr d = Iandi dr sr i")
 apply (subgoal_tac "Step d = d\<lparr>dpc := dpc d + 4, pcp := 8 + dpc d, gprs := gprs d[dr := s_and (reg (gprs d) sr) i]\<rparr>")
  apply (frule_tac d="d" in ASMcore_consis_current_instr, simp)
  apply clarsimp
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

declare intwd_as_nat_0[simp del];
declare intwd_as_nat_4[simp del];
declare intwd_as_nat_8[simp del];
declare intwd_as_nat_12[simp del];

lemma andi_mask_is_mod:
  assumes
    asm: "asm_executes_precondition d rangee [Iandi dr sr i]" and
    i: "i > 0" and
    n: "nat(i) = 2^n - Suc 0" and
    sr: "(reg (gprs d) sr) \<ge> 0"
  shows
    "asm_executes d rangee 1 (dpc d + 4)
      (d \<lparr>dpc := dpc d + 4, 
          pcp := pcp d + 4, 
          gprs := (gprs d) [ dr := int( (nat(reg (gprs d) sr)) mod (nat(i)+1)) ] \<rparr>)"
proof -
  let ?a = "reg (gprs d) sr"
  from asm have 
    "asm_executes d rangee 1 (dpc d + 4) 
        (d\<lparr>dpc := dpc d + 4, pcp := pcp d + 4, gprs := (gprs d) [dr := s_and ?a i]\<rparr>)"
    by (frule andi_execution)
  moreover
  have int_and: "s_and ?a i = (int((nat ?a) mod ((nat i) + 1)))" 
  proof -
    (* Note: possible alternative via u_and_s_and_eq and u_and_power2_minus1 ? *)
    from i and n have ngt0: "n > 0" 
    proof (cases n)
      case 0 with i and n show ?thesis by simp 
    next
      case (Suc m) thus ?thesis by simp
    qed
    moreover from n and ngt0 
    have repl: "nat_to_bv (nat i) = replicate n (1::bit)" 
      by (simp add: nat_to_bv_power2_minus1)
    moreover from repl and ngt0 
    have "\<exists> z>0. nat_to_bv (nat i) = replicate z (1::bit)" by auto
    note mask_is_mod [where a = "nat ?a" and b = "nat i", OF this]
    ultimately  
    show ?thesis using sr and i 
      by - auto
  qed
  ultimately show ?thesis by simp
qed

lemma xor_execution[rule_format]: "asm_executes_precondition d rangee [Ixor dr sr srr] 
                                         \<longrightarrow> asm_executes d rangee 1 (dpc d + 4) (d \<lparr> dpc := dpc d + 4,
                                                                                     pcp := pcp d + 4,
                                                                                     gprs := (gprs d) [dr := s_xor (reg (gprs d) sr) (reg (gprs d) srr)]\<rparr>)"
apply clarsimp
apply (simp add: asm_executes_precondition_def)
apply (simp add: asm_executes_def)
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
apply (frule_tac d="d" in ASMcore_consis_current_instr, simp)
apply clarsimp
done

lemma slli_execution [rule_format]: "asm_executes_precondition d rangee [Islli dr sr i]
  \<longrightarrow> asm_executes d rangee 1 (dpc d + 4) (d \<lparr> dpc := dpc d + 4, pcp := pcp d + 4, gprs := (gprs d) [dr := sllog (reg (gprs d) sr) (int i)]\<rparr>) "
apply clarsimp
apply (simp add: asm_executes_precondition_def)
apply (simp add: asm_executes_def)
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
apply (frule_tac d="d" in ASMcore_consis_current_instr, simp)
apply clarsimp
done

lemma and_execution [rule_format]: "asm_executes_precondition d rangee [Iand dr srl srr]
                                         \<longrightarrow> asm_executes d rangee 1 (dpc d + 4) (d \<lparr> dpc := dpc d + 4,
                                                                                     pcp := pcp d + 4,
                                                                                     gprs := (gprs d)[dr := s_and (reg (gprs d) srl) (reg (gprs d) srr)]\<rparr>)"
apply clarify
apply (simp add: asm_executes_precondition_def)
apply (simp add: asm_executes_def)
apply clarsimp
apply (subgoal_tac "current_instr d = (Iand dr srl srr)")
  prefer 2
  apply (simp add: current_instr_def)
  apply (simp add: get_instr_list_def instr_mem_read_def)
apply (frule_tac d="d" in ASMcore_consis_current_instr, simp)
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
done

lemma or_execution [rule_format]: "asm_executes_precondition d rangee [Ior dr srl srr]
                                         \<longrightarrow> asm_executes d rangee 1 (dpc d + 4) (d \<lparr> dpc := dpc d + 4,
                                                                                     pcp := pcp d + 4,
                                                                                     gprs := (gprs d)[dr := s_or (reg (gprs d) srl) (reg (gprs d) srr)] \<rparr>)"
apply clarify
apply (simp add: asm_executes_precondition_def)
apply (simp add: asm_executes_def)
apply clarsimp
apply (subgoal_tac "current_instr d = (Ior dr srl srr)")
  prefer 2
  apply (simp add: current_instr_def)
  apply (simp add: get_instr_list_def instr_mem_read_def)
apply (frule_tac d="d" in ASMcore_consis_current_instr, simp)
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
done

lemma sls_execution_1 [rule_format]: "asm_executes_precondition d rangee [Isls dr srl srr]
\<longrightarrow> reg (gprs d) srl < reg (gprs d) srr 
\<longrightarrow> asm_executes d rangee 1 (dpc d + 4) (d \<lparr> dpc := dpc d + 4, pcp := pcp d + 4, gprs := (gprs d)[dr := 1]\<rparr>) "
apply clarify
apply (simp add: asm_executes_precondition_def)
apply (simp add: asm_executes_def)
apply clarsimp
apply (subgoal_tac "current_instr d = (Isls dr srl srr)")
  prefer 2
  apply (simp add: current_instr_def)
  apply (simp add: get_instr_list_def instr_mem_read_def)
apply (frule_tac d="d" in ASMcore_consis_current_instr, simp)
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
done

lemma sls_execution_0 [rule_format]: "asm_executes_precondition d rangee [Isls dr srl srr]
\<longrightarrow> reg (gprs d) srl \<ge> reg (gprs d) srr 
\<longrightarrow> asm_executes d rangee 1 (dpc d + 4) (d \<lparr> dpc := dpc d + 4, pcp := pcp d + 4, gprs := (gprs d)[dr := 0]\<rparr>) "
apply clarify
apply (simp add: asm_executes_precondition_def)
apply (simp add: asm_executes_def)
apply clarsimp
apply (subgoal_tac "current_instr d = (Isls dr srl srr)")
  prefer 2
  apply (simp add: current_instr_def)
  apply (simp add: get_instr_list_def instr_mem_read_def)
apply (frule_tac d="d" in ASMcore_consis_current_instr, simp)
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
done

lemma sgei_execution_1 [rule_format]: "asm_executes_precondition d rangee [Isgei dr sr i]
\<longrightarrow> reg (gprs d) sr \<ge> i
\<longrightarrow> asm_executes d rangee 1 (dpc d + 4) (d \<lparr> dpc := dpc d + 4, pcp := pcp d + 4, gprs := (gprs d)[dr := 1]\<rparr>) "
apply clarify
apply (simp add: asm_executes_precondition_def)
apply (simp add: asm_executes_def)
apply clarsimp
apply (subgoal_tac "current_instr d = (Isgei dr sr i)")
  prefer 2
  apply (simp add: current_instr_def)
  apply (simp add: get_instr_list_def instr_mem_read_def)
apply (frule_tac d="d" in ASMcore_consis_current_instr, simp)
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
done

declare split_if[split del]

lemma sgei_execution_0 [rule_format]: "asm_executes_precondition d rangee [Isgei dr sr i]
\<longrightarrow> reg (gprs d) sr < i 
\<longrightarrow> asm_executes d rangee 1 (dpc d + 4) (d \<lparr> dpc := dpc d + 4, pcp := pcp d + 4, gprs := (gprs d)[dr := 0]\<rparr>) "
apply clarify
apply (simp add: asm_executes_precondition_def)
apply (simp add: asm_executes_def)
apply clarsimp
apply (subgoal_tac "current_instr d = (Isgei dr sr i)")
  prefer 2
  apply (simp add: current_instr_def)
  apply (simp add: get_instr_list_def instr_mem_read_def)
apply (frule_tac d="d" in ASMcore_consis_current_instr, simp)
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
done

lemma seq_execution[rule_format]: "asm_executes_precondition d rangee [Iseq dr lr rr] 
                                    \<longrightarrow> asm_executes d rangee 1 (dpc d + 4) (d \<lparr> dpc := dpc d + 4,
                                                                                pcp := pcp d + 4,
                                                                                gprs := (gprs d) [dr := if (reg (gprs d) lr) = (reg (gprs d) rr) then 1 else 0]\<rparr>)"
apply clarsimp
apply (simp add: asm_executes_precondition_def)
apply (simp add: asm_executes_def)
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
apply (frule_tac d="d" in ASMcore_consis_current_instr, simp)
apply clarsimp
done

lemma sne_execution[rule_format]: "asm_executes_precondition d rangee [Isne dr lr rr] 
                                    \<longrightarrow> asm_executes d rangee 1 (dpc d + 4) (d \<lparr> dpc := dpc d + 4,
                                                                                pcp := pcp d + 4,
                                                                                gprs := (gprs d) [dr := if (reg (gprs d) lr) \<noteq> (reg (gprs d) rr) then 1 else 0]\<rparr>)"
apply clarsimp
apply (simp add: asm_executes_precondition_def)
apply (simp add: asm_executes_def)
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
apply (frule_tac d="d" in ASMcore_consis_current_instr, simp)
apply clarsimp
done

lemma sle_execution[rule_format]: "asm_executes_precondition d rangee [Isle dr lr rr] 
                                    \<longrightarrow> asm_executes d rangee 1 (dpc d + 4) (d \<lparr> dpc := dpc d + 4,
                                                                                pcp := pcp d + 4,
                                                                                gprs := (gprs d) [dr := if (reg (gprs d) lr) \<le> (reg (gprs d) rr) then 1 else 0]\<rparr>)"
apply clarsimp
apply (simp add: asm_executes_precondition_def)
apply (simp add: asm_executes_def)
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
apply (frule_tac d="d" in ASMcore_consis_current_instr, simp)
apply clarsimp
done

lemma sls_execution[rule_format]: "asm_executes_precondition d rangee [Isls dr lr rr] 
                                    \<longrightarrow> asm_executes d rangee 1 (dpc d + 4) (d \<lparr> dpc := dpc d + 4,
                                                                                pcp := pcp d + 4,
                                                                                gprs := (gprs d) [dr := if (reg (gprs d) lr) < (reg (gprs d) rr) then 1 else 0]\<rparr>)"
apply clarsimp
apply (simp add: asm_executes_precondition_def)
apply (simp add: asm_executes_def)
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
apply (frule_tac d="d" in ASMcore_consis_current_instr, simp)
apply clarsimp
done

declare split_if[split]

lemma bnez_sll_execution1[rule_format]: "asm_executes_precondition d rangee [Ibnez r dist, Isll lr lr rr]
                                            \<longrightarrow> reg (gprs d) r \<noteq> 0
                                            \<longrightarrow> asm_nat ((add_pc (dpc d + 4) dist) + 4)
                                            \<longrightarrow> asm_int dist
                                            \<longrightarrow> 0 \<le> int (dpc d) + 4 + dist
                                            \<longrightarrow> asm_executes d rangee 2 (add_pc (pcp d) dist) (d \<lparr> dpc := add_pc (pcp d) dist,
                                                                                        pcp := (add_pc (pcp d) dist) + 4,
                                                                                        gprs := (gprs d) [ lr := sllog (reg (gprs d) lr) (reg (gprs d) rr)]\<rparr>)"
apply clarsimp
apply (simp add: asm_executes_precondition_def)
apply (simp add: asm_executes_def)
apply clarsimp
apply (simp add: BigStep_decompose)
apply (subgoal_tac "current_instr d = Ibnez r dist")
  prefer 2
  apply (insert instr_list_content [where i="0" and l="Suc (Suc 0)" and ad="dpc d" and d="d"])
  apply clarsimp
apply (frule_tac d="d" in ASMcore_consis_current_instr, simp)
apply (insert bnez_execution2 [where d="d" and r="r" and dist="dist"])
apply clarsimp
apply (insert asm_nat_monotonic [where x="add_pc (dpc d + 4) dist" and n="add_pc (dpc d + 4) dist + 4"])
apply simp
apply (subgoal_tac "current_instr (Step d) = (Isll lr lr rr)")
  prefer 2
  apply clarsimp
  apply (insert instr_list_content [where i="1" and l="Suc (Suc 0)" and ad="dpc d" and d="Step d"])
  apply clarsimp
apply (frule_tac d="d\<lparr>dpc := dpc d + 4, pcp := add_pc (dpc d + 4) dist\<rparr>" in ASMcore_consis_current_instr, simp)
apply (frule_tac d="d" in ASMcore_consis_current_instr, simp)
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
apply simp
done

lemma sub_execution[rule_format]: "asm_executes_precondition d rangee [Isub dr sr1 sr2] 
                                         \<longrightarrow> asm_executes d rangee 1 (dpc d + 4) (d \<lparr> dpc := dpc d + 4,
                                                                                     pcp := pcp d + 4,
                                                                                     gprs := (gprs d) [ dr := int_sub (reg (gprs d) sr1) (reg (gprs d) sr2)] \<rparr>)"
apply clarsimp
apply (simp add: asm_executes_precondition_def)
apply (simp add: asm_executes_def)
apply clarsimp
apply (subgoal_tac "current_instr d = Isub dr sr1 sr2")
 apply (subgoal_tac "Step d = d\<lparr>dpc := dpc d + 4, pcp := 8 + dpc d, gprs := gprs d[dr := int_sub (reg (gprs d) sr1) (reg (gprs d) sr2)]\<rparr>")
  apply (frule_tac d="d" in ASMcore_consis_current_instr, simp)
  apply clarsimp
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

lemma subi_execution[rule_format]: "asm_executes_precondition d rangee [Isubi dr sr i] 
                                         \<longrightarrow> asm_executes d rangee 1 (dpc d + 4) (d \<lparr> dpc := dpc d + 4,
                                                                                     pcp := pcp d + 4,
                                                                                     gprs := (gprs d) [ dr := int_sub (reg (gprs d) sr) i]\<rparr>)"
apply clarsimp
apply (simp add: asm_executes_precondition_def)
apply (simp add: asm_executes_def)
apply clarsimp
apply (subgoal_tac "current_instr d = Isubi dr sr i")
 apply (subgoal_tac "Step d = d\<lparr>dpc := dpc d + 4, pcp := 8 + dpc d, gprs := gprs d[dr := int_sub (reg (gprs d) sr) i]\<rparr>")
  apply (frule_tac d="d" in ASMcore_consis_current_instr, simp)
  apply clarsimp
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

lemma bnez_sub_execution1[rule_format]: "asm_executes_precondition d rangee [Ibnez r dist, Isub dr sr1 sr2]
                                            \<longrightarrow> reg (gprs d) r = 0
                                            \<longrightarrow> asm_nat (add_pc (pcp d) 8)
                                            \<longrightarrow> asm_executes d rangee 2 (pcp d + 4) (d \<lparr> dpc := pcp d + 4,
                                                                                        pcp := pcp d + 8,
                                                                                        gprs := (gprs d) [ dr := int_sub (reg (gprs d) sr1) (reg (gprs d) sr2)]
                                                                                      \<rparr> )"
apply clarsimp
apply (simp add: asm_executes_precondition_def)
apply (simp add: asm_executes_def)
apply clarsimp
apply (simp add: BigStep_decompose)
apply (subgoal_tac "current_instr d = Ibnez r dist")
 apply (frule_tac d="d" in ASMcore_consis_current_instr, simp)
 apply (insert bnez_execution1 [where d="d" and r="r" and dist="dist"])
 apply clarsimp
 apply (simp add: add_pc_plus)
 apply (insert asm_nat_monotonic [where x="8 + dpc d" and n="12 + dpc d"])
 apply clarsimp
 apply (subgoal_tac "current_instr (Step d) = Isub dr sr1 sr2")
  apply (frule_tac d="d\<lparr>dpc := dpc d + 4, pcp := 8 + dpc d\<rparr>" in ASMcore_consis_current_instr)
   apply (simp add: asm_executes_precondition_def)
  apply clarsimp
  apply (simp add: Step_def)
  apply (simp add: arith_exec_def)
  apply (simp add: inc_pcs_st_def)
  apply (subgoal_tac "inc_pcp_by (8 + dpc d) (int wlen_byte) = 12 + dpc d")
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

lemma bnez_sub_execution2[rule_format]: "asm_executes_precondition d rangee [Ibnez r dist, Isub dr sr1 sr2]
                                            \<longrightarrow> reg (gprs d) r \<noteq> 0
                                            \<longrightarrow> asm_nat ((add_pc (dpc d + 4) dist) + 4)
                                            \<longrightarrow> asm_int dist
                                            \<longrightarrow> 0 \<le> int (dpc d) + 4 + dist
                                            \<longrightarrow> asm_executes d rangee 2 (add_pc (pcp d) dist) (d \<lparr> dpc := add_pc (pcp d) dist,
                                                                                        pcp := (add_pc (pcp d) dist) + 4,
                                                                                        gprs := (gprs d) [ dr := int_sub (reg (gprs d) sr1) (reg (gprs d) sr2)]
                                                                                      \<rparr> )"
apply clarsimp
apply (simp add: asm_executes_precondition_def)
apply (simp add: asm_executes_def)
apply clarsimp
apply (simp add: BigStep_decompose)
apply (subgoal_tac "current_instr d = Ibnez r dist")
 apply (frule_tac d="d" in ASMcore_consis_current_instr, simp)
 apply (insert bnez_execution2 [where d="d" and r="r" and dist="dist"])
 apply clarsimp
 apply (insert asm_nat_monotonic [where x="add_pc (dpc d + 4) dist" and n="add_pc (dpc d + 4) dist + 4"])
 apply simp
 apply (subgoal_tac "current_instr (Step d ) = Isub dr sr1 sr2")
  apply (frule_tac d="d\<lparr>dpc := dpc d + 4, pcp := add_pc (dpc d + 4) dist\<rparr>" in ASMcore_consis_current_instr, simp)
  apply (frule_tac d="d" in ASMcore_consis_current_instr, simp)
  apply (simp add: Step_def)
  apply (simp add: arith_exec_def)
  apply (simp add: inc_pcs_st_def)
  apply (subgoal_tac "inc_pcp_by (add_pc (dpc d + 4) dist) (int wlen_byte) = add_pc (dpc d + 4) dist + 4")
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

declare Let_def[simp del]

end
