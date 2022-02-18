(**
 * Copyright (c) 2005-2008 Dirk Leinenbach, Hristo Pentchev, Alexandra Tsyban.
 * Some rights reserved, Saarland University.
 *
 * This work is licensed under the German-Jurisdiction Creative Commons
 * Attribution Non-commercial Share Alike 2.0 License.
 * See the file LIZENZ for a full copy of the license.
**)
(* $Id: Exec_properties.thy 28413 2009-06-15 18:23:35Z MatthiasDaum $ *)
theory Exec_properties imports Operations ASMcore_consis  begin

declare Let_def[simp]

lemma intwd_as_nat_int_add_split[rule_format]: "asm_nat (intwd_as_nat a + intwd_as_nat b)
                                             \<longrightarrow> intwd_as_nat (int_add a b) = intwd_as_nat a + intwd_as_nat b"
apply clarsimp
apply (simp add: int_add_def)
apply (simp add: natwd2intwd2natwd)
apply (simp add: asm_nat_impl_fit_nat)
done

lemma int_add_asm_int:
  shows "asm_int (int_add a b)"
proof -
  obtain x where "int_add a b = natwd_as_int (fit_nat x)" by (simp add: int_add_def)
  moreover have "asm_nat (fit_nat x)" by (simp add: asm_nat_fit_nat)
  ultimately show ?thesis by (simp add: asm_int_natwd_as_int)
qed

lemma intwd_as_nat_int_sub_split[rule_format]: "asm_nat (intwd_as_nat a - intwd_as_nat b) \<longrightarrow> intwd_as_nat b \<le> intwd_as_nat a
                                             \<longrightarrow> intwd_as_nat (int_sub a b) = intwd_as_nat a - intwd_as_nat b"
apply clarsimp
apply (simp add: int_sub_def)
apply (simp add: natwd2intwd2natwd)
apply (subgoal_tac "fit_nat (2 ^ wlen_bit + intwd_as_nat a - intwd_as_nat b) = fit_nat (intwd_as_nat a - intwd_as_nat b)")
 apply (simp add: asm_nat_impl_fit_nat)
apply (simp add: fit_nat_def)
apply (subgoal_tac "2 ^ wlen_bit + intwd_as_nat a - intwd_as_nat b = 2 ^ wlen_bit + (intwd_as_nat a - intwd_as_nat b)")
 apply (simp only: mod_add_self1)
apply clarsimp
done

lemma inc_pcp_by_is_plus_positive[rule_format]: "0 \<le> x \<longrightarrow> x < 2^(wlen_bit - 1) \<longrightarrow> int a + x < 2^wlen_bit \<longrightarrow> inc_pcp_by a x = nat (int a + x)"
apply clarsimp
apply (subgoal_tac "a + nat x < 2^wlen_bit")
 apply (simp add: inc_pcp_by_def)
 apply (simp add: intwd_as_nat_def)
 apply (simp add: fit_nat_def)
 apply (simp add: wlen_bit_def)
done

lemma inc_pcp_by_is_plus_negative[rule_format]: "-(2^(wlen_bit - Suc 0)) \<le> x \<longrightarrow> x < 0 \<longrightarrow> 0 \<le> int a + x \<longrightarrow> a < 2^wlen_bit \<longrightarrow> inc_pcp_by a x = nat (int a + x)"
apply clarsimp
apply (simp add: inc_pcp_by_def)
apply (simp add: fit_nat_def)
apply (simp add: intwd_as_nat_def)
apply (subgoal_tac "a + nat (x + 2^wlen_bit) = nat (2^wlen_bit + (int a +x))")
 apply clarsimp
 apply (simp add: add.commute)
 apply (subgoal_tac "nat (x + int a + 2^wlen_bit) = 2^wlen_bit + nat (x + int a)")
  apply clarsimp
  apply (subgoal_tac "nat (x + int a) < 2^wlen_bit")
  apply (simp add: wlen_bit_def)
  apply arith
 apply (simp add: wlen_bit_def)
done

lemma inc_pcp_by_is_plus_positive2[rule_format]: "0 \<le> x \<longrightarrow> x < 2^(wlen_bit - 1) \<longrightarrow> a + x < 2^wlen_bit \<longrightarrow> inc_pcp_by a (int x) = a + x"
apply clarsimp
apply (subgoal_tac "0 \<le> int x")
 apply (frule_tac a="a" and x="int x" in inc_pcp_by_is_plus_positive)
   apply (simp add: wlen_bit_def)
  apply (simp add: wlen_bit_def)
 apply (simp add: wlen_bit_def)
 apply arith
done

lemma inc_pcp_by_is_plus[rule_format]: "asm_int x \<longrightarrow> asm_nat a \<longrightarrow> 0 \<le> int a + x \<longrightarrow> asm_nat (add_pc a x) \<longrightarrow> inc_pcp_by a x = nat (int a + x)"
apply clarsimp
apply (simp add: asm_int_def asm_nat_def add_pc_def)
apply (subgoal_tac "int a + x < 2^wlen_bit")
 apply (case_tac "0 \<le> x")
  apply (simp add: inc_pcp_by_is_plus_positive)
 apply clarsimp
 apply (simp add: inc_pcp_by_is_plus_negative)
apply clarsimp
apply (subgoal_tac "nat (2^wlen_bit) = 2^wlen_bit")
 apply arith
apply (simp add: wlen_bit_def)
done

lemma inc_pcp_by_is_add_pc[rule_format]: "asm_int x \<longrightarrow> asm_nat p \<longrightarrow> 0 \<le> int p + x \<longrightarrow> asm_nat (add_pc p x) \<longrightarrow> inc_pcp_by p x = add_pc p x"
apply clarsimp
apply (frule inc_pcp_by_is_plus, simp, simp, simp)
apply (simp add: add_pc_def)
done

lemma inc_pcp_by_ident[rule_format]: "asm_nat x \<longrightarrow> 4 \<le> x \<longrightarrow> inc_pcp_by (x - 4) 4 = x"
apply clarsimp
apply (subst inc_pcp_by_is_plus_positive, simp)
  apply (simp add: wlen_bit_def)
 apply (simp add: asm_nat_def)
 apply (simp add: wlen_bit_def)
 apply arith
done

lemma add_pc_plus[rule_format]: "0 \<le> i \<longrightarrow> add_pc n i = n + nat i"
apply (simp add: add_pc_def)
apply (simp add: nat_int_plus)
done

lemma add_pc_minus[rule_format]: "i < 0 \<longrightarrow> add_pc n i = n - nat (- i)"
apply clarsimp
apply (simp add: add_pc_def)
done

lemma add_pc_greater1[rule_format]: "0 \<le> i \<longrightarrow> pc \<le> add_pc pc i"
apply (simp add: add_pc_def)
apply arith
done

lemma add_pc_greater2[rule_format]: "a \<le> b \<longrightarrow> add_pc pc a \<le> add_pc pc b"
apply (simp add: add_pc_def)
apply arith
done

lemma add_pc_interval_valid[rule_format]: "a \<le> x \<longrightarrow> x \<le> b \<longrightarrow> inside_range rangee (add_pc pc a) \<longrightarrow> inside_range rangee (add_pc pc b) \<longrightarrow> inside_range rangee (add_pc pc x)"
apply clarsimp
apply (frule_tac rangee="rangee" and a="add_pc pc a" and b="add_pc pc b" and x="add_pc pc x" in inside_range_interval)
      apply simp
    apply (simp add: add_pc_greater2)
  apply (simp add: add_pc_greater2)
apply simp
done

lemma asm_nat_monotonic[rule_format]: "asm_nat n \<longrightarrow> x \<le> n \<longrightarrow> asm_nat x"
apply (simp add: asm_nat_def)
done

lemma int_add_eq_int_sub_neg[rule_format]: "asm_int a \<longrightarrow> asm_int b \<longrightarrow> asm_int (-b) \<longrightarrow> int_add a b = int_sub a (-b)"
apply clarsimp
apply (simp add: asm_int_def asm_int_def)
apply clarsimp
apply (simp add: int_add_def int_sub_def)
apply (subgoal_tac "fit_nat (intwd_as_nat a + intwd_as_nat b) = fit_nat (2 ^ wlen_bit + intwd_as_nat a - intwd_as_nat (- b))")
 apply clarsimp
apply (simp add: fit_nat_def)
apply (simp add: intwd_as_nat_def)
apply auto
apply (subst diff_add_assoc2)
 apply (simp add: wlen_bit_def)
apply (subgoal_tac "2 ^ wlen_bit - nat (- b) = nat (b + 2^wlen_bit)")
 apply simp
 apply (simp add: add.commute)
apply (simp add: wlen_bit_def)
apply (subst diff_add_assoc2)
 apply (simp add: wlen_bit_def)
apply (subgoal_tac "2 ^ wlen_bit - nat (- b + 2^wlen_bit) = nat b")
 apply simp
 apply (simp add: add.commute)
apply (simp add: wlen_bit_def)
apply (subst diff_add_assoc2)
 apply (simp add: wlen_bit_def)
apply (subgoal_tac "2 ^ wlen_bit - nat (- b) = nat (b + 2^wlen_bit)")
 apply simp
 apply (simp add: add.commute)
apply (simp add: wlen_bit_def)
apply (subst diff_add_assoc2)
 apply (simp add: wlen_bit_def)
apply (subgoal_tac "2 ^ wlen_bit - nat (- b + 2^wlen_bit) = nat b")
 apply simp
 apply (simp add: add.commute)
apply (simp add: wlen_bit_def)
done

lemma int_sub_minus1 [rule_format]: "a < 2 ^ (wlen_bit - 1) - 1 \<longrightarrow> 0 \<le> a \<longrightarrow> int_sub a (- 1) = a + 1"
apply clarify
apply (cut_tac a = "a" and b = "1" in int_add_eq_int_sub_neg)
   apply (simp add: asm_int_def wlen_bit_def)
  apply (simp add: asm_int_def wlen_bit_def)
 apply (simp add: asm_int_def wlen_bit_def)
apply (erule subst)
apply (simp add: int_add_def)
apply (simp add: intwd_as_nat_def)
apply (simp add: fit_nat_def wlen_bit_def)
apply (simp add: nat_less_iff natwd_as_int_def wlen_bit_def)
done

lemma get_instr_list_butlast:"! x .get_instr_list (mm d) (dpc d) a = x
       \<longrightarrow> a = length x
       \<longrightarrow> get_instr_list (mm d) (dpc d) (a - 1) = butlast x"
  apply (induct_tac a)
  apply simp
  apply (rule allI)
  apply (intro impI)
  apply (erule_tac x = "butlast x" in allE)
  apply (elim impE)
defer
     apply simp
  apply (simp (no_asm))
prefer 2
       apply (subgoal_tac "n = Suc n - 1")
       prefer 2
       apply (simp (no_asm))
apply (rotate_tac -1, erule ssubst)
apply (simp only: get_instr_list_def) 
apply (subgoal_tac  "(mem_part_word_access (mm d) (dpc d div (4::nat)) (length x - (1::nat))) = 
                     butlast (mem_part_word_access (mm d) (dpc d div (4::nat)) (length x)) " )
apply (rotate_tac -1, erule ssubst)
apply (simp add: map_butlast)
apply (subgoal_tac "(mem_part_word_access (mm d) (dpc d div (4::nat)) (length x)) = 
                    (mem_part_word_access (mm d) (dpc d div (4::nat)) (length x - (1::nat)))@
                    (mem_part_word_access (mm d) (dpc d div (4::nat) + (length x - (1::nat))) 1)")
apply fastforce
apply (subgoal_tac "length x = (length x - 1) + 1")
apply (rotate_tac - 1, erule ssubst)
apply (simp only: mem_part_word_access_add)
apply simp
apply arith
       apply (subgoal_tac "n = Suc n - 1")
       prefer 2
       apply (simp (no_asm))
apply (rotate_tac -1, erule ssubst)
apply (simp only: get_instr_list_def) 
apply (subgoal_tac  "(mem_part_word_access (mm d) (dpc d div (4::nat)) (length x - (1::nat))) = 
                     butlast (mem_part_word_access (mm d) (dpc d div (4::nat)) (length x)) " )
apply (rotate_tac -1, erule ssubst)
apply (simp add: map_butlast)
apply (subgoal_tac "(mem_part_word_access (mm d) (dpc d div (4::nat)) (length x)) = 
                    (mem_part_word_access (mm d) (dpc d div (4::nat)) 
                    (length x - (1::nat)))@(mem_part_word_access (mm d) 
                    (dpc d div (4::nat) + (length x - (1::nat))) 1)")
apply fastforce
apply (subgoal_tac "length x = (length x - 1) + 1")
apply (rotate_tac - 1, erule ssubst)
apply (simp only: mem_part_word_access_add)
apply simp
apply arith
done

lemma dpc_pcp_BigStep[rule_format]:"! x. asm_nat(dpc d + 4 * length x + 4) 
                      \<longrightarrow> pcp d = dpc d + 4 
                      \<longrightarrow> get_instr_list (mm d) (dpc d) (length x) = x 
                      \<longrightarrow> is_not_branch_and_store_list x 
                      \<longrightarrow> a = length x
                      \<longrightarrow> dpc(BigStep d a) = dpc d + 4 * (a) \<and> 
                          pcp (BigStep d a) = pcp d + 4 * (a) \<and>  mm d = mm (BigStep d a)"
apply (induct_tac a)
 apply simp
apply (intro allI impI)
apply (simp (no_asm))
apply (erule_tac x="get_instr_list (mm d) (dpc d) ((length x) - 1)" in allE)(*butlast x*)
apply (erule impE)
 apply (subgoal_tac "(dpc d + 4 * length (get_instr_list (mm d) (dpc d) 
         (length x - (1::nat))) + 4) \<le> (dpc d + 4 * length x + 4)")
  apply (simp only: asm_nat_monotonic)
 apply (simp only: length_get_instr_list)
 apply simp
apply (erule impE)
apply (simp add: length_get_instr_list)
apply (erule impE)
 using length_get_instr_list
 apply (simp only: length_get_instr_list)
 apply (simp only: get_instr_list_butlast is_not_branch_and_store_list_def 
                   list_all_butlast)
apply (metis One_nat_def diff_Suc_1 get_instr_list_Suc list_all_append)
apply (erule impE)(*subgoal  n = length (butlast x)*)
 apply (simp only: length_get_instr_list)
apply (elim conjE)
apply (subgoal_tac "BigStep (Step d) n = Step (BigStep d n)")
 apply (simp add: Step_def current_instr_def instr_mem_read_def get_instr_list_def)
 apply (subgoal_tac "is_not_branch_and_store (cell2instr (mm (BigStep d n) 
                                             (n + dpc d div (4::nat))))")
  apply (subgoal_tac "asm_nat ( 8 + dpc (BigStep d n))")
   apply (subgoal_tac "pcp(BigStep d n)  = (dpc (BigStep d n)) + 4")
    apply (frule_tac d="BigStep d n" and 
                     i=" (cell2instr (mm (BigStep d n) (n + dpc d div (4::nat))))"in 
           is_not_branch_and_store_exec_instr, simp, simp)
    apply clarsimp
    apply (smt One_nat_def add.assoc diff_Suc_1 div_mult_self2 length_word_access zero_neq_numeral)
   apply (metis One_nat_def add.commute add.left_commute diff_Suc_1 length_word_access)
  apply (smt One_nat_def ab_semigroup_add_class.add_ac(1) add.commute add.left_commute diff_Suc_1 length_word_access mult_Suc_right numeral_Bit0)
  apply (simp add: asm_nat_def)
 apply (subgoal_tac "(mm d) (n + dpc d div (4::nat)) = 
                     (mem_part_word_access (mm d) (dpc d div (4::nat)) (length x)) ! n")
  apply (subgoal_tac "n < length (mem_part_word_access (mm d) (dpc d div (4::nat)) (length x))")
   apply (frule_tac f="cell2instr" and 
                    xs = "(mem_part_word_access (mm d) (dpc d div (4::nat)) (length x))" in 
                    nth_map)
   apply (simp add: is_not_branch_and_store_list_def)
   apply (simp add: list_all_iff)
   apply (drule_tac x="x!n" in bspec)
    apply (simp add: in_set_conv_nth)
    apply (rule_tac x="n" in exI)
    apply clarsimp
    apply (metis One_nat_def diff_Suc_1 length_word_access)
  apply (simp add: length_word_access)
 apply (subst add.commute)
 apply (simp add: word_access_content)
apply (simp add: Step_BigStep BigStep_Step)
done

lemma instr_list_content[rule_format]: 
    "i < l \<longrightarrow> dpc d = ad + 4 * i \<longrightarrow> 
     current_instr d = (get_instr_list (mm d) ad l)!i"
apply clarsimp
apply (simp add: get_instr_list_def)
apply (simp add: current_instr_def)
apply (simp add: instr_mem_read_def)
apply (frule_tac ad="ad div 4" and i="i" and len="l" and memory="mm d" in word_access_content)
apply (simp add: length_word_access)
apply (simp add: add.commute)
done

lemma store_to_mem_mem_unchanged[rule_format]: "y \<le> b \<longrightarrow> mem_unchanged m (store_to_mem m b ba l d) x y"
apply clarsimp
apply (simp add: store_to_mem_def mem_unchanged_def)
apply (simp add: mem_unchanged_word_def)
apply clarsimp
apply (rename_tac i)
apply (simp add: data_mem_write_def)
apply clarsimp
apply arith
done

lemma data_mem_write_mem_unchanged[rule_format]: "\<not> inside_range rangee b \<longrightarrow> 4 dvd (fst rangee) \<longrightarrow> 4 dvd b \<longrightarrow> mem_unchanged m (data_mem_write m b d) (fst rangee) (snd rangee)"
apply clarsimp
apply (simp add: mem_unchanged_def)
apply (simp add: mem_unchanged_word_def)
apply (simp add: inside_range_def)
apply clarsimp
apply (rename_tac i)
apply (simp add: data_mem_write_def)
apply clarsimp
apply (case_tac "fst rangee \<le> b")
 apply clarsimp
 apply arith
apply clarsimp
apply (frule_tac k="4" and a="b" and b="fst rangee" in dvd_div_less_n, simp+)
done

lemma data_mem_write_mem_unchanged3[rule_format]: "\<not> inside_range (l, r) b
                                                        \<longrightarrow> 4 dvd l
                                                        \<longrightarrow> 4 dvd r
                                                        \<longrightarrow> 4 dvd b
                                                        \<longrightarrow> mem_unchanged m (data_mem_write m b d) l r"
apply clarsimp
apply (simp add: mem_unchanged_def)
apply (simp add: mem_unchanged_word_def)
apply (simp add: inside_range_def)
apply clarsimp
apply (rename_tac i)
apply (simp add: data_mem_write_def)
apply clarsimp
apply (case_tac "l \<le> b")
 apply clarsimp
 apply arith
apply clarsimp
apply (frule_tac k="4" and a="b" and b="l" in dvd_div_less_n, simp+)
done

lemma data_mem_write_mem_unchanged2[rule_format]: "\<not> inside_range (fst rangee, snd rangee) b
                                                        \<longrightarrow> 4 dvd (fst rangee)
                                                        \<longrightarrow> 4 dvd (snd rangee)
                                                        \<longrightarrow> 4 dvd b
                                                        \<longrightarrow> mem_unchanged m (data_mem_write m b d) (fst rangee) (snd rangee)"
apply clarsimp
apply (simp add: data_mem_write_mem_unchanged3)
done

text{*instructions which are evaluated with @{text arith_exec} *}

primrec use_arith_load_comp_exec :: "instr\<Rightarrow> regname \<Rightarrow> bool"
where
  "use_arith_load_comp_exec (Ilb RD rs imm) dreg = (dreg = RD)"
 | "use_arith_load_comp_exec (Ilh RD rs imm) dreg = (dreg = RD)"
 | "use_arith_load_comp_exec (Ilw RD rs imm) dreg = (dreg = RD)"
 | "use_arith_load_comp_exec (Ilbu RD rs imm) dreg = (dreg = RD)"
 | "use_arith_load_comp_exec (Ilhu RD rs imm) dreg = (dreg = RD)"
 | "use_arith_load_comp_exec (Isb RD rs imm) dreg = False"
 | "use_arith_load_comp_exec (Ish RD rs imm) dreg = False"
 | "use_arith_load_comp_exec (Isw RD rs imm) dreg = False"

 | "use_arith_load_comp_exec (Ilhgi RD imm) dreg = (dreg = RD)"
 | "use_arith_load_comp_exec (Ilhg RD rs) dreg = (dreg = RD)"

 | "use_arith_load_comp_exec (Imovs2i RD SA) dreg = False"
 | "use_arith_load_comp_exec (Imovi2s SA rs) dreg = False"

 | "use_arith_load_comp_exec (Iaddio RD rs imm) dreg = (dreg = RD)"
 | "use_arith_load_comp_exec (Iaddi RD rs imm) dreg = (dreg = RD)"
 | "use_arith_load_comp_exec (Isubio RD rs imm) dreg = (dreg = RD)"
 | "use_arith_load_comp_exec (Isubi RD rs imm) dreg = (dreg = RD)"
 | "use_arith_load_comp_exec (Iandi RD rs imm) dreg = (dreg = RD)"
 | "use_arith_load_comp_exec (Iori RD rs imm) dreg = (dreg = RD)"
 | "use_arith_load_comp_exec (Ixori RD rs imm) dreg = (dreg = RD)"

 | "use_arith_load_comp_exec (Iaddo RD RS1 RS2) dreg = (dreg = RD)"
 | "use_arith_load_comp_exec (Iadd RD RS1 RS2) dreg = (dreg = RD)"
 | "use_arith_load_comp_exec (Isubo RD RS1 RS2) dreg = (dreg = RD)"
 | "use_arith_load_comp_exec (Isub RD RS1 RS2) dreg = (dreg = RD)"
 | "use_arith_load_comp_exec (Iand RD RS1 RS2) dreg = (dreg = RD)"
 | "use_arith_load_comp_exec (Ior RD RS1 RS2) dreg = (dreg = RD)"
 | "use_arith_load_comp_exec (Ixor RD RS1 RS2) dreg = (dreg = RD)"

 | "use_arith_load_comp_exec (Iclri RD) dreg = (dreg = RD)"
 | "use_arith_load_comp_exec (Isgri RD rs imm) dreg = (dreg = RD)"
 | "use_arith_load_comp_exec (Iseqi RD rs imm) dreg = (dreg = RD)"
 | "use_arith_load_comp_exec (Isgei RD rs imm) dreg = (dreg = RD)"
 | "use_arith_load_comp_exec (Islsi RD rs imm) dreg = (dreg = RD)"
 | "use_arith_load_comp_exec (Isnei RD rs imm) dreg = (dreg = RD)"
 | "use_arith_load_comp_exec (Islei RD rs imm) dreg = (dreg = RD)"
 | "use_arith_load_comp_exec (Iseti RD) dreg = (dreg = RD)"

 | "use_arith_load_comp_exec (Iclr RD) dreg = (dreg = RD)"
 | "use_arith_load_comp_exec (Isgr RD RS1 RS2) dreg = (dreg = RD)"
 | "use_arith_load_comp_exec (Iseq RD RS1 RS2) dreg = (dreg = RD)"
 | "use_arith_load_comp_exec (Isge RD RS1 RS2) dreg = (dreg = RD)"
 | "use_arith_load_comp_exec (Isls RD RS1 RS2) dreg = (dreg = RD)"
 | "use_arith_load_comp_exec (Isne RD RS1 RS2) dreg = (dreg = RD)"
 | "use_arith_load_comp_exec (Isle RD RS1 RS2) dreg = (dreg = RD)"
 | "use_arith_load_comp_exec (Iset RD) dreg = (dreg = RD)"

 | "use_arith_load_comp_exec (Islli RD rs sa) dreg = (dreg = RD)"
 | "use_arith_load_comp_exec (Isrli RD rs sa) dreg = (dreg = RD)"
 | "use_arith_load_comp_exec (Israi RD rs sa) dreg = (dreg = RD)"
 | "use_arith_load_comp_exec (Isll RD RS1 RS2) dreg = (dreg = RD)"
 | "use_arith_load_comp_exec (Isrl RD RS1 RS2) dreg = (dreg = RD)"
 | "use_arith_load_comp_exec (Isra RD RS1 RS2) dreg = (dreg = RD)"

 | "use_arith_load_comp_exec (Ibeqz rs imm) dreg = False"
 | "use_arith_load_comp_exec (Ibnez rs imm) dreg = False"
 | "use_arith_load_comp_exec (Ijal imm) dreg = False"
 | "use_arith_load_comp_exec (Ijalr rs) dreg = False"
 | "use_arith_load_comp_exec (Ij imm) dreg = False"
 | "use_arith_load_comp_exec (Ijr rs) dreg = False"

 | "use_arith_load_comp_exec (Itrap imm) dreg = False"
 | "use_arith_load_comp_exec (Irfe) dreg = False"

lemma exec_arith_i [rule_format]:"
               use_arith_load_comp_exec i dreg
           \<longrightarrow> asm_nat (8 + dpc d)
           \<longrightarrow> pcp d = dpc d + 4 
 \<longrightarrow> mm (exec_instr d i) = mm d 
  \<and> dpc (exec_instr d i) = dpc d + 4 
  \<and> pcp (exec_instr d i) = dpc (exec_instr d i) + 4 
  \<and> (\<forall> r. r \<noteq> dreg \<longrightarrow> gprs (exec_instr d i) ! r = gprs d ! r)
  \<and> sprs (exec_instr d i) = sprs d"
 apply clarify 
 apply (simp add: asm_nat_def wlen_bit_def) 
 apply (case_tac i)
 apply simp_all
 
 apply (simp add: load_exec''_def load_exec'_def  inc_pcs_st_def inc_pcp_by_def wlen_byte_def, simp add: fit_nat_def intwd_as_nat_def wlen_bit_def)+
 apply (simp add: arith_exec_def  inc_pcs_st_def inc_pcp_by_def wlen_byte_def, simp add: fit_nat_def intwd_as_nat_def wlen_bit_def)+
 apply (simp add: comp_exec_def  inc_pcs_st_def inc_pcp_by_def wlen_byte_def, simp add: fit_nat_def intwd_as_nat_def wlen_bit_def)+
 apply (simp add: arith_exec_def  inc_pcs_st_def inc_pcp_by_def wlen_byte_def, simp add: fit_nat_def intwd_as_nat_def wlen_bit_def)+
done

lemma exec_arith_i_list [rule_format]:"\<forall> d . 
           (\<forall> i \<in> set l.  (use_arith_load_comp_exec i dreg))
           \<longrightarrow> get_instr_list (mm d) (dpc d) (length l) = l
           \<longrightarrow> asm_nat (4 + dpc d + 4 * (length l))
           \<longrightarrow> pcp d = dpc d + 4 
 \<longrightarrow> mm (BigStep d (length l)) = mm d  
  \<and> dpc (BigStep d (length l)) = dpc d + 4 * (length l) 
  \<and> pcp (BigStep d (length l)) = dpc (BigStep d (length l)) + 4
  \<and> (\<forall> r. r \<noteq> dreg \<longrightarrow> gprs (BigStep d (length l)) ! r = gprs d ! r)
  \<and> sprs (BigStep d (length l)) = sprs d"

  apply (induct l)
  apply simp
  apply (rule allI)
  apply (erule_tac x = "(Step d)" in allE)
  apply clarify
  apply (cut_tac d= "d" and i = "a" and dreg = "dreg" in exec_arith_i)
    apply simp
    apply (simp add: asm_nat_def)
    apply simp
  apply (subgoal_tac "(Step d) = (exec_instr d a)")
    prefer 2
    apply (simp add: Step_def get_instr_list_def current_instr_def instr_mem_read_def)
  apply (elim impE)
    apply simp
    apply (simp add: Step_def get_instr_list_def instr_mem_read_def)
    apply (subgoal_tac "((dpc d + 4) div 4) = (Suc (dpc d div 4))")
      prefer 2
      apply arith
    apply simp
    apply (simp add: asm_nat_def wlen_bit_def) 
    apply simp 
  apply (subgoal_tac "(BigStep d (length (a # l))) = (Step (BigStep d (length l)))")
    prefer 2 
    apply (thin_tac "Step d = exec_instr d a", simp add: Step_BigStep_swap)
  apply simp
done

text{*Jump and Branch Instructions *}

primrec is_jump_branch :: "instr\<Rightarrow>  bool"
where
  "is_jump_branch (Ilb RD rs imm) = False"
 | "is_jump_branch (Ilh RD rs imm) = False"
 | "is_jump_branch (Ilw RD rs imm) = False"
 | "is_jump_branch (Ilbu RD rs imm) = False"
 | "is_jump_branch (Ilhu RD rs imm) = False"
 | "is_jump_branch (Isb RD rs imm) = False"
 | "is_jump_branch (Ish RD rs imm) = False"
 | "is_jump_branch (Isw RD rs imm) = False"

 | "is_jump_branch (Ilhgi RD imm) = False"
 | "is_jump_branch (Ilhg RD rs) = False"

 | "is_jump_branch (Imovs2i RD SA) = False"
 | "is_jump_branch (Imovi2s SA rs) = False"

 | "is_jump_branch (Iaddio RD rs imm) = False"
 | "is_jump_branch (Iaddi RD rs imm) = False"
 | "is_jump_branch (Isubio RD rs imm) = False"
 | "is_jump_branch (Isubi RD rs imm) = False"
 | "is_jump_branch (Iandi RD rs imm) = False"
 | "is_jump_branch (Iori RD rs imm) = False"
 | "is_jump_branch (Ixori RD rs imm) = False"

 | "is_jump_branch (Iaddo RD RS1 RS2) = False"
 | "is_jump_branch (Iadd RD RS1 RS2) = False"
 | "is_jump_branch (Isubo RD RS1 RS2) = False"
 | "is_jump_branch (Isub RD RS1 RS2) = False"
 | "is_jump_branch (Iand RD RS1 RS2) = False"
 | "is_jump_branch (Ior RD RS1 RS2) = False"
 | "is_jump_branch (Ixor RD RS1 RS2) = False"

 | "is_jump_branch (Iclri RD) = False"
 | "is_jump_branch (Isgri RD rs imm) = False"
 | "is_jump_branch (Iseqi RD rs imm) = False"
 | "is_jump_branch (Isgei RD rs imm) = False"
 | "is_jump_branch (Islsi RD rs imm) = False"
 | "is_jump_branch (Isnei RD rs imm) = False"
 | "is_jump_branch (Islei RD rs imm) = False"
 | "is_jump_branch (Iseti RD) = False"

 | "is_jump_branch (Iclr RD) = False"
 | "is_jump_branch (Isgr RD RS1 RS2) = False"
 | "is_jump_branch (Iseq RD RS1 RS2) = False"
 | "is_jump_branch (Isge RD RS1 RS2) = False"
 | "is_jump_branch (Isls RD RS1 RS2) = False"
 | "is_jump_branch (Isne RD RS1 RS2) = False"
 | "is_jump_branch (Isle RD RS1 RS2) = False"
 | "is_jump_branch (Iset RD) = False"

 | "is_jump_branch (Islli RD rs sa) = False"
 | "is_jump_branch (Isrli RD rs sa) = False"
 | "is_jump_branch (Israi RD rs sa) = False"
 | "is_jump_branch (Isll RD RS1 RS2) = False"
 | "is_jump_branch (Isrl RD RS1 RS2) = False"
 | "is_jump_branch (Isra RD RS1 RS2) = False"

 | "is_jump_branch (Ibeqz rs imm) = True"
 | "is_jump_branch (Ibnez rs imm) = True"
 | "is_jump_branch (Ijal imm) = True"
 | "is_jump_branch (Ijalr rs) = True"
 | "is_jump_branch (Ij imm) = True"
 | "is_jump_branch (Ijr rs) = True"

 | "is_jump_branch (Itrap imm) = False"
 | "is_jump_branch (Irfe) = False"

lemma exec_jump_branch_i [rule_format] :"
           is_jump_branch i
           \<longrightarrow> asm_nat (8 + dpc d)
           \<longrightarrow> pcp d = dpc d + 4 
 \<longrightarrow> mm (exec_instr d i) = mm d 
  \<and> (\<forall> r. r \<noteq> GPR_ret \<longrightarrow> gprs (exec_instr d i) ! r = gprs d ! r)
  \<and> sprs (exec_instr d i) = sprs d"
  apply clarify 
  apply (simp add: asm_nat_def wlen_bit_def) 
  apply (case_tac i)
  apply (simp_all)
done

lemma not_is_jump_branch_system_is_advancing_instr[rule_format]: "\<not> is_jump_branch i
                                                                     \<longrightarrow> \<not> is_system_instr i
                                                                      \<longrightarrow> advancing_instr d i"
apply clarsimp
apply (case_tac "i")
apply simp_all
apply (simp_all add: is_system_instr_def)
apply (simp_all add: is_Irfe_def advancing_instr_def is_Itrap_def)+
done

lemma is_not_branch_and_store_impl_not_is_jump_branch[rule_format]: "is_not_branch_and_store i \<longrightarrow> \<not> is_jump_branch i"
apply (case_tac i)
apply simp_all
done

lemma not_is_jump_branch_system_store_is_advancing_instr_BigStep[rule_format]: 
      "\<forall> d. asm_nat (dpc d + 4 * n + 4)
             \<longrightarrow> 4 dvd dpc d
             \<longrightarrow> pcp d = dpc d + 4
             \<longrightarrow> list_all (\<lambda> i. is_not_branch_and_store i \<and> (\<not> is_system_instr i)) (get_instr_list (mm d) (dpc d) n)
             \<longrightarrow> (\<forall> t < n. advancing_instr (BigStep d t) (current_instr (BigStep d t)))"
apply (induct_tac n)
 apply clarsimp
apply clarsimp
apply (simp add: list_all_iff)
apply (simp add: get_instr_list_def)
apply clarsimp
apply (erule_tac x="Step d" in allE)
apply (subgoal_tac "asm_nat (8 + dpc d)")
 apply (frule_tac is_not_branch_and_store_Step, simp)
  apply (simp add: instr_mem_read_def)
 apply clarsimp

 apply (subgoal_tac "(dpc d + 4) div 4 = Suc (dpc d div 4)")
  apply simp
  apply (erule_tac x="t - 1" in allE)
  apply clarsimp
  apply (case_tac "t")
   apply clarsimp
   apply (frule is_not_branch_and_store_impl_not_is_jump_branch)
   apply (rule not_is_jump_branch_system_is_advancing_instr)
    apply (simp add: current_instr_def instr_mem_read_def)+

apply (simp add: asm_nat_def)
done

lemma int_add_is_add[rule_format]: "0 \<le> a \<longrightarrow> 0 \<le> b \<longrightarrow> a + b < 2^(wlen_bit - 1) \<longrightarrow> int_add a b = a + b"
apply clarsimp
apply (simp add: int_add_def)
apply (simp add: asm_int_intwd_as_nat)
apply (subst asm_nat_impl_fit_nat)
 apply (simp add: asm_nat_def wlen_bit_def)
apply (simp add: natwd_as_int_def)
apply (simp add: wlen_bit_def)

done  

declare Let_def[simp del]

end
