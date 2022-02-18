(**
 * Copyright (c) 2004-2009 Eyad Alkassar, Kara Abdul-Qadar, Dirk Leinenbach,
 * Hristo Pentchev, Mareike Schmidt, Alexandra Tsyban.
 * Some rights reserved, Saarland University.
 *
 * This work is licensed under the German-Jurisdiction Creative Commons
 * Attribution Non-commercial Share Alike 2.0 License.
 * See the file LIZENZ for a full copy of the license.
**)
(* $Id: Number.thy 27178 2009-04-08 16:16:37Z DirkLeinenbach $ *)
chapter {* Some theory for number conversion *}

theory Number imports Types BitOperations begin


lemma asm_int_impl_length_int_to_bv: "asm_int i \<Longrightarrow> length (int_to_bv i) \<le> wlen_bit"
apply (clarsimp simp add: asm_int_def)
apply (case_tac "0 < i")
 apply (erule length_int_to_bv_upper_limit_gt0)
 apply simp
apply (case_tac "i < -1")
 apply (erule length_int_to_bv_upper_limit_lem1)
 apply simp
apply (case_tac "i = 0", simp)
apply (case_tac "i = -1", simp add: wlen_bit_def)
apply simp
using nat_to_bv_non_Nil 
apply force
using One_nat_def length_int_to_bv_s_lsh range_impl_s_lsh_by_0
      wlen_bit_def zero_less_numeral
apply metis
done

lemma asm_int_bv_to_int: "length wx \<le> wlen_bit \<Longrightarrow> asm_int (bv_to_int wx)"
apply (simp add: asm_int_def)
apply (rule conjI)
 apply (rule_tac y = "- (2 ^ (length wx - 1))" in order_trans)
  apply simp
  apply (simp add: wlen_bit_def)
  using bv_to_int_lower_range 
  apply auto[1]
apply (rule_tac j = "2 ^ (length wx - 1)" in i_less_le_trans)
 apply (rule bv_to_int_upper_range)
apply simp
done

lemma length_nat_to_bv_upper_limit:
  assumes nk: "n \<le> 2 ^ k - 1"
  shows       "length (nat_to_bv n) \<le> k"
proof (cases "n = 0")
  case True
  thus ?thesis
    by (simp add: nat_to_bv_def nat_to_bv_helper.simps)
next
  case False
  hence n0: "0 < n" by simp
  show ?thesis
  proof (rule ccontr)
    assume "~ length (nat_to_bv n) \<le> k"
    hence "k < length (nat_to_bv n)" by simp
    hence "k \<le> length (nat_to_bv n) - 1" by arith
    hence "(2::nat) ^ k \<le> 2 ^ (length (nat_to_bv n) - 1)" by simp
    also have "... = 2 ^ (length (norm_unsigned (nat_to_bv n)) - 1)" by simp
    also have "... \<le> bv_to_nat (nat_to_bv n)"
      by (rule bv_to_nat_lower_limit) (simp add: n0)
    also have "... = n" by simp
    finally have "2 ^ k \<le> n" .
    with n0 have "2 ^ k - 1 < n" by arith
    with nk show False by simp
  qed
qed

lemma length_nat_to_bv_le_wlen_bit: 
      "asm_nat n \<Longrightarrow> length (nat_to_bv n) \<le> wlen_bit"
apply (rule length_nat_to_bv_upper_limit)
apply (simp add: asm_nat_def)
done

lemma length_nat_to_bv_asm_int : "asm_int i \<Longrightarrow> length (nat_to_bv (nat i)) < wlen_bit"
apply (simp add: asm_int_def)
apply clarsimp
apply (cut_tac x = "i" and y = "2 ^ (wlen_bit - Suc 0)" in less_int_impl_less_nat)
   apply simp
  apply assumption  
  apply (simp only: nat_pow2_eq_pow2)
apply (frule nat_upper_limit_impl_length_nat_to_bv_limit)
apply (simp add: wlen_bit_def)
done

subsection {* normalization of integer and natural numbers, bit vectors *}

definition sxt_wd :: "bv \<Rightarrow> bv" -- "sign extend up to the length of a word"
where
"sxt_wd bv == bv_extend wlen_bit (bv_msb bv) bv"

definition fill0_wd :: "bv \<Rightarrow> bv" -- "fill with 0 in front up to the length of a word"
where
"fill0_wd bv == bv_extend wlen_bit 0 bv"

lemma bv_to_int_sxt_wd_int_to_bv: "bv_to_int (sxt_wd (int_to_bv i)) = i"
apply (simp add: sxt_wd_def)
using int_to_bv_are_not_eq norm_signed_bv_extend_bv_msb
apply force
done

lemma length_fill0_wd: "asm_int i \<Longrightarrow> length (fill0_wd (int_to_bv i)) = wlen_bit"
apply (clarsimp simp add: asm_int_def wlen_bit_def fill0_wd_def bv_extend_def)
apply (subgoal_tac "length (int_to_bv i) \<le> 32")
 apply simp
apply (case_tac "0 < i")
 apply (rule length_bounded_int_to_bv, simp)
apply (case_tac "i < -1")
apply auto
 apply (rule length_bounded_int_to_bv, simp)
apply auto
done

lemma asm_int_bv_to_int_fill0_wd_int_to_bv: 
      "asm_int i \<Longrightarrow> asm_int (bv_to_int (fill0_wd (int_to_bv i)))"
apply (frule length_fill0_wd)
apply (clarsimp simp add: fill0_wd_def asm_int_def wlen_bit_def)
apply (insert bv_to_int_lower_range [of "bv_extend 32 0 (int_to_bv i)"])
apply (insert bv_to_int_upper_range [of "bv_extend 32 0 (int_to_bv i)"])
apply (intro conjI)
  apply simp
apply (erule_tac j = "2 ^ (length (bv_extend 32 0 (int_to_bv i)) - 1)" in i_less_le_trans)
apply simp
done

lemma sxt_wd_norm_signed:"length a = wlen_bit \<Longrightarrow> sxt_wd (norm_signed a) = a"
apply (simp add: wlen_bit_def)
apply (case_tac "a")
 apply simp
apply (simp add: norm_signed_Cons)
apply safe
 apply (case_tac a)
  apply simp
  apply (simp add: sxt_wd_def)
  apply (simp add: bv_extend_def wlen_bit_def) 
  apply (frule remove_b_empty)
  apply (simp add: bv_msb_def split: bit.split)
 apply (simp split: bit.split)
 apply (simp add: sxt_wd_def wlen_bit_def bv_msb_def)
apply (case_tac a)
 apply simp
 apply (simp add: sxt_wd_def)
 apply (simp add: bv_extend_def wlen_bit_def)
 apply (subst replicate_app_Cons_same)
 apply (simp add: repl_remove)
apply (subst replicate_app_Cons_same)
apply (simp add: repl_remove)
done

lemma sxt_wd_msb_normed:
      "\<lbrakk> l = length ls; 
         l \<le> wlen_bit \<rbrakk> 
     \<Longrightarrow> 
         sxt_wd (norm_signed ls) = replicate (wlen_bit - l) (bv_msb ls) @ ls"
apply clarify
apply (subgoal_tac "norm_signed ls = norm_signed (replicate (wlen_bit - length ls) (bv_msb ls) @ ls)")
 apply (subgoal_tac "length (replicate (wlen_bit - length ls) (bv_msb ls) @ ls) = 32")
  apply (simp add: sxt_wd_norm_signed)
 apply (simp add: wlen_bit_def) 
apply (simp only: norm_signed_replicate_bv_msb)
done

lemma sxt_wd_norm_signed2: "length a \<le> wlen_bit \<Longrightarrow> sxt_wd (norm_signed a) = sxt_wd a"
apply (simp add: sxt_wd_msb_normed)
apply (simp add: sxt_wd_def)
apply (simp add: bv_extend_def)
done

lemma length_sxt_wd:"length x \<le> wlen_bit \<Longrightarrow> length (sxt_wd x) = wlen_bit"
apply (simp add: sxt_wd_def wlen_bit_def bv_extend_def)
done

lemma asm_int_impl_length_sxt_wd_is_wlen_bit: 
      "asm_int a \<Longrightarrow> length (sxt_wd (int_to_bv a)) = wlen_bit"
apply (rule length_sxt_wd)
apply (erule asm_int_impl_length_int_to_bv)
done

lemma length_sxt_wd2: "length (sxt_wd w) = max wlen_bit (length w)"
apply (simp add: sxt_wd_def)
apply (simp add: length_bv_extend)
done

lemma length_bv_extend_le_wlen_bit: "\<lbrakk> k \<le> wlen_bit; length wx \<le> wlen_bit \<rbrakk> \<Longrightarrow> length (bv_extend k a wx) \<le> wlen_bit"
  by (simp add: bv_extend_def)

lemma length_wlen_bit_sxt_wd: "length w = wlen_bit \<Longrightarrow> sxt_wd w = w"
  by (simp add: sxt_wd_def bv_extend_def)

lemma asm_int_natwd_as_int: "asm_nat n \<Longrightarrow> asm_int (natwd_as_int n)"
by (clarsimp simp add: asm_nat_def asm_int_def natwd_as_int_def wlen_bit_def)

lemma asm_nat_intwd_as_nat: "asm_int i \<Longrightarrow> asm_nat (intwd_as_nat i)"
apply (clarsimp simp add: asm_int_def asm_nat_def intwd_as_nat_def wlen_bit_def)
apply (intro conjI impI)
 apply (rule int_less_impl_less, simp)+
done

lemma asm_int_natwd_as_int_eq_asm_nat: "asm_int (natwd_as_int n) = asm_nat n"
apply (simp add: asm_nat_def asm_int_def natwd_as_int_def wlen_bit_def)
apply clarsimp
apply arith
done

lemma asm_nat_intwd_as_nat_eq_asm_int: "asm_nat (intwd_as_nat i) = asm_int i"
apply (simp split: if_split_asm add: asm_int_def asm_nat_def intwd_as_nat_def wlen_bit_def)
apply auto
done

lemma intwd2natwd2intwd: "asm_int i \<Longrightarrow> natwd_as_int (intwd_as_nat i) = i"
apply (clarsimp simp add: natwd_as_int_def intwd_as_nat_def wlen_bit_def asm_int_def)
apply (intro conjI impI)
  apply (rule int_le_impl_le)
  apply simp
 apply (rule int_less_impl_less)
 apply simp
apply (subgoal_tac "nat i < 2147483648")
 apply fastforce
apply (rule int_less_impl_less)
apply simp
done

lemma natwd2intwd2natwd: "intwd_as_nat (natwd_as_int n) = n"
apply (clarsimp simp add: intwd_as_nat_def natwd_as_int_def wlen_bit_def)
done

lemma intwd_as_nat_int_trivial: "asm_int (int x) \<Longrightarrow> intwd_as_nat (int x) = x"
  by (simp add: asm_int_def intwd_as_nat_def)

lemma intwd_as_nat_0: "intwd_as_nat 0 = 0"
  by (simp add: intwd_as_nat_def wlen_bit_def)

lemma intwd_as_nat_4: "intwd_as_nat 4 = 4"
  by (simp add: intwd_as_nat_def wlen_bit_def)

lemma intwd_as_nat_8: "intwd_as_nat 8 = 8" 
  by (simp add: intwd_as_nat_def wlen_bit_def)

lemma intwd_as_nat_12: "intwd_as_nat 12 = 12"
  by (simp add: intwd_as_nat_def wlen_bit_def)

lemma intwd_as_nat_id:
 "intwd_as_nat 16 = 16"
 "intwd_as_nat 20 = 20"
 "intwd_as_nat 24 = 24"
by (simp_all add: intwd_as_nat_def wlen_bit_def)

lemma natwd_as_int_zero: "natwd_as_int 0 = 0"
  by (simp add: natwd_as_int_def)

lemma intwd_as_nat_mod_4_I: "intwd_as_nat x mod 4 = 0 \<Longrightarrow> x mod 4 = 0"
apply (simp add: intwd_as_nat_def wlen_bit_def)
apply (split if_split_asm)
 apply (simp add: wlen_bit_def)
 apply (simp add: mod_eq_0_iff)
 apply (erule exE)
 apply (simp add: zmod_eq_0_iff)
 apply (rule_tac x = "int q - 536870912" in exI)
 apply (simp add: nat_add_distrib)
apply (split if_split_asm)
 apply (simp add: wlen_bit_def)
 apply (simp add: mod_eq_0_iff)
 apply (erule exE)
 apply (simp add: zmod_eq_0_iff)
 apply (rule_tac x = "536870912 - int q" in exI)
 apply (subgoal_tac "\<exists> k. 0 < k \<and> x = -2147483648 - k")
  apply clarsimp
  apply (simp add: nat_add_distrib)
 apply (rule_tac x = "-2147483648 - x" in exI)
 apply simp
apply (split if_split_asm)
 apply (simp add: wlen_bit_def)
 apply (simp add: mod_eq_0_iff)
 apply (erule exE)
 apply (simp add: zmod_eq_0_iff)
 apply (rule_tac x = "int q - 1073741824" in exI)
 apply (subgoal_tac "\<exists> k. 0 \<le> k \<and> x = k - 2147483648")
  apply clarsimp
  apply (simp add: nat_add_distrib)
 apply (rule_tac x = "x + 2147483648" in exI)
 apply simp
apply (simp add: wlen_bit_def)
apply (simp add: mod_eq_0_iff)
apply (erule exE)
apply (simp add: zmod_eq_0_iff)
apply (rule_tac x = "int q" in exI)
apply arith
done

lemma intwd_as_nat_mod_2_I: "intwd_as_nat x mod 2 = 0 \<Longrightarrow> x mod 2 = 0"
apply (simp add: intwd_as_nat_def wlen_bit_def)
apply (split if_split_asm)
 apply (simp add: wlen_bit_def)
 apply (simp add: mod_eq_0_iff)
 apply (erule exE)
 apply (simp add: zmod_eq_0_iff)
 apply (rule_tac x = "int q - 2 * 536870912" in exI)
 apply (simp add: nat_add_distrib)
apply (split if_split_asm)
 apply (simp add: wlen_bit_def)
 apply (simp add: mod_eq_0_iff)
 apply (erule exE)
 apply (simp add: zmod_eq_0_iff)
 apply (rule_tac x = "2 * 536870912 - int q" in exI)
 apply (subgoal_tac "\<exists> k. 0 < k \<and> x = -2147483648 - k")
  apply clarsimp
  apply (simp add: nat_add_distrib)
 apply (rule_tac x = "-2147483648 - x" in exI)
 apply simp
apply (split if_split_asm)
 apply (simp add: wlen_bit_def)
 apply (simp add: mod_eq_0_iff)
 apply (erule exE)
 apply (simp add: zmod_eq_0_iff)
 apply (rule_tac x = "int q - 2 * 1073741824" in exI)
 apply (subgoal_tac "\<exists> k. 0 \<le> k \<and> x = k - 2147483648")
  apply clarsimp
  apply (simp add: nat_add_distrib)
 apply (rule_tac x = "x + 2147483648" in exI)
 apply simp
apply (simp add: wlen_bit_def)
apply (simp add: mod_eq_0_iff)
apply (erule exE)
apply (simp add: zmod_eq_0_iff)
apply (rule_tac x = "int q" in exI)
apply arith
done

lemma even_intwd_as_nat_even_int [rule_format]: 
  "(intwd_as_nat i) = 2 * n \<longrightarrow> (\<exists> m. i = 2 * m)"
apply clarify
apply (cut_tac x = "i" in intwd_as_nat_mod_2_I)
  apply simp
apply arith
done

lemma natwd_as_int_mod_4: "t mod 4 = 0 \<Longrightarrow> natwd_as_int t mod 4 = 0"
apply (rule intwd_as_nat_mod_4_I)
apply (subst natwd2intwd2natwd)
apply assumption
done

lemma intwd_as_nat_mod_4:  "x mod 4 = 0 \<Longrightarrow> intwd_as_nat x mod 4 = 0"
apply (simp add: intwd_as_nat_def wlen_bit_def)
apply (intro conjI impI)
   apply (simp add: zmod_eq_0_iff)
   apply (erule exE)
   apply (simp add: mod_eq_0_iff)
   apply (rule_tac x = "nat (- q) + 536870912" in exI)
   apply (simp add: nat_add_distrib)
  apply (simp add: zmod_eq_0_iff)
  apply (erule exE)
  apply (simp add: mod_eq_0_iff)
  apply (rule_tac x = "nat (q + 1073741824)" in exI)
  apply arith
 apply (simp add: zmod_eq_0_iff)
 apply (erule exE)
 apply (simp add: mod_eq_0_iff)
 apply (rule_tac x = "nat q + 536870912" in exI)
 apply (simp add: nat_add_distrib)
apply (simp add: zmod_eq_0_iff)
apply (erule exE)
apply (simp add: mod_eq_0_iff)
apply (rule_tac x = "nat q" in exI)
apply arith
done

lemma natwd_as_int_mod_4_I: "natwd_as_int x mod 4 = 0 \<Longrightarrow> x mod 4 = 0"
apply (drule intwd_as_nat_mod_4)
apply (simp add: natwd2intwd2natwd)
done

lemma asm_int_intwd_as_nat_impl_val:
       "\<lbrakk> intwd_as_nat t = a; asm_int t; a < 2 ^ (wlen_bit - 1) \<rbrakk>
           \<Longrightarrow> t = int a"
apply (clarsimp simp add: asm_int_def intwd_as_nat_def wlen_bit_def)
apply (subgoal_tac "2147483648 \<le> nat (t + 4294967296)")
 apply simp
apply (thin_tac "nat (t + 4294967296) < 2147483648")
apply arith
done

lemma intwd_as_nat_neq: "\<lbrakk> asm_int b; asm_int d \<rbrakk> \<Longrightarrow> (intwd_as_nat b \<noteq> intwd_as_nat d) = (b \<noteq> d)"
apply (clarsimp simp add: intwd_as_nat_def asm_int_def wlen_bit_def)
apply (intro impI conjI)
apply arith+
done

text{* Implication was replaced by IFF *}
lemma intwd_as_nat_eq: "\<lbrakk> asm_int b; asm_int d \<rbrakk> \<Longrightarrow> (intwd_as_nat b = intwd_as_nat d) = (b = d)"
apply (clarsimp simp add: intwd_as_nat_def asm_int_def wlen_bit_def)
apply (intro impI conjI)
apply arith+
done

lemma intwd_as_nat_neq1: 
  "\<lbrakk> b \<noteq> d; asm_int b; asm_int d \<rbrakk> \<Longrightarrow> intwd_as_nat b \<noteq> intwd_as_nat d"
apply (subst intwd_as_nat_eq, assumption+)
done

lemma intwd_as_nat_less_impl_pos_and_neg: 
  "\<lbrakk>intwd_as_nat d < intwd_as_nat b; asm_int d; asm_int b; b \<le> d \<rbrakk> \<Longrightarrow> 
   0 \<le> d \<and> b < 0"
apply (clarsimp simp add: intwd_as_nat_def wlen_bit_def asm_int_def)
apply (split if_split_asm)
 apply simp_all
apply (split if_split_asm)
 apply simp_all
done

lemma intwd_as_nat_less_and_neg_impl_neg: 
  "\<lbrakk>intwd_as_nat d < intwd_as_nat b; asm_int d; asm_int b; d < 0 \<rbrakk> \<Longrightarrow> b < 0"
apply (clarsimp simp add: intwd_as_nat_def wlen_bit_def asm_int_def)
apply (split if_split_asm)
 apply assumption
apply simp
done

lemma intwd_as_nat_le_and_pos_impl_pos: "\<lbrakk> intwd_as_nat b \<le> intwd_as_nat d; asm_int d; asm_int b; 0 \<le> d \<rbrakk> \<Longrightarrow> 0 \<le> b"
apply (clarsimp simp add: intwd_as_nat_def wlen_bit_def asm_int_def)
apply (split if_split_asm)
 apply simp_all
apply (subgoal_tac "nat d < nat (b + (2 ^ wlen_bit))")
 apply simp
apply (thin_tac "nat (b + (2 ^ wlen_bit)) \<le> nat d")
apply (rule of_nat_less_iff_impl)
apply (simp add: wlen_bit_def)
done

lemma intwd_as_nat_less_impl_relation_posibilities:
   "\<lbrakk> asm_int a; asm_int b; intwd_as_nat a < intwd_as_nat b \<rbrakk> \<Longrightarrow> (0 \<le> a \<and> a < b) \<or> (b < 0 \<and> a < b) \<or> (0 \<le> a \<and> b < 0)"
apply clarsimp
apply (case_tac "a = 0", simp)
apply (case_tac "0 \<le> a")
 apply (subgoal_tac "b \<le> a")
  prefer 2
  apply simp
 apply (frule intwd_as_nat_less_impl_pos_and_neg, assumption+)
 apply simp
apply (case_tac "a < 0")
 apply (frule intwd_as_nat_less_and_neg_impl_neg, assumption+)
 apply (clarsimp simp add: intwd_as_nat_def wlen_bit_def asm_int_def)
apply simp
done

lemma intwd_as_nat_le_and_neg_impl_neg: " \<lbrakk> intwd_as_nat a \<le> intwd_as_nat b; asm_int a; asm_int b; a < 0 \<rbrakk> \<Longrightarrow> b < 0"
apply (clarsimp simp add: intwd_as_nat_def wlen_bit_def asm_int_def)
apply (split if_split_asm)
 apply assumption
apply simp
done

lemma intwd_as_nat_le_impl_pos_and_neg: "\<lbrakk> intwd_as_nat a \<le> intwd_as_nat b; asm_int a; asm_int b; b < a \<rbrakk> \<Longrightarrow> 0 \<le> a \<and> b < 0"
apply (case_tac "intwd_as_nat a = intwd_as_nat b")
 apply (clarsimp simp add: intwd_as_nat_def wlen_bit_def asm_int_def)
 apply (simp split: if_split_asm)
  apply (simp add: wlen_bit_def)
apply (rule intwd_as_nat_less_impl_pos_and_neg, simp+)
done

lemma intwd_as_nat_le_impl_relation_posibilities:
   "\<lbrakk> asm_int a; asm_int b; intwd_as_nat a \<le> intwd_as_nat b \<rbrakk> \<Longrightarrow> (0 \<le> a \<and> a \<le> b) \<or> (b < 0 \<and> a \<le> b) \<or> (0 \<le> a \<and> b \<le> 0)"
apply clarsimp
apply (case_tac "a = 0", simp)
apply (case_tac "0 \<le> a")
 apply (subgoal_tac "b \<le> a")
  prefer 2
  apply simp
 apply (frule intwd_as_nat_le_impl_pos_and_neg, simp+)
apply (case_tac "a < 0")
 apply (frule intwd_as_nat_le_and_neg_impl_neg, assumption+)
 apply (clarsimp simp add: intwd_as_nat_def wlen_bit_def asm_int_def)
 apply arith
apply simp
done


lemma intwd_as_nat_meaning: 
      "asm_int x \<Longrightarrow> intwd_as_nat x = bv_to_nat (sxt_wd (int_to_bv x))"
apply (simp only: intwd_as_nat_def asm_int_def)
apply (erule conjE)
apply (case_tac "2 ^ (wlen_bit - 1) \<le> x \<and> x < 2 ^ wlen_bit", simp)
apply (case_tac " x < - (2 ^ (wlen_bit - 1))", simp)
apply (split if_split)
apply (rule conjI)
 apply simp
apply (case_tac "0 < x")
 apply (frule int_to_bv_g_0)
 apply (simp add: sxt_wd_def bv_extend_def bv_msb_def)
 apply (simp add: bv_to_nat_replicate_Zero_append)
apply (case_tac "x = 0")
 apply (frule int_to_bv_e_0)
 apply (simp add: sxt_wd_def bv_extend_def bv_msb_def)
 using bv_to_nat_replicate_Zero apply auto[1]
apply (case_tac "x < 0")
 prefer 2
 apply simp
apply (rule impI)
apply (subgoal_tac "(if x < - (2 ^ (wlen_bit - 1)) then nat (- x + 2 ^ (wlen_bit - 1))
        else if - (2 ^ (wlen_bit - 1)) \<le> x \<and> x < 0 then nat (x + 2 ^ wlen_bit) else nat x) = nat (x + 2 ^ wlen_bit)")
 prefer 2
 apply simp
apply (rotate_tac -1, erule ssubst)
apply (subgoal_tac " nat (x + 2 ^ wlen_bit) =  nat (bv_to_int (sxt_wd (int_to_bv x)) + 2 ^ wlen_bit)")
 prefer 2
 apply (simp add: sxt_wd_def)
prefer 2
apply (rotate_tac -1, erule ssubst)
apply (subgoal_tac "bv_msb (sxt_wd (int_to_bv x))  = 1")
 prefer 2
 apply (simp add: sxt_wd_def bv_msb_def bv_extend_def)
 apply (simp add: hd_append  norm_signed_One_bv_not_nat_to_bv)
apply (subgoal_tac "asm_int x")
 prefer 2
 apply (simp add: asm_int_def)
apply (frule asm_int_impl_length_int_to_bv)
apply (subgoal_tac "int_to_bv x \<noteq> []")
 prefer 2
 apply (frule int_to_bv_not_zero_is_not_empty)
 apply clarsimp
apply (subgoal_tac "length (1 # tl (sxt_wd (int_to_bv x))) = wlen_bit")
 prefer 2
 apply (simp add: sxt_wd_def wlen_bit_def bv_extend_def)
apply (subgoal_tac "0 < length (int_to_bv x)")
 prefer 2
 apply clarsimp
apply (frule_tac l = "wlen_bit" in bv_to_int_bv_to_nat_eq_one)	  
apply (subgoal_tac "(sxt_wd (int_to_bv x)) = 1 # tl (sxt_wd (int_to_bv x))")
 apply (rotate_tac -1, erule ssubst)
 apply clarsimp
 apply (simp add: norm_signed_One_bv_not_nat_to_bv  wlen_bit_def)
apply (subgoal_tac "(sxt_wd (int_to_bv x)) \<noteq> []")
 apply (simp only: bv_msb_def)
 apply (frule_tac xs ="sxt_wd (int_to_bv x)" in hd_Cons_tl)
 apply clarsimp
apply (simp only: sxt_wd_def bv_extend_is_not_empty_1)  
apply (simp add: sxt_wd_def wlen_bit_def  bv_to_int_def  bv_extend_def split: bit.split)  
apply auto
apply (metis bv_msb_def bv_msb_norm list.distinct(1) list.sel(1) norm_signed_replicate_bv_msb zero_neq_one)  
apply (auto simp add: bv_msb_def split: if_split_asm)
apply (smt bitNOT_bit.simps(2) bv_nat_bv bv_to_nat0 bv_to_nat_replicate_Zero_append complement_bv_eq int_nat_eq length_map list.simps(9) norm_signed_One_bv_not_nat_to_bv)
apply (cases x)
apply auto
apply (smt bitNOT_bit.simps(2) bv_nat_bv bv_to_nat0 bv_to_nat_replicate_Zero_append complement_bv_eq length_map list.simps(9) norm_signed_One_bv_not_nat_to_bv)
done


lemma length_nat_to_bv_lower_limit:
  assumes nk: "2 ^ k \<le> n"
  shows       "k < length (nat_to_bv n)"
proof (rule ccontr)
  assume "~ k < length (nat_to_bv n)"
  hence lnk: "length (nat_to_bv n) \<le> k" by simp
  have "n = bv_to_nat (nat_to_bv n)" by simp
  also have "... < 2 ^ length (nat_to_bv n)"
    by (rule bv_to_nat_upper_range)
  also from lnk have "... \<le> 2 ^ k" by simp
  finally have "n < 2 ^ k" .
  with nk show False by simp
qed


lemma natwd_as_int_meaning:
      "asm_nat x \<Longrightarrow> natwd_as_int x = bv_to_int (fill0_wd (nat_to_bv x))"
apply (simp add: natwd_as_int_def asm_nat_def)
apply (intro conjI impI)
 prefer 2
 apply (simp add: fill0_wd_def)
 apply (simp add: bv_extend_def)
 apply (case_tac "wlen_bit - length (nat_to_bv x)")
  apply simp
  apply (subgoal_tac "length (nat_to_bv x) \<le> wlen_bit - Suc 0")
   apply (simp add: wlen_bit_def)
  apply (rule length_nat_to_bv_upper_limit)
  apply arith
 apply simp
 apply (simp add: bv_to_nat_replicate_Zero_append)
apply (subgoal_tac "fill0_wd (nat_to_bv x) = nat_to_bv x")
 prefer 2
 apply (simp add: fill0_wd_def)
 apply (simp add: bv_extend_def)
 apply (drule length_nat_to_bv_lower_limit)
 apply (simp add: wlen_bit_def)
apply (rotate_tac -1, erule ssubst)
apply (simp add: bv_to_int_def)
apply (subgoal_tac "bv_msb (nat_to_bv x) = 1")
 prefer 2
 apply (case_tac "nat_to_bv x")
  apply (drule nat_to_bv_is_Nil_impl_nat_is_0)
  apply (simp add: wlen_bit_def)
 apply (frule nat_to_bv_Cons_impl_head_is_One)
 apply simp
apply (rotate_tac -1, erule ssubst)
apply simp
(* ================== rev. 12634 ======================
apply (subst complement_bv_eq)
apply simp
apply (drule length_nat_to_bv_lower_limit)
apply (subgoal_tac "length (nat_to_bv x) \<le> wlen_bit")
 prefer 2
 apply (rule length_nat_to_bv_upper_limit)
 apply arith
apply (simp add: wlen_bit_def)
apply (simp add: bv_msb_def)
apply (simp add: bv_msb_def wlen_bit_def split: if_split_asm)
 ================== rev. 12634 ====================== *)
sorry

lemma intwd_as_nat_sub[rule_format]: "asm_int a \<longrightarrow> b \<le> intwd_as_nat a \<longrightarrow> asm_int (a - int b) \<longrightarrow> intwd_as_nat (a - int b) = intwd_as_nat a - b"
apply clarsimp
apply (simp add: asm_int_def)
apply (simp add: intwd_as_nat_def)
apply auto
done

lemma intwd_as_nat_add[rule_format]: 
      "asm_int a \<longrightarrow> asm_int (a + int b) \<longrightarrow> asm_nat (intwd_as_nat a + b) \<longrightarrow> 
       intwd_as_nat (a + int b) = intwd_as_nat a + b"
apply clarsimp
apply (simp add: asm_int_def asm_nat_def)
apply (simp add: intwd_as_nat_def)
apply auto
apply (simp add: wlen_bit_def)+
done

lemma intwd_as_nat_zero: "intwd_as_nat x = 0 \<Longrightarrow> x=0"
apply (simp add: intwd_as_nat_def)
apply (simp split: if_split_asm)
apply (simp add: wlen_bit_def)+
done

lemma asm_int_intwd_as_nat[rule_format]: 
      "0 \<le> x \<longrightarrow> x < 2^ (wlen_bit - 1) \<longrightarrow> intwd_as_nat x = nat x"
apply clarsimp
apply (simp add: asm_int_def intwd_as_nat_def)
done

lemma asm_int_intwd_as_nat_neg: 
     "\<lbrakk> x < 0 ; - ( 2^(wlen_bit - 1)) \<le> x\<rbrakk> \<Longrightarrow> 
       intwd_as_nat x = (nat (x + 2^wlen_bit))"
  by (simp add: intwd_as_nat_def wlen_bit_def)

definition
  fit_nat :: "nat \<Rightarrow> nat"
where
  "fit_nat i == i mod 2^wlen_bit"

lemma asm_nat_fit_nat: 
      "asm_nat (fit_nat n)"
by (simp add: asm_nat_def fit_nat_def)

lemma asm_nat_impl_fit_nat: 
      "asm_nat n \<Longrightarrow> fit_nat n = n"
by (simp add: asm_nat_def fit_nat_def)

lemma fit_nat_dvd:
 "((4::nat) dvd fit_nat x) = (4 dvd x)"
proof -
  have "(4::nat) dvd 4294967296"
  by arith
  hence 1: "4 dvd fit_nat x \<Longrightarrow> 4 dvd x"
  apply (clarsimp simp add: fit_nat_def wlen_bit_def)
  by (rule_tac n = "4294967296" in dvd_mod_imp_dvd, simp_all)

  have 2:"(4::nat) dvd x \<Longrightarrow> 4 dvd fit_nat x"
   apply (clarsimp simp add: fit_nat_def wlen_bit_def)
  by (rule_tac dvd_mod, simp_all)
thus ?thesis using 1 by (simp add: iffI)
qed

lemma asm_int_impl_nat_x_mod32_eq_intwd_as_nat_x_mod_32:
      "\<lbrakk>asm_int x\<rbrakk> \<Longrightarrow> nat (x mod 32) = (intwd_as_nat x) mod 32"
apply (case_tac "0 < x")
 apply (simp add: asm_int_def intwd_as_nat_def wlen_bit_def)
 apply (subgoal_tac "int (nat (x mod (32::int)))= int((nat x) mod (32::nat)) ")
  apply simp
 apply (simp add: int_mod)
apply (simp add: asm_int_def intwd_as_nat_def wlen_bit_def)
apply clarsimp
apply (subgoal_tac "int (nat (x mod (32::int))) = 
                   int ((nat (x + (4294967296::int))) mod (32::nat)) ")
 apply simp
apply (simp add: int_mod)
apply (simp add: mod_add_eq)
done

lemma norm_unsigned_int2bvn_length_mono [rule_format] : 
      "asm_int a \<longrightarrow> asm_int b \<longrightarrow> a \<ge> 0 \<longrightarrow> b \<ge> 0 \<longrightarrow> 
       length (norm_unsigned (int2bvn wlen_bit a)) < 
       length (norm_unsigned (int2bvn wlen_bit b)) \<longrightarrow> a < b"
apply clarify
apply (simp add: int2bvn_def)
apply (frule length_nat_to_bv_asm_int)
apply (frule_tac i = "b" in length_nat_to_bv_asm_int)
apply (cut_tac w = "(0 # nat_to_bv (nat a))" in norm_signed_length)
apply (cut_tac w = "(0 # nat_to_bv (nat b))" in norm_signed_length)
apply simp
apply (case_tac "0 = a")
 apply simp
 apply (case_tac "0 = b")
  apply simp
 apply simp
apply (case_tac "0 = b")
 apply (simp add: norm_unsigned_bv_extend)
apply (cut_tac a = "nat a" in nat_to_bv_pos_not_nil)
 apply arith
apply (cut_tac a = "nat b" in nat_to_bv_pos_not_nil)
(* ================== rev. 12634 ======================
 apply arith
apply clarsimp
apply (subgoal_tac "length (nat_to_bv (nat a)) < length (nat_to_bv (nat b))")
 prefer 2
 apply (simp add: Let_def)
 apply (simp add: norm_unsigned_bv_extend)
apply (frule nat_to_bv_length_mono)
apply arith
  ================== rev. 12634 ====================== *)
sorry

text {* next definition is used only for the program verification but it is better to define it here *}

definition  regs_eq_except_from_list :: "[registers, registers, regname list] \<Rightarrow> bool"
where
  "regs_eq_except_from_list regs1 regs2 reg_ls \<equiv> (\<forall> r < 32. r \<notin> set reg_ls \<longrightarrow> regs1 ! r = regs2 ! r)"

subsection {* operations for bit vectors *}

lemma length_bv_op[rule_format]: "! r i. bv_op \<in> {op AND, op OR, op XOR} \<longrightarrow> length r = n \<longrightarrow> length i = n \<longrightarrow> length (map (\<lambda> (a, b). bv_op a b) (zip r i)) = n"
apply (induct_tac n)
 apply clarsimp
apply (intro allI impI)
apply (case_tac r, simp)
apply (case_tac i, simp)
apply (erule_tac x = "list" in allE)
apply (erule_tac x = "lista" in allE)
apply (drule mp, assumption)
apply (drule mp, simp)
apply (drule mp, simp)
apply simp
done

lemma length_bv_op_sxt_wd: "\<lbrakk>bv_op \<in> {op AND, op OR, op XOR}; length r \<le> wlen_bit; length i \<le> wlen_bit \<rbrakk> \<Longrightarrow> 
         length (map (\<lambda> (a, b). bv_op a b) (zip (bv_extend (length i) (bv_msb r) r) (bv_extend (length r) (bv_msb i) i))) \<le> wlen_bit"
apply (drule_tac n = "max (length i) (length r)" and
                 r = "bv_extend (length i) (bv_msb r) r" and 
                 i = "bv_extend (length r) (bv_msb i) i" in length_bv_op)
  prefer 3
  apply (erule ssubst)
  apply (simp add: bv_extend_def max_def)+
done

lemma bv_extend_zero_norm_unsigned_sxt_wd[rule_format]: "length x \<le> wlen_bit \<longrightarrow> bv_extend wlen_bit 0 (norm_unsigned (sxt_wd x)) = bv_extend wlen_bit (bv_msb x) x"
apply clarsimp
apply (simp add: sxt_wd_def)
apply (subst bv_extend_norm_unsigned2)
 apply (simp add: length_bv_extend  bv_extend_def wlen_bit_def bv_msb_def)+
done

lemma asm_int_s_bitop[rule_format]: "asm_int a \<longrightarrow> asm_int b \<longrightarrow> asm_int (s_bitop f a b)"
apply clarsimp
apply (simp add: asm_int_def)
apply clarsimp
apply (rule bounded_s_bitop, simp, simp)
    apply (simp add: wlen_bit_def)
apply simp+
done

lemma asm_int_bv_op: "\<lbrakk>asm_int r; asm_int i; bv_op \<in> {op AND, op OR, op XOR}\<rbrakk> \<Longrightarrow> asm_int (s_bitop bv_op r i)"
  by (simp add: asm_int_s_bitop)

lemma asm_int_int_and: "\<lbrakk> asm_int r; asm_int i \<rbrakk> \<Longrightarrow> asm_int (s_and r i)"
apply (erule asm_int_bv_op)
apply simp_all
done

lemma asm_int_int_or: "\<lbrakk> asm_int r; asm_int i \<rbrakk> \<Longrightarrow> asm_int (s_or r i)"
apply (erule asm_int_bv_op)
apply simp_all
done

lemma asm_int_int_xor: "\<lbrakk> asm_int r; asm_int i \<rbrakk> \<Longrightarrow> asm_int (s_xor r i)"
apply (erule asm_int_bv_op)
apply simp_all
done

declare Let_def[simp]

lemma int_and_1_pos: "0 \<le> x \<Longrightarrow> s_and x 1 = x mod 2"
apply (simp add: s_bitop_def)
apply (subst nat_to_bv_one[simplified])
apply (subst nat_to_bv_one[simplified])
apply simp
apply (case_tac "x = 0")
 apply simp
apply (subgoal_tac "nat_to_bv (nat x) \<noteq> []")
 prefer 2
 apply (rule ccontr)
 apply simp
 apply (drule nat_to_bv_is_Nil_impl_nat_is_0)
(* ================== rev. 12634 ======================

 apply arith
apply (subgoal_tac "norm_signed (0 # nat_to_bv (nat x)) = 0 # nat_to_bv (nat x)")
 prefer 2
 apply (case_tac "nat_to_bv (nat x)")
  apply simp
 apply simp
 apply (frule nat_to_bv_Cons_impl_head_is_One)
 apply simp
apply (rotate_tac -1, erule ssubst)
apply (subgoal_tac "map (\<lambda>(ua, u). ua AND u) 
         (zip (bv_extend (Suc (Suc 0)) 0 (0 # nat_to_bv (nat x))) 
              (bv_extend (length (0 # nat_to_bv (nat x))) 0 [0, 1])) = 
                        (replicate (length (nat_to_bv (nat x))) 0) @ [last (nat_to_bv (nat x))]")
 apply (rotate_tac -1, erule ssubst)
 apply (subgoal_tac "replicate (length (nat_to_bv (nat x))) 0 = 
                     0 # replicate (length (nat_to_bv (nat x)) - 1) 0")
  apply (rotate_tac-1, erule ssubst)
  apply (simp add: bv_to_int_def)
  apply (subst bv_to_nat_replicate_Zero_append)
  apply (subst nat_to_bv_non0)
   apply simp
  apply simp
  apply (case_tac "x mod 2 = 0")
   apply simp
   apply (subgoal_tac "nat x mod 2 = 0")
    apply simp
   apply (subst int_int_eq[THEN sym])
   apply (subst int_mod)
   apply simp
  apply simp
  apply (subst int_int_eq[THEN sym])
  apply (subst int_mod)
  apply simp
 apply (case_tac "nat_to_bv (nat x)")
  apply simp_all
apply (subst nat_to_bv_non0[of "nat x"],simp)+
apply (simp only: bv_extend_def)
apply (subgoal_tac "[0, 1] = [0] @ [1]")
 prefer 2
 apply simp
apply (rotate_tac -1, erule ssubst)
apply (subgoal_tac "(zip (replicate (Suc (Suc 0) - length (0 # nat_to_bv (nat x div 2) @ 
                    [if nat x mod 2 = 0 then 0 else 1])) 0 @
              0 # nat_to_bv (nat x div 2) @ [if nat x mod 2 = 0 then 0 else 1])
          (replicate (Suc (length (nat_to_bv (nat x div 2) @ [if nat x mod 2 = 0 then 0 else 1])) - 
           length ([1] @ [1])) 0 @ [0] @ [1])) =
                    (zip (replicate (Suc (Suc 0) - length (0 # nat_to_bv (nat x div 2) @ 
                    [if nat x mod 2 = 0 then 0 else 1])) 0 @
              0 # nat_to_bv (nat x div 2))
          (replicate (Suc (length (nat_to_bv (nat x div 2) @ [if nat x mod 2 = 0 then 0 else 1])) -
           length ([0] @ [1])) 0 @ [0])) @
                    (zip [if nat x mod 2 = 0 then 0 else 1] [1])")
 prefer 2
 apply (subst zip_append[THEN sym])
   apply simp
  apply simp
 apply simp
apply (rotate_tac -1, erule ssubst)
apply simp
apply (subgoal_tac "map (\<lambda>(x, y). x AND y) (zip (1 # nat_to_bv (nat x div 2)) 
                    (replicate (length (nat_to_bv (nat x div 2))) 0 @ [0])) =
                    replicate (Suc (length (nat_to_bv (nat x div 2)))) 0")
 apply simp
apply (rule list_equality)
 prefer 2
 apply simp
apply (intro allI impI)
apply (subst nth_replicate)
 apply simp
apply (subst nth_map)
 apply simp
apply (subst nth_zip)
  apply simp
 apply simp
apply (subst nth_append)
apply simp
apply (case_tac "(0 # nat_to_bv (nat x div 2)) ! i")
 apply simp
apply simp
  ================== rev. 12634 ====================== *)
sorry

(* TODO REMOVE? (see proof) *)
lemma minus_mod_two: "- x mod 2 = x mod (2::int)"
by (simp add: zmod_zminus1_eq_if)

(* TODO MOVE *)

lemma mod_null_minus_mod_one: "x mod 2 = 0 \<Longrightarrow> (- x - 1) mod 2 = (1::int)"
apply (subgoal_tac "- x - 1 = (- x) + (- 1)")
 apply (rotate_tac, erule ssubst)
 apply (subst mod_add_eq [of "- x" "- 1" 2])
 apply simp
 apply (simp only: minus_mod_two)
 apply simp
apply simp
done

(* TODO MOVE *)

lemma mod_one_minus_mod_null: "x mod 2 = 1 \<Longrightarrow> (- x - 1)mod 2 = (0::int)"
apply (subgoal_tac "- x - 1 = (- x) + (- 1)")
 apply (rotate_tac)
 apply (erule ssubst)
 apply (subst mod_add_eq [of "- x" "- 1" 2])
 apply simp
 apply (simp only: minus_mod_two)
 apply simp
apply simp
done

(* TODO PROVE USING BITOPERATIONS *)

lemma int_and_1_neg: "x < 0 \<Longrightarrow> s_and x 1 = x mod 2"
apply (simp add: s_bitop_def)
apply (subst nat_to_bv_one[simplified])
apply (subst nat_to_bv_one[simplified])
apply simp
apply (case_tac "x = -1")
 apply simp
apply (subgoal_tac "x < -1")
 prefer 2
 apply simp
apply (subgoal_tac "norm_signed (1 # bv_not (nat_to_bv (nat (- x - 1)))) = 
                    1 # bv_not (nat_to_bv (nat (- x - 1)))")
 prefer 2
 apply (case_tac "nat_to_bv (nat (- x - 1))")
  apply simp
 apply simp
 apply (frule nat_to_bv_Cons_impl_head_is_One)
 apply simp
apply (rotate_tac -1, erule ssubst)
apply (subgoal_tac "map (\<lambda>(ua, u). ua AND u)
          (zip (bv_extend (Suc (Suc 0)) 1 (1 # bv_not (nat_to_bv (nat (- x - 1))))) 
          (bv_extend (length (1 # bv_not (nat_to_bv (nat (- x - 1))))) 0 [0, 1])) =
        (replicate (length (nat_to_bv (nat (- x - 1)))) 0) @ [last (bv_not (nat_to_bv (nat (- x - 1))))]")
 apply (rotate_tac -1, erule ssubst)
 apply (subgoal_tac "replicate (length (nat_to_bv (nat (- x - 1)))) 0 = 
                     0 # replicate (length (nat_to_bv (nat (- x - 1))) - 1) 0")
  apply (rotate_tac-1, erule ssubst)
(* ================== rev. 12634 ======================
  apply (simp add: bv_to_int_def)
  apply (subst bv_to_nat_replicate_Zero_append)
  apply (subst nat_to_bv_non0)
   apply simp
  apply (subst bv_not_append)
  apply (split if_split)
  apply simp
  apply (case_tac "x mod 2 = 0")
   apply simp
   apply (subst int_int_eq[THEN sym])
   apply (subst int_mod)
   apply simp
   apply (simp add: mod_null_minus_mod_one)
  apply simp
  apply (subgoal_tac "nat (- x - 1) mod 2 = 0")
   apply simp
  apply (subst int_int_eq[THEN sym])
  apply (subst int_mod)
  apply simp
  apply (simp add: mod_one_minus_mod_null)
 apply (case_tac "nat_to_bv (nat (- x - 1))")
  apply simp
  apply (drule nat_to_bv_is_Nil_impl_nat_is_0)
  apply simp_all
 apply arith
apply (subst nat_to_bv_non0[of "nat (- x - 1)"], simp)+
apply (simp only: bv_extend_def)
apply (subgoal_tac "[0, 1] = [0] @ [1]")
 prefer 2
 apply simp
apply (rotate_tac -1, erule ssubst)
apply (subst bv_not_append)+
apply (subgoal_tac "(zip (replicate (Suc (Suc 0) - 
          length (1 # bv_not (nat_to_bv (nat (- x - 1) div 2)) @ 
          bv_not [if nat (- x - 1) mod 2 = 0 then 0 else 1])) 1 @
           1 # bv_not (nat_to_bv (nat (- x - 1) div 2)) @ 
          bv_not [if nat (- x - 1) mod 2 = 0 then 0 else 1])
       (replicate (Suc (length (nat_to_bv (nat (- x - 1) div 2) @ 
        [if nat (- x - 1) mod 2 = 0 then 0 else 1])) - length ([0] @ [1])) 0 @ [0] @ [1])) =
       (zip (replicate (Suc (Suc 0) - length (1 # bv_not (nat_to_bv (nat (- x - 1) div 2)) @ 
       bv_not [if nat (- x - 1) mod 2 = 0 then 0 else 1])) 1 @
           1 # bv_not (nat_to_bv (nat (- x - 1) div 2)))
       (replicate (Suc (length (nat_to_bv (nat (- x - 1) div 2) @ [if nat (- x - 1) mod 2 = 0 then 0 else 1])) - 
        length ([0] @ [1])) 0 @ [0])) @
                    (zip (bv_not [if nat (- x - 1) mod 2 = 0 then 0 else 1]) [1])")
 prefer 2
 apply (subst zip_append[THEN sym])
   apply simp
  apply simp
 apply simp
apply (rotate_tac -1, erule ssubst)
apply simp
apply (subgoal_tac "map (case_prod op AND) (zip (1 # bv_not (nat_to_bv (nat (- x - 1) div 2))) 
                    (replicate (length (nat_to_bv (nat (- x - 1) div 2))) 0 @ [0])) =
                         replicate (Suc (length (nat_to_bv (nat (- x - 1) div 2)))) 0")
 apply simp
apply (rule list_equality)
 prefer 2
 apply simp
apply (intro allI impI)
apply (subst nth_replicate)
 apply simp
apply (subst nth_map)
 apply simp
apply (subst nth_zip)
  apply simp
 apply simp
apply (subst nth_append)
apply simp
apply (case_tac "(1 # bv_not (nat_to_bv (nat (- x - 1) div 2))) ! i")
 apply simp
apply simp
  ================== rev. 12634 ====================== *)
sorry

lemma int_and_1: "s_and x 1 = x mod 2" 
apply (case_tac "0 \<le> x")
 apply (erule int_and_1_pos)
apply (simp add: int_and_1_neg)
done

lemma int_and_minus1: "s_and (-1) i = i"
apply (simp add: s_bitop_def bv_extend_def)
apply (case_tac"int_to_bv i")
 apply simp  
 apply (case_tac "i = 0")
  apply (simp add: bv_msb_def)
  apply (simp add: bv_to_int_replicate_Zero map_split_bitand_replicate_Zero)
 apply (simp add: int_to_bv_not_zero_is_not_empty)
apply simp
apply (cut_tac xs = "(replicate (length list) 1 @ [1])" and ys = 
                     "(a # list)" in map_split_bitand_commute)
apply (simp add: bv_msb_def)
apply (cut_tac i = "(length (a # list))" and xs = "(a # list)" in map_split_bitand_replicate_One)
  apply simp
apply (cut_tac n = "(length list)" and x = "1" and m="1" in replicate_add)
apply (subgoal_tac "(replicate (length list) 1 @ [1]) = (replicate (length (a # list)) 1)")
  prefer 2
  apply clarsimp
  apply (simp add: replicate_append_same)
apply simp
apply (drule sym)
apply simp
sorry

definition sllog :: "[int, int] \<Rightarrow> int"
where
  "sllog i sh == let sa = (intwd_as_nat sh) mod 2^5
                 in s_lsh i wlen_bit sa"

definition srlog :: "[int, int] \<Rightarrow> int"
where
  "srlog i sh == let sa = (intwd_as_nat sh) mod 2^5
                 in s_rsh i wlen_bit sa"

definition srath :: "[int, int] \<Rightarrow> int"
where
  "srath i sh == let sa = (intwd_as_nat sh) mod 2^5
                 in i div 2^sa"

lemma asm_int_s_lsh: "asm_int b \<Longrightarrow> asm_int (b \<lless>\<^bsub>s/wlen_bit\<^esub> c mod 32)"
apply (simp add: wlen_bit_def s_lsh_def)
apply (simp add: int2bvn_def asm_int_def Let_def)
apply (subgoal_tac "wlen_bit - Suc 0 = length (drop (c mod 32 + (length (int_to_bv b) - 32)) (bv_extend 32 (bv_msb (int_to_bv b)) (int_to_bv b)) @
        replicate (c mod 32) 0) - 1")
 apply (erule ssubst)
 apply (rule conjI)
  apply (rule bv_to_int_lower_range)
 apply (rule bv_to_int_upper_range)
apply (simp add: wlen_bit_def)
apply (simp add: bv_extend_def)
done

lemma asm_int_s_rsh: "asm_int b \<Longrightarrow> asm_int (b \<ggreater>\<^bsub>s/wlen_bit\<^esub> c mod 32)"
apply (simp add: wlen_bit_def s_rsh_def)
apply (simp add: int2bvn_def asm_int_def Let_def)
apply (rule impI)
apply (subgoal_tac "bv_to_nat (take (32 - c mod 32) (drop (length (int_to_bv b) - 32) (bv_extend 32 (bv_msb (int_to_bv b)) (int_to_bv b)))) < 2 ^ (wlen_bit - Suc 0)") 
 apply (simp add: wlen_bit_def)
apply (rule bv_to_nat_less_power)
apply (subgoal_tac "length (int_to_bv b) \<le> 32")
 apply (simp add: wlen_bit_def bv_extend_def min_def)
 apply (intro impI conjI)
    apply arith
   apply arith
  apply arith
apply (simp add: length_bounded_int_to_bv wlen_bit_def)
done

lemma sllog_is_mult_sign:
      "\<lbrakk> asm_int x; asm_sa sa \<rbrakk> \<Longrightarrow> sllog x (int sa) = natwd_as_int (intwd_as_nat x * 2 ^ sa mod 2 ^ wlen_bit)"
apply (simp add: sllog_def)
apply (subgoal_tac "intwd_as_nat (int sa) mod 32 = sa")
 prefer 2
 apply (simp add: asm_sa_def intwd_as_nat_def wlen_bit_def)
apply (rotate_tac -1, erule ssubst)
apply (subst s_lsh_arith)
    apply (simp add: wlen_bit_def)
   apply (simp add: asm_int_def wlen_bit_def)
  apply (simp add: asm_int_def wlen_bit_def)
 apply (simp add: asm_sa_def)
apply (simp add: smod_def)
apply (intro conjI impI)
 apply (simp add: intwd_as_nat_def natwd_as_int_def asm_int_def wlen_bit_def)
 apply (intro conjI impI, simp_all)
    apply (subgoal_tac "nat (x + 4294967296) * 2 ^ sa mod 4294967296 < 2147483648")
     apply simp
    apply (thin_tac "2147483648 \<le> nat (x + 4294967296) * 2 ^ sa mod 4294967296")
    apply (rule int_less_impl_less)
    apply (simp add: int_mod)
    apply (simp add: distrib_right)
    apply (insert mod_add_eq)
   apply (simp add: int_mod)
   apply (simp add: distrib_right)
   apply (insert mod_add_eq)
  apply (subgoal_tac "nat x * 2 ^ sa mod 4294967296 < 2147483648")
   apply simp
  apply (thin_tac "2147483648 \<le> nat x * 2 ^ sa mod 4294967296")
  apply (rule int_less_impl_less)
  apply (simp add: int_mod)
 apply (simp add: int_mod)
apply (simp add: intwd_as_nat_def natwd_as_int_def asm_int_def wlen_bit_def)
apply (intro conjI impI, simp_all)
   apply (simp add: int_mod)
   apply (simp add: distrib_right)
   apply (insert mod_add_eq)
  apply (subgoal_tac "2147483648 \<le> nat (x + 4294967296) * 2 ^ sa mod 4294967296")
   apply simp
  apply (thin_tac "\<not> 2147483648 \<le> nat (x + 4294967296) * 2 ^ sa mod 4294967296")
  apply (rule int_le_impl_le)
  apply (simp add: int_mod)
  apply (simp add: distrib_right)
  apply (insert mod_add_eq)
 apply (simp add: int_mod)
apply (subgoal_tac "2147483648 \<le> nat x * 2 ^ sa mod 4294967296")
 apply simp
apply (thin_tac "\<not> 2147483648 \<le> nat x * 2 ^ sa mod 4294967296")
apply (rule int_le_impl_le)
apply (simp add: int_mod)
done

lemma sllog_is_mult_pos: 
      "\<lbrakk> 0 \<le> i;
         i * 2 ^ a < 2 ^ (wlen_bit - 1);
         asm_sa a \<rbrakk> \<Longrightarrow> sllog i (int a) = i * 2 ^ a"
apply (subgoal_tac "i < 2 ^ (wlen_bit - 1)")
 prefer 2
 apply (rule_tac j = "i * 2 ^ a" in i_le_less_trans)
  apply (erule i_le_mult)
  apply (rule one_le_power)
  apply simp
 apply assumption
apply (subst sllog_is_mult_sign)
  apply (simp add: asm_int_def)
 apply assumption
apply (subgoal_tac "intwd_as_nat i = nat i")
 prefer 2
 apply (simp add: intwd_as_nat_def)
apply (rotate_tac -1, erule ssubst)
apply (subgoal_tac "nat i * 2 ^ a < 2 ^ (wlen_bit - 1)")
 prefer 2
 apply (rule int_less_impl_less)
 apply (subst int_mult)
 apply (subst int_power)
 apply (subst int_power)
 apply simp
apply (subst mod_less)
 apply (erule less_le_trans)
 apply (simp add: wlen_bit_def)
apply (subgoal_tac "natwd_as_int (nat i * 2 ^ a) = int (nat i * 2 ^ a)")
 prefer 2
 apply (simp add: natwd_as_int_def)
apply (rotate_tac -1, erule ssubst)
apply (subst int_mult)
apply (subst int_power)
apply simp
done

lemma sllog_0: "asm_int x \<Longrightarrow> sllog x 0 = x"
  apply (simp add: sllog_def) 
  apply (simp add: intwd_as_nat_0 s_lsh_def)
  apply (cut_tac x = "x" and w = "wlen_bit" in bv_to_int_int2bvn)
    apply (simp only: asm_int_impl_length_int_to_bv)
  apply simp
done

subsection{*Shift Operations *}
text{* These lemmas are placed here because they use @{text intwd_as_nat} and @{text natwd_as_int} definitions and also the lemma @{text asm_int_impl_length_int_to_bv} *}

lemma s_rsh_asm_int_eq_div: "\<lbrakk>0 < a ; asm_int x\<rbrakk> \<Longrightarrow>   x \<ggreater>\<^bsub>s/wlen_bit\<^esub> a = (int (intwd_as_nat x)) div 2^a"
apply (case_tac "x = 0 ")
 apply simp
 apply (simp add: intwd_as_nat_def wlen_bit_def)
apply (frule asm_int_impl_length_int_to_bv)
apply (case_tac "x < 0")
 apply (simp add: s_rsh_neg_eq_div)
 apply (simp add: asm_int_def intwd_as_nat_def )
 apply clarsimp
 apply (simp add: wlen_bit_def)
 apply (simp add: add.commute)
apply (simp add: s_rsh_pos_eq_div)
apply (simp add: intwd_as_nat_def asm_int_def )
done

declare drop_not_eq_list_not_eq [simp]
lemma s_rsh_equ_bv_a_less_bv_length:" \<lbrakk>asm_int x ; 0 < a;x \<noteq> 0;a < (length (int_to_bv x)) \<rbrakk>\<Longrightarrow> x \<ggreater>\<^bsub>s/wlen_bit\<^esub> a = int (bv_to_nat ((replicate (wlen_bit - (length (int_to_bv x))) (hd (int_to_bv x))) @ (take ((length (int_to_bv x)) - a) (int_to_bv x))))"
apply (simp add: s_rsh_def)
apply (simp add: int2bvn_def)
apply (simp add:asm_int_impl_length_int_to_bv)
apply (simp add: bv_extend_def bv_msb_def)
apply (frule asm_int_impl_length_int_to_bv)
apply (subgoal_tac "(min (wlen_bit - a) (wlen_bit - (length (int_to_bv x)))) = 
                    (wlen_bit - (length (int_to_bv x))) ")
prefer 2
apply arith
apply simp 
done

declare drop_not_eq_list_not_eq [simp del]


lemma s_rsh_equ_bv_a_ge_bv_length:" \<lbrakk>asm_int x ; 0 < a;x \<noteq> 0; (length (int_to_bv x))\<le>a \<rbrakk>\<Longrightarrow> x \<ggreater>\<^bsub>s/wlen_bit\<^esub> a = (if x < 0 then 2^(wlen_bit - a) - 1  else  0)"
apply (case_tac "x < 0")
apply (frule int_to_bv_not_zero_is_not_empty)
apply (simp add: s_rsh_def del: int_to_bv_lt0)
apply (simp add: int2bvn_def del: int_to_bv_lt0)
apply (frule asm_int_impl_length_int_to_bv)
apply (simp add: bv_extend_def bv_msb_def del: int_to_bv_lt0)
apply (subgoal_tac "(min (wlen_bit - a) (wlen_bit - (length (int_to_bv x)))) = (wlen_bit - a) ")
prefer 2
apply arith
apply (simp add: int_to_bv_l_0 del: int_to_bv_lt0)
apply (simp add: bv_to_nat_replicate_One)
apply (subgoal_tac "(int (((2::nat) ^ (wlen_bit - a)) - (Suc (0::nat)))) = 
                   ((int ((2::nat) ^ (wlen_bit - a))) - (int (Suc (0::nat))))")
apply (simp add: int_power)
apply (subgoal_tac "(Suc 0) \<le>((2::nat) ^ (wlen_bit - a)) ")
apply (frule_tac m = "((2::nat) ^ (wlen_bit - a))" and n = "(Suc 0)" in of_nat_diff)
apply simp 
apply (simp add: one_le_power)
apply (frule int_to_bv_not_zero_is_not_empty)
apply (simp add: s_rsh_def del: int_to_bv_ge0)
apply (simp add: int2bvn_def del: int_to_bv_ge0)
apply (frule asm_int_impl_length_int_to_bv)
apply (simp add: bv_extend_def bv_msb_def del: int_to_bv_ge0)
apply (subgoal_tac "(min (wlen_bit - a) (wlen_bit - (length (int_to_bv x)))) = (wlen_bit - a) ")
prefer 2
apply arith
apply (simp add: int_to_bv_g_0 del: int_to_bv_ge0)
apply (simp add: bv_to_nat_replicate_Zero)
done

lemma intwd_as_nat_s_lsh_eq_nat_mod: "\<lbrakk>length (int_to_bv x) \<le>  wlen_bit; 0 < a ; asm_int x; a < wlen_bit\<rbrakk> \<Longrightarrow>(intwd_as_nat (x \<lless>\<^bsub>s/wlen_bit\<^esub>  a)) = (nat ((x * 2^a) mod 2^wlen_bit))"
apply (subgoal_tac " 0 < wlen_bit" )
 apply (frule_tac x = "x " and bw = "wlen_bit" and n = "a "  in s_lsh_arith)
    apply (simp add: asm_int_def )
   apply (simp add: asm_int_def )
  apply arith
 apply simp
 apply (simp add:  smod_def )
 apply (rule conjI impI)+
  apply (subgoal_tac "0\<le> ((x * ((2::int) ^ a)) mod ((2::int) ^ wlen_bit))" )
   prefer 2
   apply (simp add:pos_mod_sign wlen_bit_def)
  apply (simp add: asm_int_intwd_as_nat)
 apply clarsimp
 apply (subgoal_tac "(- ((2::int) ^ (wlen_bit - (1::nat)))) \<le> 
                     (((x * ((2::int) ^ a)) mod ((2::int) ^ wlen_bit)) - 
                     ((2::int) ^ wlen_bit)) \<and> (((x * ((2::int) ^ a)) mod 
                     ((2::int) ^ wlen_bit)) - ((2::int) ^ wlen_bit)) < 0")
  prefer 2
  apply (simp add: wlen_bit_def  pos_mod_conj)
 apply clarify
 apply (simp add: asm_int_intwd_as_nat_neg)
apply (simp add: wlen_bit_def)
done

lemma intwd_as_nat_s_lsh_eq_intwd_as_nat_u_lsh: "\<lbrakk> asm_int x; a < wlen_bit\<rbrakk> \<Longrightarrow>  ((intwd_as_nat x)\<lless>\<^bsub>u/wlen_bit\<^esub>  a ) = (intwd_as_nat (x \<lless>\<^bsub>s/wlen_bit\<^esub>  a))"
apply (subgoal_tac "length (int_to_bv x) \<le> wlen_bit")
 prefer 2
 apply (simp add: asm_int_impl_length_int_to_bv)
apply (subgoal_tac " (intwd_as_nat x) < ((2::nat) ^ wlen_bit) " )
apply (case_tac " a = 0" )
apply (simp add: s_lsh_def u_lsh_adef)
(*case 0 < a *)
apply simp
apply (frule_tac n = "(intwd_as_nat x) "  and k = "wlen_bit " in nat_upper_limit_impl_length_nat_to_bv_limit)
apply (simp add: u_lsh_adef)
apply (simp add: intwd_as_nat_s_lsh_eq_nat_mod)
apply (case_tac "0 \<le> x")
apply (simp add: asm_int_def asm_int_intwd_as_nat)
apply (subgoal_tac "(((nat x) * ((2::nat) ^ a)) mod ((2::nat) ^ wlen_bit))  = 
                    (nat (int (((nat x) * ((2::nat) ^ a)) mod ((2::nat) ^ wlen_bit)) ))" )
apply (erule ssubst)+
apply (simp only: int_mod)
apply (simp add: int_power int_mult)
apply simp
(*case x < 0*)
apply (simp add: asm_int_def asm_int_intwd_as_nat_neg)
apply clarsimp
apply (subgoal_tac "(((nat (x + ((2::int) ^ wlen_bit))) * 
                    ((2::nat) ^ a)) mod((2::nat) ^ wlen_bit)) = 
                    (nat (int (((nat (x + ((2::int) ^ wlen_bit))) * ((2::nat) ^ a)) mod
                    ((2::nat) ^ wlen_bit))))" )
prefer 2
apply simp 
apply (simp only:int_mod)
apply (simp add: int_power int_mult)
apply (subgoal_tac "((0::int) \<le> (x + ((2::int) ^ wlen_bit))) ")
apply simp
apply (simp add: distrib_right)
apply (simp add: wlen_bit_def)
apply (simp add: asm_int_def intwd_as_nat_def wlen_bit_def)
apply clarsimp
apply arith
done

lemma intwd_as_nat_s_rsh_eq_intwd_as_nat_u_rsh: 
     "\<lbrakk> asm_int x; a < wlen_bit\<rbrakk> \<Longrightarrow>  
      (intwd_as_nat x \<ggreater>\<^bsub>u/wlen_bit\<^esub> a ) = 
      (intwd_as_nat (x \<ggreater>\<^bsub>s/wlen_bit\<^esub> a))"
apply (case_tac "a=0")
 apply (simp add: s_rsh_def u_rsh_def)
apply clarsimp
apply (simp add: u_rsh_is_div_power2)
apply (subst s_rsh_asm_int_eq_div, simp+)
apply (subst asm_int_intwd_as_nat[where x="int (intwd_as_nat x) div 2 ^ a"])
  apply (subgoal_tac "0 < 2^a")
   apply (frule_tac b="2^a" and a="int (intwd_as_nat x)" in pos_imp_zdiv_nonneg_iff)
   apply simp
  apply (case_tac "2^a \<le> (0::int)")
   apply (simp add: power_le_zero_eq)
  apply simp
 apply (frule asm_nat_intwd_as_nat)
 apply (simp add: asm_nat_def)
 apply (subgoal_tac "(2::int)^ a = int ((2::nat)^ a)")
  apply simp
(* ================== rev. 12634 ======================
  apply (simp add: zdiv_int[symmetric])
  apply (subgoal_tac "int (intwd_as_nat x div 2 ^ a) < int (2^ (wlen_bit - Suc 0))")
   apply (simp add: int_pow2_eq_pow2)
   apply (metis int_div int_nat_two_exp)
  apply (simp add: of_nat_less_iff)
  apply (rule less_mult_impl_div_less)
   apply (simp add: power_add_2)
   apply (case_tac a, simp)
   apply simp
   apply (rule less_le_trans, simp)
   apply simp
  apply (simp add: zero_less_power)
 apply (simp add: int_pow2_eq_pow2)
apply (subgoal_tac "int (intwd_as_nat x) div 2 ^ a = int (intwd_as_nat x div 2 ^ a)")
 apply simp
apply (simp add: zdiv_int)
apply (simp add: int_pow2_eq_pow2)
   ================== rev. 12634 ====================== *)
sorry


lemma int_to_bv_neg_eq_nat_to_bv_two_complement: "\<lbrakk>x < 0; length (int_to_bv x) \<le> wlen_bit;asm_int x \<rbrakk> \<Longrightarrow> (sxt_wd (int_to_bv x))  =( nat_to_bv (nat(2^(wlen_bit) + x)))"
apply (frule_tac w ="wlen_bit" in  bv_to_nat_extend_int_to_bv_neg)
 apply simp
apply (subgoal_tac "nat (int (bv_to_nat (bv_extend wlen_bit 1 (int_to_bv x))))= 
                    nat (((2::int) ^ wlen_bit) + x)")
 apply (thin_tac "((int (bv_to_nat (bv_extend wlen_bit 1 (int_to_bv x)))) = 
                  (((2::int) ^ wlen_bit) + x))")
 apply (simp del:int_to_bv_lt0)
 apply (subgoal_tac "nat_to_bv (bv_to_nat (bv_extend wlen_bit 1 (int_to_bv x))) = 
                     nat_to_bv(nat (((2::int) ^ wlen_bit) + x))")
  prefer 2
  apply (simp )
 apply (thin_tac  "((bv_to_nat (bv_extend wlen_bit 1 (int_to_bv x))) = 
                   (nat (((2::int) ^ wlen_bit) + x)))")
 apply (simp only:  nat_bv_nat del: int_to_bv_lt0)
 apply (simp add: bv_extend_def del: int_to_bv_lt0)
 apply (simp add: sxt_wd_def del: int_to_bv_lt0)
 apply (subgoal_tac "(bv_msb (int_to_bv x)) = 1")
  apply (simp add: int_to_bv_l_0 del: int_to_bv_lt0)
  apply (case_tac  "((Suc (length (nat_to_bv (nat ((- x) - (1::int)))))) = wlen_bit)")
   apply simp
   apply (simp add: bv_extend_def)
   apply (simp add: asm_int_def)
   apply (subgoal_tac "2^(wlen_bit - 1) \<le>(nat (((2::int) ^ wlen_bit) + x)) ")
    prefer 2
    apply (simp add: wlen_bit_def)
    apply (metis le_eq_less_or_eq length_Cons length_map)
    apply (metis bv_extend_def diff_is_0_eq diffs0_imp_equal length_Cons length_map 
                 norm_unsigned_replicate_One rem_initial_append1 replicate_empty)
    using bv_msb_def int_to_bv_l_0 apply auto[1]
apply simp
done

lemma length_nat_to_bv_two_complement_wlen_bit: "\<lbrakk>asm_int x; x < 0\<rbrakk> \<Longrightarrow> length (nat_to_bv (nat (2^wlen_bit + x))) = wlen_bit"
apply (subgoal_tac "2^(wlen_bit - 1) \<le>(nat (2^wlen_bit + x)) \<and> (nat (2^wlen_bit + x) )< 2^wlen_bit")
 apply clarify
 apply (frule_tac k = "(wlen_bit - (1::nat))" and n = "(nat (((2::int) ^ wlen_bit) + x))" in length_nat_to_bv_upper_limit_impl_nat_limit_aux)
 apply (frule_tac n = "(nat (((2::int) ^ wlen_bit) + x))" and k = "wlen_bit" in nat_upper_limit_impl_length_nat_to_bv_limit)
 apply arith
apply (simp add: asm_int_def nat_less_iff wlen_bit_def)
done

lemma intwd_as_nat_smod_eq_mod_wlen_bit[rule_format]:"(intwd_as_nat(x smod wlen_bit )) mod (2^wlen_bit)= (intwd_as_nat(x smod wlen_bit ))"
apply (insert smod_less [of "x"  "wlen_bit" ])
apply (insert smod_ge [of "wlen_bit"  "x" ])
apply (subgoal_tac  "((intwd_as_nat (x smod wlen_bit)) < ((2::nat) ^ wlen_bit))" )
 apply (simp add: mod_less)
apply (simp add: intwd_as_nat_def wlen_bit_def)
apply (rule conjI impI)+
 apply simp
 apply arith
done

lemma intwd_as_nat_power2_neg[rule_format]: 
"n < wlen_bit \<longrightarrow> intwd_as_nat (- (2^n)) = 2^wlen_bit - 2^n"
apply clarsimp
apply (simp add: intwd_as_nat_def)
apply (simp add: wlen_bit_def)
apply auto
apply (smt pow2_greater_zero_int)

apply (subst nat_diff_distrib)
  apply simp
 apply (subgoal_tac "(2::int) ^ n \<le> 2^32")
  apply simp
 apply (simp only: power_increasing)
apply (simp add: nat_power_eq)
apply (smt zero_less_power)
done


lemma intwd_as_nat_upper_range_asm_int [rule_format] : "intwd_as_nat x < 2 ^ wlen_bit \<longrightarrow> asm_int x"
apply clarify
apply (simp add: asm_int_def intwd_as_nat_def wlen_bit_def)
apply (split if_split_asm)
 apply (simp add: wlen_bit_def)
 apply (simp add: nat_add_distrib int_pow2_eq_pow2)
apply (split if_split_asm)
 apply (simp add: wlen_bit_def)
apply (split if_split_asm)
 apply (simp add: wlen_bit_def) 
apply simp
apply (case_tac "2147483648 \<le> x")
 apply arith
apply simp
done

lemma less_intwd_as_nat_mono [rule_format] : "asm_int i 
\<longrightarrow> i \<ge> 0 
\<longrightarrow> i < n 
\<longrightarrow> intwd_as_nat i < nat n"
apply clarify 
apply (cut_tac x = "nat i" in intwd_as_nat_int_trivial)
  apply simp
apply simp
done

lemma s_and_intwd_as_nat_upper_bound [rule_format] : "a\<ge>0 \<longrightarrow> b < 2 ^ (wlen_bit - 1) \<longrightarrow> intwd_as_nat (s_and a (int b)) \<le> b"
apply clarsimp
apply (cut_tac x="nat a" and y="b" in s_and_int_upper_bound)
apply (cut_tac x="nat a" and y="b" in s_and_int_lower_bound)
apply (cut_tac i="s_and a (int b)" and n="int (Suc b)" in less_intwd_as_nat_mono)
   apply (simp add: int_nat_eq)
   apply (simp add: asm_int_def)
   apply (simp add: wlen_bit_def)
  apply simp+
done

(*new arithmetic definition sllog for intwd_as_nat*)
lemma sllog_is_mult_pos_nat: 
      "\<lbrakk> 0 \<le> i; asm_int i;
         intwd_as_nat i * 2 ^ a < 2 ^ wlen_bit;
         asm_sa a \<rbrakk> \<Longrightarrow> intwd_as_nat (sllog i (int a)) = intwd_as_nat i * 2 ^ a"
apply (subst sllog_is_mult_sign)
   apply assumption+
apply (simp add: natwd2intwd2natwd)
done

lemma srlog_is_div_sign:
      "\<lbrakk> asm_int x; asm_sa sa; 0 < sa \<rbrakk> \<Longrightarrow> srlog x (int sa) = (int (intwd_as_nat x)) div 2^sa"
  apply (simp add: srlog_def)
  apply (frule asm_int_impl_length_int_to_bv)
  apply (frule_tac a = "sa" in s_rsh_asm_int_eq_div)
    apply assumption+
  apply (simp add: asm_sa_def wlen_bit_def intwd_as_nat_def)
done

lemma srlog_is_div_sign1:
      "\<lbrakk> asm_int x; asm_sa sa; 0 < sa \<rbrakk> \<Longrightarrow> srlog x (int sa) = int ((intwd_as_nat x) div 2^sa)"
  apply (frule srlog_is_div_sign)
    apply simp+
  apply (simp add: int_div int_power)
done

lemma s_and_srlog_div_mod_eq : "asm_int ad_disk \<longrightarrow> asm_sa sa \<longrightarrow> 0 < sa \<longrightarrow> 0 \<le> ad_disk \<longrightarrow> 0 < z
        \<longrightarrow> s_and (srlog ad_disk (int sa)) (2^z - 1) = (ad_disk div 2^sa) mod 2^z"
apply clarsimp
apply (frule_tac sa="sa" in srlog_is_div_sign, simp+)
apply (subst asm_int_intwd_as_nat, simp)
 apply (simp add: asm_int_def)
apply simp
apply (rule mask_is_mod_nat, simp)
apply (rule i_div_ge_0, simp)
apply (simp add: pow2_greater_zero_int)
done

declare Let_def[simp del]

end
