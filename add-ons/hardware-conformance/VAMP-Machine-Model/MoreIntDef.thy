(**
 * Copyright (c) 2003-2006 Matthias Daum, Dirk Leinenbach, Elena Petrova,
 * Alexandra Tsyban.
 * Some rights reserved, Saarland University.
 *
 * This work is licensed under the German-Jurisdiction Creative Commons
 * Attribution Non-commercial Share Alike 2.0 License.
 * See the file LIZENZ for a full copy of the license.
**)
(* $Id: MoreIntDef.thy 29819 2009-11-24 14:41:51Z DirkLeinenbach $ *)
chapter {* Additional theory about integer numbers *}

theory MoreIntDef imports MoreDivides begin

subsection {* comparison *}

lemma i_less_trans: "\<lbrakk>(i::int) < j; j < k\<rbrakk> \<Longrightarrow> i < k"
  by (cases i, cases j, cases k, simp_all)

lemma i_le_less_trans: "\<lbrakk>i \<le> j; j < k\<rbrakk> \<Longrightarrow> i < (k::int)"
  by arith

lemma i_less_le_trans: "\<lbrakk>i < j; j \<le> k\<rbrakk> \<Longrightarrow> i < (k::int)"
  by arith

lemma i_le_trans: "i \<le> j \<longrightarrow> j \<le> k \<longrightarrow> i \<le> (k::int)"
  by arith

lemma of_nat_less_iff_impl[rule_format]: "int m < int n \<longrightarrow> m < n"
  by simp  

(* allows ML code generation for max with int arguments *)
lemma [code]:"max (z::int) y = (if z \<le> y then y else z)"
  by auto

subsection {* nat and int conversion *}

lemma nat_equality: "i1 = i2 \<Longrightarrow> nat i1 = nat i2"
  by simp

lemma int_less_impl_less: "int m < int n \<Longrightarrow> m < n"
  by simp

lemma int_le_impl_le: "int m \<le> int n \<Longrightarrow> m \<le> n"
  by simp

lemma int_mult: "int (m * n) = int m * int n"
  by auto

lemma int_pow2_eq_pow2: "int (2^i) = 2^i"
  by auto

lemma nat_pow2_eq_pow2: "nat (2^i) = 2^i"
by (simp add: nat_power_eq)

lemma pow2_greater_zero_nat: "0 < (2::nat)^i"
  by (auto)

lemma pow2_greater_zero_int [rule_format] : "(0::int) < 2 ^ n"
  apply (cut_tac i = "n" in pow2_greater_zero_nat)
  apply (cut_tac z = "2 ^ n" in zero_less_nat_eq)
  apply (simp only: nat_pow2_eq_pow2)
done

lemma less_int_impl_less_nat [rule_format]: 
  "0 < y \<longrightarrow>  x < y \<longrightarrow> (nat x < nat y )"
  by clarsimp

subsection {* Addition *}

lemma i_add_ge_0: "\<lbrakk>0 \<le> (a::int); 0 \<le> b\<rbrakk> \<Longrightarrow> 0 \<le> a + b"
  by simp

lemma i_le_neg_impl_add_ge_0: "- a \<le> b \<Longrightarrow> 0 \<le> b + (a::int)"
  by simp

lemma i_le_add1: "0 \<le> b \<Longrightarrow> a \<le> (a::int) + b"
  by simp

lemma i_le_add2: "0 \<le> b \<Longrightarrow> a \<le> b + (a::int)"
  by simp

subsection {* Multiplication *}

lemma i_mult_neg_neg_is_pos: "\<lbrakk>a < 0; b < 0\<rbrakk> \<Longrightarrow> 0 < a * (b::int)"
  using Rings.linordered_ring_strict_class.mult_neg_neg
  by auto

lemma i_mult_pos_neg_is_neg: "\<lbrakk>0 < a; b < 0\<rbrakk> \<Longrightarrow> a * b < (0::int)"
  using  Rings.linordered_semiring_strict_class.mult_pos_neg
  by auto

lemma i_mult_neg_pos_is_neg: "\<lbrakk>a < 0; 0 < b\<rbrakk> \<Longrightarrow> a * b < (0::int)"
apply (subgoal_tac "a * b = b * a")
 apply (erule ssubst)
 apply (erule i_mult_pos_neg_is_neg)
 apply assumption
apply simp
done

lemma i_mult_pos_pos_is_pos: "\<lbrakk>0 < a; 0 < b\<rbrakk> \<Longrightarrow> 0 < a * (b::int)"
  by (cases a, cases b, simp_all)

lemma i_mult_le_mono_int: "a \<le> b \<Longrightarrow> 0 \<le> c \<longrightarrow> int c * a \<le> int c * b"
  apply (induct_tac "c", simp)
  apply (simp add: of_nat_Suc)
done

lemma i_mult_less_mono_int: "a < b \<Longrightarrow> 0 <c \<longrightarrow> int c * a < int c * b"
  apply (induct_tac "c", simp)
  apply (simp add: of_nat_Suc)
done

lemma i_mult_le_mono: "\<lbrakk>a \<le> b; (0::int) \<le> c \<rbrakk> \<Longrightarrow> c * a \<le> c * b"
  apply (case_tac "0 < c")
   apply (frule order_less_imp_le [THEN zero_le_imp_eq_int])
   apply (auto simp add: i_mult_le_mono_int)
done

lemma i_mult_less_mono: "\<lbrakk>a < b; (0::int) < c \<rbrakk> \<Longrightarrow> c * a < c * b"
 apply (frule order_less_imp_le [THEN zero_le_imp_eq_int])
 apply (auto simp add: i_mult_less_mono_int)
done

lemma i_mult_pos_pos_ge_0: "\<lbrakk>0 \<le> (a::int); 0 \<le> b\<rbrakk> \<Longrightarrow> 0 \<le> a * b"
  using Nat_Transfer.transfer_nat_int_function_closures(2)
  by auto

lemma i_minus_first_is_minus_mult: "- a * b = - (a * (b::int))"
  apply (subgoal_tac "- a = 0 - a")
   apply (erule ssubst)
  apply simp
  apply simp
done

lemma i_is_odd_or_even: "\<exists> q. (x::int) = q * 2 \<or> x = q * 2 + 1"
apply (induct x)
 apply (subgoal_tac "\<exists> r. n = r * 2 \<or> n = r * 2 + 1")
  apply (erule exE)
  apply (rule_tac x = "int r" in exI)
  apply (erule disjE)
   apply (rule disjI1)
   apply (erule ssubst)
   apply (simp add: int_mult)
   apply simp
 apply (metis nat_is_odd_or_even)
apply (subgoal_tac "\<exists> r. Suc n = r * 2 \<or> Suc n = r * 2 + 1")
 apply (erule exE)
 apply (erule disjE)
  apply (rule_tac x= "- int r" in exI)
  apply (rule disjI1)
  apply (erule ssubst)
  apply (simp add: int_mult)
 apply (rule_tac x = "- int (r + 1)" in exI)
 apply (rule disjI2)
 apply (erule ssubst)
 apply (simp add: int_mult)
apply (rule nat_is_odd_or_even)
done

lemma i_decompose: "0 < b \<and> 0 \<le> a \<Longrightarrow> \<exists> q r. 0 \<le> q \<and> 0 \<le> r \<and> r < b \<and> (a::int) = q * b + r"
apply (induct a)
 apply (subgoal_tac "\<exists> q r. r < nat b \<and> n = q * nat b + r")
  apply (elim exE conjE)
  apply (rule_tac x = "int q" in exI)
  apply (rule_tac x = "int r" in exI)
  apply (rule conjI)
   apply simp
  apply (rule conjI)
   apply simp
  apply (rule conjI)
   apply (subgoal_tac "b = int (nat b)")
    apply (rotate_tac -1)
    apply (erule ssubst)
    apply (simp only: of_nat_less_iff)
   apply simp
  apply (erule ssubst)
  apply (simp add: int_mult)
 apply (rule nat_decompose)
 apply simp
apply simp
done

lemma i_mult_abs_is_abs_mult: "\<bar>(a::int)\<bar> * \<bar>b\<bar> = \<bar>a * b\<bar>"
apply (simp add: zabs_def)
apply (intro conjI impI)
   apply (drule i_mult_neg_neg_is_pos)
    apply assumption
   apply simp
  apply (case_tac "0 < b")
   apply (drule i_mult_neg_pos_is_neg)
    apply assumption
  apply simp
  apply simp
 apply (case_tac "0 < a")
  apply (drule i_mult_pos_neg_is_neg)
   apply assumption
  apply simp
 apply simp
apply (case_tac "0 < a")
 apply (case_tac "0 < b")
  apply (drule i_mult_pos_pos_is_pos)
   apply assumption
  apply simp
 apply (rule disjI2)
 apply simp
apply (rule disjI1)
apply simp
done

lemma i_le_mult: "\<lbrakk>0 \<le> a; (1::int) \<le> b\<rbrakk> \<Longrightarrow> (a \<le> a * b)"
by (frule_tac a="1" in i_mult_le_mono)simp+

lemma mult_less_mono_int [rule_format] : "0 \<le> a \<longrightarrow> a * c < b \<longrightarrow> c \<ge> (1::int) \<longrightarrow> a < b"
  apply clarify
  apply (frule_tac a = "a" and b = "c" in i_le_mult)
  apply simp+
done

end
