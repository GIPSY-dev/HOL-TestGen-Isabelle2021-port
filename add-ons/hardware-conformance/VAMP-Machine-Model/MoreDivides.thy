(**
 * Copyright (c) 2003-2009 Eyad Alkassar, Matthias Daum, Dirk Leinenbach,
 * Hristo Pentchev, Elena Petrova, Alexandra Tsyban.
 * Some rights reserved, Saarland University.
 *                                                                             
 * This work is licensed under the German-Jurisdiction Creative Commons
 * Attribution Non-commercial Share Alike 2.0 License.
 * See the file LIZENZ for a full copy of the license.
**)
(* $Id: MoreDivides.thy 28410 2009-06-15 18:21:43Z MatthiasDaum $ *)
chapter {* Additional theory about division for natural numbers *}

theory MoreDivides imports MoreNat begin

subsection {* \textbf{div} *}

lemma div_add_mult_self: "b \<noteq> 0 \<Longrightarrow> (a + b * k) div b = a div b + (k::nat)"
apply (subst div_add1_eq [of a "b * k" b])
apply simp
done

lemma le_div: "\<lbrakk>0 \<le> n; 0 < k; k \<le> b; x * b < n\<rbrakk> \<Longrightarrow> x \<le> n div (k::nat)"
apply (subgoal_tac "x * b \<le> n")
 apply (rule_tac j = "n div b" in le_trans)
  apply (subgoal_tac "x = x * b div b")
   apply (erule ssubst)
   apply (erule div_le_mono)
  apply simp
 apply (erule div_le_mono2)
 apply assumption
apply simp
done

lemma le_div2[rule_format]: "0 < k \<longrightarrow> (b::nat) * k \<le> n \<longrightarrow> b \<le> n div k"    
      -- "a special case of @{text le_div}"
apply clarsimp
apply (subgoal_tac "b = b * k div k")
 apply (erule ssubst)
 apply (erule div_le_mono)
apply simp
done

lemma mult_div_le: "0 < a \<Longrightarrow> a * (b div a) \<le> (b::nat)"
apply (subgoal_tac "b = b mod a + a * (b div a)")
 apply (subst ssubst)
 apply simp_all
using split_div_lemma 
apply auto
done

lemma div_less_mono[rule_format]: "(a::nat) div k < b div k \<longrightarrow> a < b"
apply clarsimp
apply (case_tac "b \<le> a")
 apply (frule_tac k="k" in div_le_mono)
 apply simp
apply simp
done

lemma less_mult_impl_div_less':
      "\<lbrakk> a < (b::nat) * c \<rbrakk>
          \<Longrightarrow> a div c < b"
  apply (subgoal_tac "c* (a div c) < c*b" )
   apply simp
  by (smt Divides.div_mult2_eq div_eq_0_iff div_mult_mult2 mult.commute not_less_zero)

(* TODO: just here for backward compatibility; replace by less_mult_impl_div_less' which has less preconditions *)
lemma less_mult_impl_div_less:
      "\<lbrakk> a < (b::nat) * c; 0 < c \<rbrakk>
          \<Longrightarrow> a div c < b"
  by (simp add: less_mult_impl_div_less')


subsection {* \textbf{mod/div} *}

lemma less_div: "\<lbrakk>0 \<le> n; 0 < k; k \<le> b; x * b < n; n mod k = 0\<rbrakk> \<Longrightarrow> x < n div (k::nat)"
apply (frule le_div, assumption+)
apply (case_tac "x = n div k")
 apply simp
 apply (subgoal_tac "n = k * (n div k) + n mod k")
  apply simp
  apply (case_tac "b = k")
   apply clarsimp
  apply (case_tac "k < b")
   apply clarsimp
  apply simp
 apply (rule sym)
 apply (rule mult_div_mod_eq)
apply simp
done

lemma nat_div_diff[rule_format]: 
   "(k :: nat) dvd m \<longrightarrow> k dvd n \<longrightarrow> m div k - n div k = (m - n) div k"
apply clarsimp
using dvd_diff
proof -
  assume a1: "k dvd m"
  assume a2: "k dvd n"
  obtain nn :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
    "\<forall>x0 x1. (\<exists>v2. x0 = x1 * v2) = (x0 = x1 * nn x0 x1)"
    by moura
  then have f3: "\<forall>n na. \<not> n dvd na \<or> na = n * nn na n"
    by (meson dvdE)
  then have f4: "m div k = k div k * nn m k"
    using a1 by (simp add: dvd_div_mult)
  have "n = k * nn n k"
    using f3 a2 by metis
  then show "m div k - n div k = (m - n) div k"
    using f4 f3 a1 by (metis (no_types) diff_mult_distrib2 dvd_div_mult dvd_refl)
qed

lemma mod_le: "(a::nat) mod b \<le> a"
apply (induct_tac a)
 apply simp
apply (simp add: mod_Suc)
done

lemma mod_add_left_eq: "(a+b) mod (c::nat) = ((a mod c) + b) mod c"
  using Divides.semiring_div_class.mod_add_left_eq
  by fast 

lemma mod_add_right_eq: "(a+b) mod (c::nat) = (a + (b mod c)) mod c"
by (rule mod_add_right_eq)

lemma mod_diff_cancel[rule_format]: 
  "(b::nat) \<le> a \<longrightarrow> (a - b) mod b = a mod b"
  apply clarsimp
  apply (insert mod_if[where m="a" and n="b"])
  apply simp
done

lemma div_diff_cancel[rule_format]: 
  "0 < b \<longrightarrow> (b::nat) \<le> a \<longrightarrow> (a - b) div b = a div b - Suc 0"
apply clarsimp
apply (insert div_if[where m="a" and n="b"])
apply simp
done

lemma div_diff_cancel2[rule_format]: 
  "0 < x \<longrightarrow> x * q \<le> a \<longrightarrow>  ((a::nat) - x * q) div x = a div x - q"
apply (induct_tac q)
 apply simp
apply clarsimp
apply (subgoal_tac "a - (x + x * n) = (a - x * n) - x")
 apply (simp only:)
 apply (subst div_diff_cancel, simp)
  apply simp
  apply arith
 apply simp
done

lemma div_mod: 
  "0 < x \<Longrightarrow> a div x mod y = a mod (x * y) div (x::nat)"
by (simp add: mod_mult2_eq div_add1_eq)

lemma mult_2_minus_1_div_2:" 0 < a\<Longrightarrow> ((2::nat)* a  - Suc 0 ) div 2 = a  - Suc 0"
 apply (induct a)
 apply simp+
done

lemma mod2_1:"\<lbrakk> x = (2::nat) * q ; 0 < q \<rbrakk> \<Longrightarrow>(x - 1) mod 2 = 1"
 apply (insert minus_div_mult_eq_mod [of "x - 1" "2"])
 apply auto
 apply (insert mult_2_minus_1_div_2 [of q])
 apply simp
done

lemma mod_le_mult : "(a::nat) mod n \<le> a mod (n * m)"
  by (simp add: mod_mult2_eq)

lemma diff_mod_left [rule_format]: 
  "x mod m \<ge> y \<longrightarrow>  x \<ge> y --> (x mod m - y) mod m = (x-y) mod (m::nat)"
  apply clarsimp
  apply (subgoal_tac "((int x) mod (int m) - (int y)) mod (int m) = ((int x)-(int y)) mod (int m)")
  apply (simp add: of_nat_diff zmod_int [symmetric])
  apply (metis Divides.transfer_int_nat_functions(2) of_nat_diff of_nat_eq_iff)
  apply (simp only: mod_diff_left_eq [symmetric])
done

subsection {* \textbf{dvd} *}

lemma div_is_zero_impl_dividend_is_zero: 
  "\<lbrakk>0 < k; d div k = 0; k dvd d\<rbrakk> \<Longrightarrow> d = (0::nat)"
apply (case_tac "d = 0")
 apply assumption
apply (subgoal_tac "d div k \<noteq> 0")
 apply simp
apply (thin_tac "d div k = 0")
apply (erule dvdE)
apply (subgoal_tac "k * (d div k) \<noteq> 0")
 apply simp
apply (subgoal_tac "k * (d div k) = k * (d div k) + d mod k")
 apply (rotate_tac -1)
 apply (erule ssubst)
 apply (simp (no_asm))
apply simp
done

lemma dvd_div_less_n[rule_format]: 
  "k dvd (b::nat) \<longrightarrow> 0 < k \<longrightarrow> a < b \<longrightarrow> a div k < b div k"
  apply clarsimp
  apply (rule_tac b = k in  less_div)
       apply simp_all
    apply (simp add: mult.commute)
    apply (rule_tac y = "a" in le_less_trans)
     apply (erule mult_div_le)
    apply assumption
done

lemma dvd_le_div[rule_format]: 
  "(k::nat) dvd a \<longrightarrow> k dvd b \<longrightarrow> a div k \<le> b div k \<longrightarrow> a \<le> b"
  apply clarsimp
  apply (erule dvdE, clarsimp)+
done

lemma dvd_le_div2[rule_format]: 
  "0 < (k::nat) \<longrightarrow> k dvd a \<longrightarrow> a div k \<le> b div k \<longrightarrow> a \<le> b"
  apply clarsimp
  apply (case_tac "b < a")
   prefer 2
   apply simp
  apply clarsimp
  apply (cut_tac a="b" and b="a" and k="k" in dvd_div_less_n, simp+)
done

lemma less_neg[rule_format]: "0 \<le> (a::int) \<longrightarrow> a < b \<longrightarrow> - b < a"
 by clarsimp


lemma nat_mod_ge_zero[rule_format]: "0 \<le> (a::nat) mod b"
  by auto


lemma int_mod_ge_zero[rule_format]: 
      "\<forall> a. 0 < (b::int) \<longrightarrow> 0 \<le> a mod b"
  by simp


lemma power_mod_zero[rule_format]: "0 < b \<longrightarrow> a^b mod a = (0::nat)"
  by clarsimp


lemma dvd_mult_self: "(k::nat) dvd k * x"
  by clarsimp

lemma dvd_mult_self2: "(k::nat) dvd x * k"
  by clarsimp

lemma dvd_div_add1[rule_format]: 
      "(x::nat) dvd b \<longrightarrow> (a + b) div x = a div x + b div x"
  apply clarsimp
  apply (subgoal_tac "b mod x = 0")
    apply (simp add: mod_eq_0_iff)
  apply (auto simp add: dvd_eq_mod_eq_0)
done

lemma dvd_div_add2[rule_format]: 
  "(x::nat) dvd a \<longrightarrow> (a + b) div x = a div x + b div x"
  apply clarsimp
  apply (frule_tac a="b" and b="a" in dvd_div_add1)
  apply (simp add: add.commute)
done

lemma dvd_div_diff1[rule_format]: 
  "0 < x \<longrightarrow> b \<le> (a::nat) \<longrightarrow> x dvd b \<longrightarrow> (a - b) div x = a div x - b div x"
apply clarsimp
apply (subgoal_tac "b mod x = 0")
 apply (simp add: mod_eq_0_iff)
 apply auto 
 using div_diff_cancel2 dvd_mult_div_cancel
 apply metis
done

lemma power2_minus1_mod_power2[rule_format]: 
  "0 < i \<longrightarrow> i \<le> n \<longrightarrow> (2^n - Suc 0) mod 2^i = 2^i - Suc 0"
apply (induct_tac n)
 apply simp
apply clarsimp
apply (subgoal_tac "2 * 2^n - Suc 0 = 2^n + (2^n - Suc 0)")
 apply clarsimp
 apply (subst diff_add_assoc, simp)
 apply (subst mod_add_eq)
 apply (case_tac "i = Suc n")
  apply clarsimp
  apply (subst mod_add_right_eq[symmetric])
  apply (case_tac n, simp)
  apply simp
 apply clarsimp
 apply (subgoal_tac "(2::nat) ^ n mod 2 ^ i = 0")
  apply clarsimp
 apply (subgoal_tac "i \<le> n")
  apply clarsimp
  apply (subgoal_tac "\<exists> j. n = i + j")
   apply clarsimp
   apply (subst power_add)
   apply simp_all
   apply (auto simp: le_iff_add)
 done


end
