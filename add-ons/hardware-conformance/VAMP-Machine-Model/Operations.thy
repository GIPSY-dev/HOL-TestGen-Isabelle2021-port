(**
 * Copyright (c) 2005-2006 Dirk Leinenbach, Hristo Pentchev.
 * Some rights reserved, Saarland University.
 *
 * This work is licensed under the German-Jurisdiction Creative Commons
 * Attribution Non-commercial Share Alike 2.0 License.
 * See the file LIZENZ for a full copy of the license.
**)
(* $Id: Operations.thy 22840 2008-03-26 17:32:49Z MarkHillebrand $ *)
theory Operations imports Exec begin
declare Let_def[simp]

(* TODO some of the lemmas below should be moved *)

lemma same_bits_same_range[rule_format]:"0 < length y \<longrightarrow> length y = l \<longrightarrow> 
     - ((2::int) ^ (l - (1::nat))) \<le> bv_to_int y \<and> bv_to_int y < (2::int) ^ (l - (1::nat)) "
 apply clarify
 apply (insert bv_to_int_lower_range[of y])
 apply (insert bv_to_int_upper_range[of y])
 apply clarsimp
done

lemma less_bits_same_range2[rule_format]:
      " 0 < length y \<longrightarrow> length y < l \<longrightarrow> 
     - ((2::int) ^ (l - (1::nat))) < bv_to_int y "
  apply clarify
  apply (insert bv_to_int_lower_range[of y])
  apply (subgoal_tac " - ((2::int) ^ (l - (1::nat))) <  - ((2::int) ^ (length y - (1::nat)))")
  apply (simp only: less_trans)
  apply auto
  apply (subgoal_tac "length y = Suc (length y - Suc (0::nat))")
  apply (subgoal_tac "l = Suc (l - Suc (0::nat))")
  apply (subgoal_tac "Suc (length y - Suc (0::nat)) < Suc (l - Suc (0::nat))")
  apply (simp only: Suc_less_eq )
  apply simp+
done

lemma less_bits_same_range1[rule_format]:
    " 0 < length y \<longrightarrow> length y < l \<longrightarrow> 
     bv_to_int y < (2::int) ^ (l - (1::nat))"
  apply clarify
  apply (insert bv_to_int_upper_range[of y])
  apply (subgoal_tac "(2::int) ^ (length y - (1::nat)) < (2::int) ^ (l - (1::nat))")
  (*apply (simp only: less_trans)*)
  apply auto
  apply (subgoal_tac "length y = Suc (length y - Suc (0::nat))")
  apply (subgoal_tac "l = Suc (l - Suc (0::nat))")
  apply (subgoal_tac "Suc (length y - Suc (0::nat)) < Suc (l - Suc (0::nat))")
  apply (simp only: Suc_less_eq )
  apply auto
  apply (metis (mono_tags) Nat_Transfer.transfer_int_nat_functions(4) 
               Suc_1 Suc_le_lessD i_less_trans of_nat_numeral le_less_linear 
               less_imp_of_nat_less order_less_irrefl power_strict_increasing_iff)
 apply(simp add: diff_less_mono leI)
done

lemma bv_to_int_upper_range_le[rule_format]: 
     "0 < length y \<longrightarrow> length y \<le> l \<longrightarrow>  - (2 ^ (l - 1)) \<le> bv_to_int y \<and> 
      bv_to_int y < 2 ^ (l - 1)"
  apply (rule impI)+
  apply (case_tac "length y = l")
  apply (simp only: same_bits_same_range, simp)
  apply (case_tac "length y < l")
  apply (rule conjI)
  using less_bits_same_range2 
  apply fastforce
  using less_bits_same_range1 
  apply auto
done

lemma u_bitop_s_bitop_eq[rule_format]:" asm_int x 
   \<longrightarrow> asm_int y 
   \<longrightarrow> f 0 0 = 0
\<longrightarrow> u_bitop f (intwd_as_nat x) ( intwd_as_nat y) = intwd_as_nat (s_bitop f x y)"
apply clarsimp
apply (frule_tac f="f" and a="x" and b="y" in asm_int_s_bitop, simp)
apply (simp add: intwd_as_nat_meaning)
apply (subst u_bitop_fixed_def[where w="wlen_bit"]) 
   apply (simp add: bv_nat_bv)
   apply (rule_tac j="length (sxt_wd (int_to_bv x))" in le_trans)
    apply (simp add: length_norm_unsigned_le)
   apply (simp add: length_sxt_wd2)
   apply (simp add: asm_int_impl_length_int_to_bv)
  apply (simp add: bv_nat_bv)
  apply (rule_tac j="length (sxt_wd (int_to_bv y))" in le_trans)
   apply (simp add: length_norm_unsigned_le)
  apply (simp add: length_sxt_wd2)
  apply (simp add: asm_int_impl_length_int_to_bv)
 apply simp
apply (subst s_bitop_fixed_def[where w="wlen_bit"]) 
   apply (simp add: asm_int_impl_length_int_to_bv)
  apply (simp add: asm_int_impl_length_int_to_bv)
 apply simp
apply (simp add: s_bitop_def u_bitop_def)
apply (subst sxt_wd_norm_signed2)
 apply clarsimp
 apply (simp add: length_bv_extend)
 apply (frule_tac i="x" in asm_int_impl_length_int_to_bv)
 apply (frule_tac i="y" in asm_int_impl_length_int_to_bv)
 apply (simp add: max_def min_def)
apply (subst bv_extend_zero_norm_unsigned_sxt_wd)
 apply (simp add: asm_int_impl_length_int_to_bv)
apply (subst bv_extend_zero_norm_unsigned_sxt_wd)
 apply (simp add: asm_int_impl_length_int_to_bv)
apply (subst length_wlen_bit_sxt_wd)
 apply clarsimp
 apply (simp add: length_bv_extend)
 apply (frule_tac i="x" in asm_int_impl_length_int_to_bv)
 apply (frule_tac i="y" in asm_int_impl_length_int_to_bv)
 apply (simp add: max_def min_def)
apply simp
done

lemma u_and_s_and_eq[rule_format]:" asm_int x 
   \<longrightarrow> asm_int y 
\<longrightarrow> (intwd_as_nat x \<and>\<^sub>u intwd_as_nat y) = intwd_as_nat (x \<and>\<^sub>s y)"
apply clarsimp
apply (simp add: u_bitop_s_bitop_eq)
done

lemma int_add_zero_pos [rule_format]:"  0\<le> i \<longrightarrow> i<2^31  \<longrightarrow>int_add 0 i = i"
apply clarify
apply (simp add: int_add_def)
apply (simp add: intwd_as_nat_def  wlen_bit_def) 
apply (simp add: fit_nat_def wlen_bit_def)
apply (subgoal_tac "nat i < 2^(wlen_bit - 1)")
apply (simp add: wlen_bit_def)
apply (simp add: natwd_as_int_def wlen_bit_def)
apply (simp add: wlen_bit_def)
done

lemma int_add_zero_neg [rule_format]:"  - (2^31) \<le> i \<longrightarrow>  i < 0  \<longrightarrow> int_add 0 i = i"
apply clarsimp
apply (simp add: int_add_def)

apply (simp add: intwd_as_nat_def  wlen_bit_def) 
apply (simp add: fit_nat_def wlen_bit_def)
apply (subgoal_tac "nat (i + 4294967296) mod 4294967296 = nat (i + 4294967296)")
 apply clarsimp
 apply (subgoal_tac "nat i mod 4294967296 < 2^(wlen_bit - 1)")
  apply (simp add: natwd_as_int_def)
  apply (simp add: wlen_bit_def)
  apply arith
 apply (simp add: wlen_bit_def)
apply (subgoal_tac "nat (i + 4294967296) < 4294967296")
 apply simp
apply arith
done

lemma int_add_zero [rule_format]: "asm_int i \<longrightarrow> int_add 0 i = i"
apply clarsimp
apply (simp add: asm_int_def)
apply clarsimp
apply (simp add: wlen_bit_def)
apply (case_tac "0 \<le> i")
 apply (simp add: int_add_zero_pos)
apply (simp add: int_add_zero_neg)
done

lemma bv_xor_zero[rule_format]:
      "x = length a \<longrightarrow> (map (case_prod op XOR) (zip (replicate x (0::bit)) a)) = 
       a \<and> (map (case_prod op XOR) (zip a (replicate x 0))) = a"
    apply clarify
    apply (induct_tac a)
    apply simp+
done


lemma bv_xor_one1[rule_format]:"(map (\<lambda>y. y XOR 1::bit) b) = bv_not b"
   apply (induct_tac b)
   apply simp+

done

lemma bv_xor_one[rule_format]:
     "x = length a \<longrightarrow> (map (case_prod op XOR) (zip a (replicate x (1::bit)))) = 
      bv_not  a"
   apply clarify
   apply (induct_tac a)
   apply simp+
done

lemma bv_xor_append[rule_format]: 
      "length a = length c \<longrightarrow> length d = length b \<longrightarrow> 
       (map (case_prod op XOR) (zip (a@b) (c@d))) = 
       (map (case_prod op XOR) (zip a c)) @ (map (case_prod op XOR) (zip b d)) "
  apply clarify
  apply simp
done

lemma bit_xor_same: 
      "map (case_prod op XOR) (zip xs xs) = 
       replicate (length xs) (0::bit)"
by (induct xs) simp_all

(* TODO move *)

lemma int_xor_same: "s_xor x x = 0"
  apply (simp add: s_bitop_def)
  apply (cases "x = 0")
  apply (simp)
  apply (metis bit_xor_same bv_to_int_Nil bv_to_int_type norm_signed_replicate_Zero)
  apply (subgoal_tac "int_to_bv x \<noteq> []")
      prefer 2
      apply (erule int_to_bv_not_zero_is_not_empty)
  apply (subgoal_tac "map (case_prod op XOR) (zip (int_to_bv x) (int_to_bv x)) = 
                      replicate (length (int_to_bv x)) 0")
      prefer 2
      apply (rule bit_xor_same)
  apply (rotate_tac -1)
  apply (erule ssubst)
  apply (subgoal_tac "bv_msb(replicate (length (int_to_bv x)) 0) = 0")
      prefer 2
      apply (simp add: bv_msb_def)
  using bit_xor_same bv_to_int_def bv_to_int_replicate_Zero 
  apply presburger
done
(* TODO move *)

lemma int_xor_zero_same: 
      "s_xor (0::int) x = x"
unfolding s_bitop_def bv_extend_def
proof (simp)
  have f1: "nat_to_bv 0 = []"
    by (meson less_numeral_extra(3) nat_to_bv_non_Nil)
  have f2: "\<forall>bs. bv_to_int bs \<noteq> 0 \<or> bs = replicate (length bs) 0"
    by (meson bv_to_int_is_zero_impl_replicate_zeros)
  have "bv_to_int (bv_msb (0 # nat_to_bv 0) # 0 # nat_to_bv 0) = 0"
    by (simp add: bv_to_int_Cons_bv_msb)
  then have "0 = bv_msb (0 # nat_to_bv 0)"
    using f2 by force
  then show "bv_to_int (map (\<lambda>(x, y). x XOR y) (zip (replicate (length (int_to_bv x) - 
             length (norm_signed (0 # nat_to_bv 0))) (bv_msb (0 # nat_to_bv 0)) @ 
             norm_signed (0 # nat_to_bv 0)) (replicate (length (norm_signed (0 # nat_to_bv 0)) -
              length (int_to_bv x)) (bv_msb (int_to_bv x)) @ int_to_bv x))) = x"
    using f1 by (simp add: bv_xor_zero)
qed

(* TODO move *)

lemma int_xor_same_zero: "s_xor x (0::int) = x"
  apply (simp add: s_bitop_def)
  apply (simp add: bv_extend_def bv_msb_def)
  apply (simp add: bv_xor_zero)
  apply (metis bv_int_bv bv_to_int_Nil bv_xor_zero empty_replicate list.size(3) 
         minus_eq nat_to_bv_non_Nil norm_signed0 replicate_not_empty self_append_conv 
         self_append_conv2)
done

lemma msb1_bv_to_int [rule_format]:
      "l = (1::bit) # ls \<longrightarrow> bv_to_int l < (0::int)"
 by clarsimp

lemma bv_msb_hd[rule_format]:"l \<noteq> [] \<longrightarrow> bv_msb l = hd l"
  apply (induct l)
  apply simp+
 apply (simp add: bv_msb_def)
done

lemma msb0_bv_to_int [rule_format]:"l = (0::bit) # ls \<longrightarrow> 0 \<le> bv_to_int l"
  by clarsimp

lemma int_xor_dif_sign[rule_format]: 
      "length (int_to_bv a) \<le> 32 \<longrightarrow> length (int_to_bv b) \<le> 32 \<longrightarrow> 
       0 \<le> a \<and> b < 0 \<or> a < 0 \<and> 0 \<le> b \<longrightarrow> s_xor a b < 0"
apply clarify
apply (erule disjE)
apply (case_tac "a = 0")
apply (simp add: int_xor_zero_same)
apply (elim conjE)
apply (frule_tac x="a" and y = "b" and f = "op XOR" in s_bitop_fixed_def)
apply (assumption, simp)
apply (simp only: Let_def)
apply (subgoal_tac "bv_msb (bv_extend (32::nat) (bv_msb (int_to_bv a)) (int_to_bv a)) = 0")
    prefer 2
    apply simp
    apply (simp add: bv_to_int_msb0)
apply (subgoal_tac "bv_msb (bv_extend (32::nat) (bv_msb (int_to_bv b)) (int_to_bv b)) = 1")
    prefer 2
    apply simp
apply (subgoal_tac "(bv_extend (32::nat) (bv_msb (int_to_bv a)) (int_to_bv a)) \<noteq> []")
    prefer 2
      apply (subgoal_tac " 0 < length (bv_extend (32::nat) (bv_msb (int_to_bv a)) 
                                                 (int_to_bv a))")
    apply (simp only: length_greater_0_conv)
    apply simp
      apply simp
      apply (simp add: bv_extend_Nil)
     apply (simp add: bv_to_int_msb1)
apply (subgoal_tac "(bv_extend (32::nat) (bv_msb (int_to_bv b)) (int_to_bv b)) \<noteq> []")
    prefer 2
      apply (subgoal_tac " 0 < length (bv_extend (32::nat) (bv_msb (int_to_bv b)) 
                                                 (int_to_bv b))")
    apply (simp only: length_greater_0_conv)
    apply simp
      apply simp
    apply (simp add: bv_extend_Nil)
apply (subgoal_tac "(bv_extend (32::nat) (bv_msb (int_to_bv b)) (int_to_bv b)) =
                     hd (bv_extend (32::nat) (bv_msb (int_to_bv b)) (int_to_bv b))# tl 
                     (bv_extend (32::nat) (bv_msb (int_to_bv b)) (int_to_bv b))")
    prefer 2
    apply (simp add: hd_Cons_tl)
apply ((subgoal_tac "(bv_extend (32::nat) (bv_msb (int_to_bv a)) (int_to_bv a)) = 
                     hd (bv_extend (32::nat) (bv_msb (int_to_bv a)) (int_to_bv a))# tl 
                     (bv_extend (32::nat) (bv_msb (int_to_bv a)) (int_to_bv a))"))
    prefer 2
    apply (simp add: hd_Cons_tl)
    apply (simp add: bv_extend_Nil)
apply (rotate_tac -1, erule ssubst)
apply (rotate_tac -1)
apply (erule ssubst)
apply (subgoal_tac "(zip (hd (bv_extend (32::nat) (bv_msb (int_to_bv a)) (int_to_bv a)) # tl 
                             (bv_extend (32::nat) (bv_msb (int_to_bv a)) (int_to_bv a)))
                         (hd (bv_extend (32::nat) (bv_msb (int_to_bv b)) (int_to_bv b)) # tl 
                             (bv_extend (32::nat) (bv_msb (int_to_bv b)) (int_to_bv b)))) = 
                          (hd (bv_extend (32::nat) (bv_msb (int_to_bv a)) (int_to_bv a)), 
                         hd (bv_extend (32::nat) (bv_msb (int_to_bv b)) (int_to_bv b))) 
# (zip (tl (bv_extend (32::nat) (bv_msb (int_to_bv a)) (int_to_bv a))) (tl (bv_extend (32::nat) (bv_msb (int_to_bv b)) (int_to_bv b))))")
prefer 2
apply (simp only: zip_Cons_Cons)
apply (simp (no_asm_simp)del: bv_to_int_def )
apply (subgoal_tac "bv_msb (bv_extend (32::nat) (bv_msb (int_to_bv a)) (int_to_bv a)) = 
                           hd (bv_extend (32::nat) (bv_msb (int_to_bv a)) (int_to_bv a))")
    prefer 2 
    apply (simp add: bv_extend_Nil bv_msb_hd)
    apply (smt bitNOT_bit.simps(1) bitXOR_bit.simps(1) bv_msb_bv_extend_bv_msb bv_msb_hd bv_to_int_msb0 int_to_bv_ge0 int_to_bv_l_0 list.distinct(1) list.sel(1) list.simps(3) list.simps(9) norm_signed_One_bv_not_nat_to_bv zero_neq_one)

(*disje*)
apply (case_tac "b = 0")
apply (simp add: int_xor_same_zero) 
apply (elim conjE)
apply (frule_tac x="a" and y = "b" and f = "op XOR" in s_bitop_fixed_def)
apply (assumption, simp)
apply (simp only: Let_def)
apply (subgoal_tac "bv_msb (bv_extend (32::nat) (bv_msb (int_to_bv a)) (int_to_bv a)) = 1")
    prefer 2
    apply simp
    using bv_msb_def apply auto[1]
apply (subgoal_tac "bv_msb (bv_extend (32::nat) (bv_msb (int_to_bv b)) (int_to_bv b)) = 0")
    prefer 2
    apply simp
    using bv_msb_def apply auto[1]
apply (subgoal_tac "(bv_extend (32::nat) (bv_msb (int_to_bv a)) (int_to_bv a)) \<noteq> []")
    prefer 2
      apply (subgoal_tac " 0 < length (bv_extend (32::nat) (bv_msb (int_to_bv a)) (int_to_bv a))")
    apply (simp only: length_greater_0_conv)
    apply simp
      apply simp
      apply (simp add: bv_extend_Nil)
apply (subgoal_tac "(bv_extend (32::nat) (bv_msb (int_to_bv b)) (int_to_bv b)) \<noteq> []")
    prefer 2
      apply (subgoal_tac "0 < length (bv_extend (32::nat) (bv_msb (int_to_bv b)) 
                           (int_to_bv b))")
    apply (simp only: length_greater_0_conv)
    apply simp
      apply simp
      using bv_extend_Nil apply auto[1]
apply ((subgoal_tac "(bv_extend (32::nat) (bv_msb (int_to_bv b)) (int_to_bv b)) = 
                      hd (bv_extend (32::nat) (bv_msb (int_to_bv b)) 
                         (int_to_bv b))# tl (bv_extend (32::nat) (bv_msb (int_to_bv b)) 
                         (int_to_bv b))"))
    prefer 2
    apply (simp add: hd_Cons_tl)
apply ((subgoal_tac "(bv_extend (32::nat) (bv_msb (int_to_bv a)) (int_to_bv a)) = 
                      hd (bv_extend (32::nat) (bv_msb (int_to_bv a)) (int_to_bv a))# 
                      tl (bv_extend (32::nat) (bv_msb (int_to_bv a)) (int_to_bv a))"))
    prefer 2
    apply (simp add: hd_Cons_tl)
apply (rotate_tac -1, erule ssubst)
apply (rotate_tac -1, erule ssubst)
apply (subgoal_tac "(zip (hd (bv_extend (32::nat) (bv_msb (int_to_bv a)) (int_to_bv a)) # 
                          tl (bv_extend (32::nat) (bv_msb (int_to_bv a)) (int_to_bv a)))
                         (hd (bv_extend (32::nat) (bv_msb (int_to_bv b)) (int_to_bv b)) # 
                          tl (bv_extend (32::nat) (bv_msb (int_to_bv b)) (int_to_bv b)))) = 
                          (hd (bv_extend (32::nat) (bv_msb (int_to_bv a)) (int_to_bv a)), 
                         hd (bv_extend (32::nat) (bv_msb (int_to_bv b)) (int_to_bv b)))# 
                    (zip (tl (bv_extend (32::nat) (bv_msb (int_to_bv a)) (int_to_bv a))) 
                         (tl (bv_extend (32::nat) (bv_msb (int_to_bv b)) (int_to_bv b))))")
prefer 2
apply (simp only: zip_Cons_Cons)
apply (simp (no_asm_simp)del: bv_to_int_def )
apply (subgoal_tac "bv_msb (bv_extend (32::nat) (bv_msb (int_to_bv a)) (int_to_bv a)) = 
                    hd (bv_extend (32::nat) (bv_msb (int_to_bv a)) (int_to_bv a))")

    prefer 2 
    apply (frule bv_msb_hd)
    using bv_msb_hd 
    apply blast
apply (subgoal_tac "bv_msb (bv_extend (32::nat) (bv_msb (int_to_bv b)) (int_to_bv b)) = 
                    hd (bv_extend (32::nat) (bv_msb (int_to_bv b)) (int_to_bv b))")
    prefer 2 
  
    apply (frule_tac l = "bv_extend (32::nat) (bv_msb (int_to_bv b)) (int_to_bv b)" in 
           bv_msb_hd)
    apply assumption
apply (subgoal_tac "hd (bv_extend (32::nat) 0 (norm_signed (0 # nat_to_bv (nat b)))) = 
                    hd (bv_extend (32::nat) (bv_msb (int_to_bv b)) (int_to_bv b))")
    prefer 2
    apply simp
apply (subgoal_tac "hd (bv_extend (32::nat) 1 (norm_signed (1 # bv_not (nat_to_bv 
                    (nat (- a - (1::int))))))) = 
                   hd (bv_extend (32::nat) (bv_msb (int_to_bv a)) (int_to_bv a))")
    prefer 2
    apply (simp (no_asm_simp))
    using bv_msb_def apply force

apply (rotate_tac -1, erule ssubst)
apply (rotate_tac -1, erule ssubst)
apply (rotate_tac -1, erule subst)
apply (rotate_tac -1, erule subst)
apply (rotate_tac 6, erule ssubst, erule ssubst)
apply (subgoal_tac "(1 XOR (0::bit)) = 1")
prefer 2
apply simp
apply (rotate_tac -1, erule ssubst)
(*apply (simp (no_asm_simp)only: msb1_bv_to_int)*)
apply (smt bitNOT_bit.simps(1) bit_extra_simps(6) bv_msb_def bv_msb_norm_signed bv_to_int_msb0 hd_Cons_tl int_to_bv_g_0 int_to_bv_l_0 int_to_bv_returntype list.collapse list.distinct(1) list.sel(1) list.simps(9) norm_signed_One_bv_not_nat_to_bv norm_signed_bv_extend_bv_msb zero_neq_one)
done
thm int_xor_dif_sign
lemma int_xor_same_sign[rule_format]: 
   "length (int_to_bv a) \<le> 32 \<longrightarrow> length (int_to_bv b) \<le> 32 \<longrightarrow> 
    (0::int) \<le> a \<and> (0::int) \<le> b \<or> a < (0::int) \<and> b < (0::int) \<longrightarrow> (0::int) \<le> s_xor a b"
  apply clarify
  apply (erule disjE)
  apply (case_tac "a = 0")
  apply (simp add: int_xor_zero_same)
  apply (elim conjE)
  apply (frule_tac x="a" and y = "b" and f = "op XOR" in s_bitop_fixed_def)
  apply (assumption, simp)
  apply (simp only: Let_def)
(*************************************************************************************************
  apply clarify
  apply (erule disjE)
  apply (case_tac "a = 0")
  apply (case_tac "b = 0")
  apply (simp add: int_xor_zero_same)
  apply (simp add: int_xor_zero_same)
  apply (case_tac "b = 0")
  apply (simp add: int_xor_same_zero)
  apply (elim conjE)
  apply (frule_tac x="a" and y = "b" and f = "op XOR" in s_bitop_fixed_def)
     apply (assumption, simp)
     apply (simp only: Let_def)*)
  apply (subgoal_tac "bv_msb (bv_extend (32::nat) (bv_msb (int_to_bv a)) (int_to_bv a)) = (0::bit)")
      prefer 2
      apply simp
      apply (simp add: bv_msb_def)
  apply (subgoal_tac "bv_msb (bv_extend (32::nat) (bv_msb (int_to_bv b)) (int_to_bv b)) = (0::bit)")
      prefer 2
      apply simp
      apply (simp add: bv_msb_def)
  apply (subgoal_tac "(bv_extend (32::nat) (bv_msb (int_to_bv a)) (int_to_bv a)) \<noteq> []")
      prefer 2
      apply (subgoal_tac " 0 < length (bv_extend (32::nat) (bv_msb (int_to_bv a)) (int_to_bv a))")
      apply (simp only: length_greater_0_conv)
      apply simp
          apply simp
          apply (simp add: bv_extend_Nil)
          apply (smt Nil_is_map_conv bit_xor_same bv2int_inj bv_extend_Nil bv_msb_hd bv_to_int_Nil bv_to_int_Nil bv_to_int_is_zero_impl_replicate_zeros bv_to_int_msb1 bv_to_int_type bv_to_int_zero_zero hd_map head_zip list.map_sel(1) list.sel(1) list.simps(3) norm_signed0 zero_neq_numeral zero_neq_one zip_is_not_empty)
apply (subgoal_tac "(bv_extend (32::nat) (bv_msb (int_to_bv b)) (int_to_bv b)) \<noteq>  []")
    prefer 2
      apply (subgoal_tac " 0 < length (bv_extend (32::nat) (bv_msb (int_to_bv b)) (int_to_bv b))")
    apply (simp only: length_greater_0_conv)
    apply simp
      apply simp
      apply (simp add: bv_extend_Nil)
apply ((subgoal_tac "(bv_extend (32::nat) (bv_msb (int_to_bv b)) (int_to_bv b)) = hd (bv_extend (32::nat) (bv_msb (int_to_bv b)) (int_to_bv b))# tl (bv_extend (32::nat) (bv_msb (int_to_bv b)) (int_to_bv b))"))
    prefer 2
    apply simp 
apply ((subgoal_tac "(bv_extend (32::nat) (bv_msb (int_to_bv a)) (int_to_bv a)) = hd (bv_extend (32::nat) (bv_msb (int_to_bv a)) (int_to_bv a))# tl (bv_extend (32::nat) (bv_msb (int_to_bv a)) (int_to_bv a))"))
    prefer 2
    apply simp
    apply (simp add: bv_extend_Nil)
apply (rotate_tac -1, erule ssubst)
apply (rotate_tac -1, erule ssubst)
apply (subgoal_tac "(zip (hd (bv_extend (32::nat) (bv_msb (int_to_bv a)) (int_to_bv a)) # tl (bv_extend (32::nat) (bv_msb (int_to_bv a)) (int_to_bv a)))
                         (hd (bv_extend (32::nat) (bv_msb (int_to_bv b)) (int_to_bv b)) # tl (bv_extend (32::nat) (bv_msb (int_to_bv b)) (int_to_bv b)))) = 
                          (hd (bv_extend (32::nat) (bv_msb (int_to_bv a)) (int_to_bv a)), hd (bv_extend (32::nat) (bv_msb (int_to_bv b)) (int_to_bv b))) 
# (zip (tl (bv_extend (32::nat) (bv_msb (int_to_bv a)) (int_to_bv a))) (tl (bv_extend (32::nat) (bv_msb (int_to_bv b)) (int_to_bv b))))")
prefer 2
apply (simp only: zip_Cons_Cons)

apply (subgoal_tac "bv_msb (bv_extend (32::nat) (bv_msb (int_to_bv a)) (int_to_bv a)) = hd (bv_extend (32::nat) (bv_msb (int_to_bv a)) (int_to_bv a))")
    prefer 2   
    apply (simp add: bv_msb_hd bv_extend_Nil)
apply (subgoal_tac "bv_msb (bv_extend (32::nat) (bv_msb (int_to_bv b)) (int_to_bv b)) = hd (bv_extend (32::nat) (bv_msb (int_to_bv b)) (int_to_bv b))")
    prefer 2 
    apply (frule_tac l = "bv_extend (32::nat) (bv_msb (int_to_bv b)) (int_to_bv b)" in bv_msb_hd)
    apply assumption
(*apply (subgoal_tac "hd (bv_extend (32::nat) (0::bit) (norm_signed ((0::bit) # nat_to_bv (nat a)))) =
                     hd (bv_extend (32::nat) (bv_msb (int_to_bv b)) (int_to_bv b))")*)
apply (subgoal_tac "bv_msb (bv_extend (32::nat) (bv_msb (int_to_bv a)) (int_to_bv a)) =
                     hd (bv_extend (32::nat) (bv_msb (int_to_bv a)) (int_to_bv a))")

prefer 2
    apply (simp (no_asm_simp) only: bv_msb_def split: if_split)
    apply (rule conjI)
      apply clarsimp
      apply (simp add: norm_signed_One_bv_not_nat_to_bv)
      apply clarify
      apply (subst  int_to_bv_def)
      apply (subst  int_to_bv_def)
      apply (simp only: split: if_split)
      apply (rule conjI)
        apply clarify
        apply linarith
        apply clarify   
        apply (simp add: bv_extend_Nil )     
    (**)
(*apply (subgoal_tac "hd (bv_extend (32::nat) (0::bit) (norm_signed ((0::bit) # nat_to_bv (nat b)))) =
                     hd (bv_extend (32::nat) (bv_msb (int_to_bv b)) (int_to_bv b))")*)
 apply (subgoal_tac "bv_msb (bv_extend (32::nat) (bv_msb (int_to_bv b)) (int_to_bv b)) =
                     hd (bv_extend (32::nat) (bv_msb (int_to_bv b)) (int_to_bv b))")
prefer 2
    apply (simp (no_asm_simp) only: bv_msb_def split: if_split)
    apply (rule conjI)
      apply clarsimp
      apply (simp add: norm_signed_One_bv_not_nat_to_bv)
      apply clarify
      apply (subst  int_to_bv_def)
      apply (subst  int_to_bv_def)
      apply (simp only: split: if_split)
      apply (rule conjI)
        apply clarify
        apply linarith
        apply clarify   
        apply (simp add: bv_extend_Nil )     
    (**)
apply (rotate_tac -1, erule ssubst)
apply (rotate_tac -1, erule ssubst)
apply (rotate_tac -1, erule subst)
apply (rotate_tac -1, erule subst)
(*apply (rotate_tac 7, erule ssubst, erule ssubst)*)
apply (rotate_tac 5, erule ssubst)
apply (subgoal_tac "((0::bit) XOR (0::bit)) = (0::bit)")
    prefer 2
    apply simp
apply (rotate_tac -1, erule ssubst)
apply clarsimp
apply (smt bitNOT_bit.simps(1) bit_ops_same(3) bv_extend_def bv_extend_is_not_empty_1 bv_msb_extend_same bv_msb_hd bv_to_int_msb1 hd_map hd_map head_zip int_to_bv_l_0 int_to_bv_not_zero_is_not_empty list.map_disc_iff list.map_sel(1) list.map_sel(1) list.sel(1) list.simps(3) map_is_Nil_conv old.prod.case s_bitop_def split_conv zero_neq_one zip_Nil2)
done

lemma s_and_neg_power2[rule_format]: 
      "0 < n \<longrightarrow> n < wlen_bit \<longrightarrow> asm_int a \<longrightarrow>  
       intwd_as_nat (s_and a (-(2^n))) = intwd_as_nat a - intwd_as_nat a mod 2^n"
apply clarsimp
apply (subst u_bitop_s_bitop_eq[symmetric])
   apply simp
  apply (simp add: asm_int_def)
  apply clarsimp
  apply (rule conjI)
   apply (simp add: wlen_bit_def)
  apply (subgoal_tac "0 < (2::int)^n")
   apply simp
   apply (smt zero_less_power)
  apply (simp add: zero_less_power_eq)
 apply simp
apply (subst intwd_as_nat_power2_neg, simp)
apply (subst u_bitop_split[where n="n"], simp)
apply (simp add: mod_diff_cancel)
apply (simp add: div_diff_cancel)
apply (simp add: nat_power_mod_cancel)
apply (simp add: nat_power_div)
apply (simp add: u_and_zero)
apply (simp add: u_and_power2_minus1)
apply (simp add: mult_mod_left)
apply (frule asm_nat_intwd_as_nat)
apply (simp add: asm_nat_def)
proof -
  assume a1: "n < wlen_bit"
  assume a2: "intwd_as_nat a < 2 ^ wlen_bit"
  have "\<forall>n. \<not> (n::nat) < n"
    by (metis less_irrefl_nat)
  then have "intwd_as_nat a div 2 ^ n div 2 ^ (wlen_bit - n) = 0"
    using a2 a1 by (metis (no_types) Divides.div_mult2_eq div_eq_0_iff leI 
                    le_add_diff_inverse less_trans power_add)
  then have "intwd_as_nat a div 2 ^ n = intwd_as_nat a div 2 ^ n mod 2 ^ (wlen_bit - n)"
    using div_eq_0_iff by auto
  then show "2 ^ n * (intwd_as_nat a div 2 ^ n mod 2 ^ (wlen_bit - n)) = 
             intwd_as_nat a - intwd_as_nat a mod 2 ^ n"
    by (metis minus_mod_eq_mult_div)
qed

lemma int_and_neg_power2:
  assumes "0 < n" "n < wlen_bit"
  assumes "asm_int a"
  shows "intwd_as_nat (s_and a (- (2^n))) = intwd_as_nat a - intwd_as_nat a mod 2^n"
  using assms
by (simp add: s_and_neg_power2)

lemma int_add_commute:
  shows "int_add i j = int_add j i"
proof -
  have "intwd_as_nat i + intwd_as_nat j = intwd_as_nat j + intwd_as_nat i" by simp
  thus ?thesis by (simp only: int_add_def)
qed

lemma int_add_i_zero: "asm_int i \<Longrightarrow> int_add i 0 = i"
apply (simp add: asm_int_def wlen_bit_def int_add_commute)
apply (case_tac "i < 0")
 apply (simp add: int_add_zero_neg)
apply (simp add: int_add_zero_pos)
done

lemma int_or_one_one[rule_format]:"s_or (1::int) 1 = 1" 
  apply (simp add: s_bitop_def)
  apply (cut_tac nat_to_bv_one)
  apply (simp add: bv_msb_def bv_extend_def)
done

lemma int_sub0 [rule_format]: "asm_int a \<longrightarrow> int_sub a 0 = a"
apply clarify
apply (simp add: int_sub_def)
apply (simp add: intwd_as_nat_0)
apply (simp add: fit_nat_def) 
apply (frule asm_nat_intwd_as_nat)
apply (simp add: asm_nat_def)
apply (simp add: intwd2natwd2intwd)
done

lemma int_add_1_minus1 [rule_format]: "int_add 1 (-1) = 0 \<and> int_add (- 1) 1 = 0"
apply (simp add: int_add_def)
apply (simp add: intwd_as_nat_def)
apply (simp add: wlen_bit_def) 
apply (simp add: fit_nat_def wlen_bit_def natwd_as_int_def)
done

lemma int_sub1 [rule_format]: "asm_int a \<longrightarrow> a \<ge> 1 \<longrightarrow> int_sub a 1 = a - 1"
apply (clarify)
apply (simp add: int_sub_def)
apply (simp only: fit_nat_def)
apply (cut_tac i = "2 ^ wlen_bit" and j = "intwd_as_nat a" and k = "intwd_as_nat 1" in diff_add_assoc)
  apply (simp add: asm_int_def intwd_as_nat_def wlen_bit_def)
apply simp
apply (subgoal_tac "((intwd_as_nat a - intwd_as_nat 1) < 2 ^ wlen_bit) \<and> 0 \<le> (intwd_as_nat a - intwd_as_nat 1)")
  prefer 2
  apply (simp add: asm_int_def intwd_as_nat_def wlen_bit_def)
apply simp
apply (simp add: asm_int_def intwd_as_nat_def natwd_as_int_def wlen_bit_def)
apply arith
done

declare Let_def[simp del]

end
