(**
 * Copyright (c) 2004-2008 Dirk Leinenbach, Alexandra Tsyban.
 * Some rights reserved, Saarland University.
 *
 * This work is licensed under the German-Jurisdiction Creative Commons
 * Attribution Non-commercial Share Alike 2.0 License.
 * See the file LIZENZ for a full copy of the license.
**)
(* $Id: arith_range.thy 24808 2008-08-08 18:44:51Z DirkLeinenbach $ *)
theory arith_range imports MoreWord begin

text {*
  This theory contains some definitions regarding the range of arithmetic types like int, unsigned int, @{text \<dots>}
*}

definition 
  "int_bitwidth == (32::nat)"

definition 
 "unsigned_int_bitwidth == (32::nat)"
definition 
 "char_bitwidth == (8::nat)"
  
definition -- "byte length in bits"
  "bytelen_bit == (8::nat)"

definition -- "word length in bits"
  "wordlen_bit == (32::nat)"

definition
  -- "upper bound (exclusive) and lower bound (inclusive) of size of integers"
  int_size_ub :: int
where
  "int_size_ub == 2^(wordlen_bit - 1)"
definition  int_size_lb :: int
where  "int_size_lb == - int_size_ub"

  -- "upper bound (exclusive) and lower bound (inclusive) of size of unsigned integers"
definition  un_int_size_ub :: nat
where  "un_int_size_ub == 2^wordlen_bit"
definition  un_int_size_lb :: nat
where
  "un_int_size_lb == 0"

  -- "upper bound (exclusive) and lower bound (inclusive) of size of characters"
definition  chr_size_ub :: int
where  "chr_size_ub == 2^(bytelen_bit - 1)"
definition  chr_size_lb :: int
 where "chr_size_lb == - chr_size_ub"


text {*
  The minimum and maximum values for the different basic types in C0.
  *}

definition
  min_char :: "int"
where
  "min_char \<equiv> -(2^(char_bitwidth - 1))"

definition  max_char :: "int"
 where  "max_char \<equiv> 2^(char_bitwidth - 1) - 1"

definition  min_int :: "int"
where  "min_int \<equiv>  -(2^(int_bitwidth - 1))"

definition  max_int :: "int"
where  "max_int \<equiv> 2^(int_bitwidth - 1) - 1"

definition  min_unsigned_int :: "int"
where  "min_unsigned_int \<equiv> 0"

definition  max_unsigned_int :: "int"
where  "max_unsigned_int \<equiv> 2^unsigned_int_bitwidth - 1"

text {*
We define predicates which state if values of the basic types are valid or not.
*}

definition is_valid_int::"int \<Rightarrow> bool"
where
  "is_valid_int i \<equiv> (min_int \<le> i) \<and> (i \<le> max_int)"

definition  is_valid_unsigned_int::"nat \<Rightarrow> bool"
 where "is_valid_unsigned_int n \<equiv> (min_unsigned_int \<le> int n) \<and> (int n \<le> max_unsigned_int)"

definition  is_valid_char::"int \<Rightarrow> bool"
where  "is_valid_char c \<equiv> (min_char \<le> c) \<and> (c \<le> max_char)"

lemma is_valid_unsigned_int_monotonic[rule_format]: "is_valid_unsigned_int a \<longrightarrow> b \<le> a \<longrightarrow> is_valid_unsigned_int b"
apply clarsimp
apply (simp add: is_valid_unsigned_int_def)
apply (simp add: min_unsigned_int_def)
done

lemma smod_int_bitwidth_is_valid_int[simp]: 
      "is_valid_int (a smod int_bitwidth)"
apply (simp add: is_valid_int_def)
apply (simp add: min_int_def max_int_def)
apply (simp add: smod_less smod_ge)
done

lemma smod_char_bitwidth_is_valid_char[simp]: 
      "is_valid_char (a smod char_bitwidth)"
apply (simp add: is_valid_char_def)
apply (simp add: min_char_def max_char_def)
apply (simp add: smod_less smod_ge)
done

lemma umod_unsigned_int_bitwidth_is_valid_unsigned_int[simp]: 
      "is_valid_unsigned_int (umod a  unsigned_int_bitwidth)"
apply (simp add: "umod_def")
apply (simp add: is_valid_unsigned_int_def)
apply (simp add: min_unsigned_int_def max_unsigned_int_def)
apply (simp add: unsigned_int_bitwidth_def)
done

lemma mod_unsigned_int_bitwidth_is_valid_unsigned_int[simp]: 
      "is_valid_unsigned_int (nat (a mod 2^unsigned_int_bitwidth))"
apply (simp add: is_valid_unsigned_int_def)
apply (simp add: min_unsigned_int_def max_unsigned_int_def)
done

lemma modwrap_is_valid_int[simp]: 
      "is_valid_int (a modwrap int_size_ub)"
apply (simp add: is_valid_int_def modwrap_def)
apply (simp add: min_int_def int_size_ub_def max_int_def)
apply (simp add: int_bitwidth_def wordlen_bit_def)
done

lemma modwrap_is_valid_char[simp]: 
      "is_valid_char (a modwrap chr_size_ub)"
apply (simp add: is_valid_char_def modwrap_def)
apply (simp add: min_char_def chr_size_ub_def max_char_def)
apply (simp add: char_bitwidth_def bytelen_bit_def)
done

lemma mod_is_valid_unsigned_int[simp]: 
      "is_valid_unsigned_int (a mod un_int_size_ub)"
apply (simp add: is_valid_unsigned_int_def)
apply (simp add: min_unsigned_int_def un_int_size_ub_def max_unsigned_int_def)
apply (simp add: unsigned_int_bitwidth_def wordlen_bit_def)
done

lemma mod_is_valid_unsigned_int2[simp]: 
      "is_valid_unsigned_int (nat (a mod (int un_int_size_ub)))"
apply (simp add: is_valid_unsigned_int_def)
apply (simp add: min_unsigned_int_def un_int_size_ub_def max_unsigned_int_def)
apply (simp add: unsigned_int_bitwidth_def wordlen_bit_def)
done

definition -- "word length in bytes/bits"
  "wlen_byte == (4::nat)"
definition
  "wlen_bit == (32::nat)"

text{* Meaning of the following function is: @{text "nat (bv_to_nat (sxt_wd (int_to_bv n)))"} *}

definition intwd_as_nat :: "int \<Rightarrow> nat"
where
"intwd_as_nat n == if 2^(wlen_bit - 1) \<le> n \<and> n < 2^wlen_bit 
                   then nat (n + 2^(wlen_bit - 1)) 
                   else 
                   if n < -(2^(wlen_bit - 1)) then nat (-n + 2^(wlen_bit - 1)) else
                   if -(2^(wlen_bit - 1)) \<le> n \<and> n < 0 then nat (n + 2^wlen_bit)
                   else nat n"

text{* Meaning of the following function is: @{text "bv_to_int (fill0_wd (nat_to_bv (int n)))"} *}

definition natwd_as_int :: "nat \<Rightarrow> int"
where
"natwd_as_int n == if 2^(wlen_bit - 1) \<le> n \<and> n < 2^wlen_bit 
                   then int n - (2^wlen_bit) 
                   else int n"

definition asm_int :: "int \<Rightarrow> bool"
where
  "asm_int n == -(2^(wlen_bit - 1)) \<le> n \<and> n < 2^(wlen_bit - 1)"

definition asm_nat :: "nat \<Rightarrow> bool"
where
  "asm_nat n == n < 2^wlen_bit"

text {* some lemmas *}

lemma intwd_as_nat_inj: "inj_on intwd_as_nat {i. -(2^31) \<le> i \<and> i < 2^31}"
apply (simp add: inj_on_def)
apply (simp add: intwd_as_nat_def)
apply (simp add: wlen_bit_def)
apply clarsimp
apply auto
done

lemma asm_int_zero: "asm_int 0"
by (simp add: asm_int_def wlen_bit_def)

lemma asm_int_one: "asm_int 1"
by (simp add: asm_int_def wlen_bit_def)

--"div"

lemma div_wlen_bit_is_zero: "asm_nat n \<Longrightarrow> n div 2^wlen_bit = 0"
by (simp add: asm_nat_def wlen_bit_def)

lemma asm_int_div: "\<lbrakk>0 < m; asm_int i\<rbrakk> \<Longrightarrow> asm_int (i div m)"
apply (clarsimp simp add: asm_int_def wlen_bit_def)
apply (case_tac "i < 0")
 apply (rule conjI)
  apply (rule_tac y = "i div 1" in order_trans)
   apply simp
  apply (erule zdiv_mono2_neg)
   apply simp
  apply simp
 apply (rule_tac j = "0" in i_less_trans)
  apply (simp add: div_neg_pos_less0)
 apply simp
apply (case_tac "0 \<le> i")
 apply (rule conjI)
  apply (rule_tac y = "0" in order_trans)
   apply simp
  apply (simp add: pos_imp_zdiv_nonneg_iff)
 apply (rule_tac j = "i div 1" in i_le_less_trans)
  apply (erule zdiv_mono2)
   apply simp_all
done

lemma asm_nat_div_power: "asm_nat n \<Longrightarrow> asm_nat (n div 2 ^ p)"
apply (simp add: asm_nat_def wlen_bit_def)
apply (case_tac "n = 0", simp)
apply (case_tac p, simp)
apply (rule_tac y = "n" in less_trans)
 apply (rule div_less_dividend)
  apply (rotate_tac -1, erule ssubst)
  apply (rule power_gt1)
  apply simp_all
done

--"mod"

lemma mod_wlen_bit_is_same: "asm_nat n \<Longrightarrow> n mod 2^wlen_bit = n"
by (simp add: asm_nat_def wlen_bit_def)


lemma asm_nat_mod: "\<lbrakk>0 < m; asm_nat n\<rbrakk> \<Longrightarrow> asm_nat (n mod m)"
apply (simp add: asm_nat_def wlen_bit_def)
apply (case_tac "n < m")
 apply (simp add: mod_less)
apply (rule_tac y = "m" in less_trans)
 apply (simp add: mod_less_divisor)
apply (rule_tac y = "n" in le_less_trans)
 apply simp_all
done


lemma asm_nat_mod_wlen_bit: "asm_nat (n mod 2 ^ wlen_bit)"
by (simp add: asm_nat_def wlen_bit_def)


lemma asm_nat_mod_mult: 
  assumes 1 : " x = 2 ^ (wlen_bit - p)" and 2 : " y = 2 ^ p" and 3:" p \<le> wlen_bit"
  shows   "asm_nat (n mod x * y)"
proof -
   have * : "4294967296 = ((2::nat) ^ (32 - p) * (2::nat) ^ p)" 
            by(subst power_add_2, simp add: 3[simplified wlen_bit_def] wlen_bit_def) 

   show ?thesis
   apply(insert  1 2 3)
   apply(clarsimp simp add: asm_nat_def wlen_bit_def)
   by(subst *, simp add: wlen_bit_def)
qed

lemma asm_nat_mod_mult_65536: "asm_nat n \<Longrightarrow> asm_nat (n mod 65536 * 65536)"
apply (rule_tac p = "16" in asm_nat_mod_mult)
  apply (simp add: wlen_bit_def)+
done

lemma asm_int_int_mod: "0 < n \<and> n \<le> 2 ^ 31 \<Longrightarrow> asm_int (int (x mod n))"
apply (simp add: asm_int_def)
apply (rule conjI)
 apply (simp add: wlen_bit_def)
apply (simp add: wlen_bit_def)
apply (subgoal_tac "2147483648 = int 2147483648")
 prefer 2
 apply simp
apply (erule ssubst)
apply (subst of_nat_less_iff)
apply (metis mod_less_divisor order_less_le_trans)
done
end
