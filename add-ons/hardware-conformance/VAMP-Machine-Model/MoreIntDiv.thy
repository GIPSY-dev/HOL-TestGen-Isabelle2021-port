(**
 * Copyright (c) 2003-2007 Eyad Alkassar, Matthias Daum, Dirk Leinenbach,
 * Elena Petrova, Alexandra Tsyban.
 * Some rights reserved, Saarland University.
 *
 * This work is licensed under the German-Jurisdiction Creative Commons
 * Attribution Non-commercial Share Alike 2.0 License.
 * See the file LIZENZ for a full copy of the license.
**)
(* $Id: MoreIntDiv.thy 25621 2008-10-08 17:59:26Z DirkLeinenbach $ *)
chapter {* Additional theory about division for integer numbers *}

theory MoreIntDiv imports MoreIntDef MorePower begin

subsection {* nat and int conversion *}

lemma int_div: "int (a div b) = (int a) div (int b)" 
apply (case_tac "0 < b")
 apply (subgoal_tac "\<exists> q r. r < b \<and> a = q * b + r")
  apply (elim exE conjE)
  apply (subgoal_tac "int a = int q * int b + int r")
   apply (rotate_tac -1)
   apply (erule ssubst)
   apply (erule ssubst)
   apply (subgoal_tac "(q * b + r) div b = (q * b) div b + r div b + ((q * b) mod b + r mod b) div b")
    apply (erule ssubst)
    apply (subgoal_tac "(int q * int b + int r) div int b = (int q * int b) div int b + int r div int b + ((int q * int b) mod int b + int r mod int b) div int b")
     apply (erule ssubst)
     apply simp
     apply (rule div_pos_pos_trivial)
      apply simp
     apply simp
    apply (rule zdiv_zadd1_eq)
   apply (rule div_add1_eq)
  apply (erule ssubst)
  apply (simp add: int_mult)
 apply (erule nat_decompose)
apply simp
done

lemma nat_div: "\<lbrakk>0 \<le> a; 0 \<le> b\<rbrakk> \<Longrightarrow> nat (a div b) = nat a div nat b"
apply (subgoal_tac "nat a div nat b = nat (int (nat a div nat b))")
 apply (erule ssubst)
 apply (rule nat_equality)
 apply (simp add: int_div)
apply simp
done

lemma int_mod: "int (a mod b) = (int a) mod (int b)"  
apply (case_tac "0 < b")
 apply (subgoal_tac "\<exists> q r. r < b \<and> a = q * b + r")
  apply (elim exE conjE)
  apply (subgoal_tac "int a = int q * int b + int r")
   apply (rotate_tac -1)
   apply (erule ssubst)
   apply (erule ssubst)
   apply (subgoal_tac "(q * b + r) mod b = ((q * b) mod b + r mod b) mod b")
    apply (erule ssubst)
    apply (subgoal_tac "(int q * int b + int r) mod int b = ((int q * int b) mod int b + int r mod int b) mod int b")
     apply (erule ssubst)
     apply simp
     apply (rule sym)
     apply (rule mod_pos_pos_trivial)
      apply simp
     apply simp
    apply (rule mod_add_eq)
   apply (rule mod_add_eq)
  apply (erule ssubst)
  apply (simp add: int_mult)
 apply (erule nat_decompose)
apply simp
done


subsection {* zdiff *}

lemma zdiff_zadd_neg:"((a::int)-b) = a + (-b)"
  by clarsimp

subsection {* \textbf{mod} *}

lemma negative_mod [rule_format]:
      " (a::int) < 0 \<longrightarrow> 0 < (b::int) \<longrightarrow> (- b) < a \<longrightarrow> a mod b = a + b"
  apply clarify
  apply (simp add: Divides.mod_pos_neg_trivial)
  apply (subgoal_tac "0 \<le> a + b" )
  using mod_add_self2 mod_pos_pos_trivial
  add_less_same_cancel2
  apply metis
  apply simp
done

lemma zmod_zdiff1_eq: 
      "(a-b) mod (c::int) = (a mod c + (- b mod c)) mod c"
  apply (subst zdiff_zadd_neg)
  apply (subst mod_add_eq)
  apply clarsimp
done

lemma zmod_less_pos[rule_format]: "0 \<le> (a::int) \<longrightarrow> a < b \<longrightarrow> a mod b = a"
  apply clarsimp
  apply (cases a,cases b,simp_all)
  apply (auto simp: arith Divides.transfer_int_nat_functions(2) )
done

lemma zmod_less_neg[rule_format]: "-b < (a::int) \<longrightarrow> a < 0 \<longrightarrow> a mod b = b + a"
  by (simp add: negative_mod)

lemma zmod_neg_self: "(-a::int) mod a = 0"
  by (metis mod_self zmod_zminus1_not_zero)

lemma zmod_zdiff_self2: "(b-a) mod a = b mod (a::int)"
  using  Divides.ring_div_class.minus_mod_self2
  by auto


lemma zmod_geq[rule_format]: "0 < (b::int) \<longrightarrow> b \<le> a \<longrightarrow> a mod b = (a - b) mod b"
  by clarsimp

lemma zmod_trivial_pos[rule_format]: 
      "0 \<le> (x::int) \<longrightarrow> x < y \<longrightarrow> x mod y = x"
  by (simp add: mod_pos_pos_trivial)

lemma zmod_if_neg[rule_format]: 
  "(x::int) < 0 \<longrightarrow> x mod y = (if -x < y then (y + x) else (x - y) mod y)"
  by (simp add: zmod_less_neg)

lemma zmod_trivial_neg[rule_format]: 
  "(x::int) < 0 \<longrightarrow> y < x \<longrightarrow> x mod y = x"
  by (simp add: mod_neg_neg_trivial)

lemma zmod_if_pos[rule_format]: 
  "0 \<le> (x::int) \<longrightarrow> x mod y = (if x < y then x else (x - y) mod y)"
  by (simp add: mod_pos_pos_trivial)

lemma nat_mod[rule_format]: "0 \<le> a \<longrightarrow> nat a mod b = nat (a mod (int b))"
  apply clarsimp
  apply (insert int_mod[where a="nat a" and b="b"])
  apply clarsimp
  apply arith
done

lemma zdiff_zmod_left: "(x mod m - y) mod m = (x-y) mod (m::int)"
  by (simp only: zdiff_zmod_left)

lemma zmod_le_divisor : "a\<ge>0 \<and> n>0 \<longrightarrow> a mod n \<le> (n::int)"
 using  less_le pos_mod_conj
 by fast


subsection {* \textbf{div} *}

lemma i_div_ge_0: "\<lbrakk>(0::int) \<le> n; 0 < m\<rbrakk> \<Longrightarrow> 0 \<le> n div m"
apply (subgoal_tac "(0::int) = 0 div m")
 apply (erule ssubst)
by (erule zdiv_mono1) simp_all

lemma i_div_less_self: "\<lbrakk>0 < x; 1 < k\<rbrakk> \<Longrightarrow> x div k < (x::int)"
apply (subgoal_tac "x div k \<le> x div 1")
 prefer 2
 apply (rule zdiv_mono2)
   apply simp
  apply simp
 apply simp
apply (subgoal_tac "x div k \<noteq> x")
 apply simp
apply (insert i_decompose [of k x])
apply simp
apply (elim exE conjE)
apply (subgoal_tac "r div k = 0")
 prefer 2
 apply (erule div_pos_pos_trivial)
 apply assumption
apply (case_tac "q = 0")
 apply simp
apply (rotate_tac -1, erule ssubst)
apply (subgoal_tac "(q * k + r) div k = q * k div k + r div k + (q * k mod k + r mod k) div k")
 apply (rotate_tac -1, erule ssubst)
 apply simp
 apply (subgoal_tac "q < q * k + r")
  apply simp
 apply (rule_tac j = "q * k" in i_less_le_trans)
  apply (subgoal_tac "q * 1 < q * k")
   apply simp
  apply (erule zmult_zless_mono2)
  apply simp
 apply simp
apply (rule zdiv_zadd1_eq)
done

lemma i_div_add_mult: "c \<noteq> 0 \<Longrightarrow> (a * c + b) div c = a + b div (c::int)"
apply (subgoal_tac "(a * c + b) div c = a * c div c + b div c + (a * c mod c + b mod c) div c")
 apply (erule ssubst)
 apply simp
apply (rule zdiv_zadd1_eq)
done

lemma i_mult_div_le_self: "\<lbrakk>0 < b; 0 \<le> c\<rbrakk> \<Longrightarrow> b * (c div b) \<le> (c::int)"
  using int_mod_ge_zero mult_div_mod_eq
  proof -
    assume "0 < b"
    then show ?thesis
      by (smt int_mod_ge_zero mult_div_mod_eq)
  qed

lemma i_le_div: "\<lbrakk>0 \<le> n; 0 < k; k \<le> b; x * b < n\<rbrakk> \<Longrightarrow> x \<le> n div (k::int)"
  apply (subgoal_tac "x * b \<le> n")
   apply (rule_tac y = "n div b" in order_trans)
    apply (subgoal_tac "x = x * b div b")
     apply (erule ssubst)
     apply (erule zdiv_mono1)
     apply simp_all
  apply (drule zdiv_mono2)
   apply assumption
  apply assumption
  apply assumption
done

lemma i_power_div_base: "\<lbrakk>0 < m; 0 < k\<rbrakk> \<Longrightarrow> k ^ m div k = (k::int) ^ (m - Suc 0)"
  using Divides.int_power_div_base
  by auto

lemma i_less_div: 
      "\<lbrakk>0 \<le> n; 0 < k; k \<le> b; x * b < n; n mod k = 0\<rbrakk> \<Longrightarrow> x < n div (k::int)"

proof -
  have 1: "0 \<le> k * x \<Longrightarrow>
    0 < k \<Longrightarrow> k \<le> b \<Longrightarrow> x * b < k * x \<Longrightarrow> b \<noteq> k \<Longrightarrow> n = k * x \<Longrightarrow> False"
  proof -
    assume a1: "0 \<le> k * x"
    assume a2: "0 < k"
    assume a3: "k \<le> b"
    assume a4: "x * b < k * x"
    assume a5: "n = k * x"
    then have "0 \<le> n"
      using a1 by metis
    then show False
      using a5 a4 a3 a2
     by (simp add: mult.commute mult_less_cancel_right zero_le_mult_iff)
  qed
  show "\<lbrakk>0 \<le> n; 0 < k; k \<le> b; x * b < n; n mod k = 0\<rbrakk> \<Longrightarrow> x < n div (k::int)" 
  apply (frule i_le_div)
     apply assumption+
  apply (case_tac "x = n div k")
   apply simp
   apply (insert mult_div_mod_eq [of n k])
    apply simp
    apply (case_tac "b = k")
     apply simp
     apply (subgoal_tac "k * (n div k) = n")
      apply auto
      using 1 
      apply simp
  done
qed

subsection {* \textbf{smod and umod} *}
(* attention: smod and umod compute modulo 2^bw!!! *)
(* signed modulo *)


definition smod :: "int \<Rightarrow> nat \<Rightarrow> int" (infixl "smod" 70)
where                    
  " a smod  bw \<equiv> 
   (
     let 
       x = a mod 2^bw
     in
       if x < 2^(bw - 1) then
         x
       else
         x - 2^bw
   )
  "
 
definition umod :: "nat \<Rightarrow> nat \<Rightarrow> nat"                   
 where
  " umod a bw \<equiv> a mod 2^bw"

lemma smod_less[rule_format]: 
      "  a smod  b < 2^(b - Suc 0)"
   apply (simp add: smod_def)
   apply (simp add: Let_def)
   apply clarsimp
   apply (subgoal_tac "a mod 2^b <  2 ^ (b - Suc 0) + 2 ^ b")
    apply simp
   apply (subgoal_tac "(0::int) < 2^b")
    apply (subgoal_tac "a mod  2 ^ b < 2 ^ b")
     apply (subgoal_tac "(0::int) < 2^(b- Suc 0)")
      apply simp
     apply (subgoal_tac "(0::int) < 2")
      apply (simp_all)
   apply (subgoal_tac "(0::int) < 2")
    apply (simp_all)
    using  Divides.pos_mod_bound One_nat_def add.commute less_add_same_cancel1 
           less_trans numeral_1_eq_Suc_0 pow2_greater_zero_int
    apply metis
done

lemma smod_ge[rule_format]: "- (2^(b - Suc 0)) \<le>   a smod  b"
apply (simp add:  smod_def)
apply (simp add: Let_def)
apply (rule conjI)
 apply clarsimp
 apply (subgoal_tac "0 \<le> a mod 2 ^ b")
  apply (simp add: less_neg)
 apply (subgoal_tac "(0::int) < 2^b")
  apply simp
 apply (subgoal_tac "(0::int) < 2")
  apply (simp)
 apply auto
 apply (metis diff_0 diff_0_right i_le_trans minus_le_iff mod_0 pos_mod_conj pow2_greater_zero_int zmod_le_divisor)
apply (subgoal_tac "(2::int)^b - (2 ^ (b - Suc 0)) = 2 ^ (b - Suc 0)")
 apply simp
apply (subgoal_tac "0 < b")
 apply (simp add: int_power_Suc)
apply (case_tac b, simp, simp)
done

lemma smod_0[simp]:"   0 smod n = 0"
  by (simp add: smod_def)

lemma zmod_zmult_zmult1_aux1:
     "[| (0::int) < b;  c \<noteq> 0 |] ==> (c*a) mod (c*b) = c * (a mod b)"
by (subst zmod_zmult2_eq, auto)

lemma zmod_zmult_zmult1_aux2:
     "[| b < (0::int);  c \<noteq> 0 |] ==> (c*a) mod (c*b) = c * (a mod b)"
apply (subgoal_tac " (c * (-a)) mod (c * (-b)) = c * ((-a) mod (-b))")
apply (rule_tac [2] zmod_zmult_zmult1_aux1, auto)
done

lemma zmod_zmult_zmult1: "(c*a) mod (c*b) = (c::int) * (a mod b)"
apply (case_tac "b = 0", simp)
apply (case_tac "c = 0", simp)
apply (auto simp add: linorder_neq_iff zmod_zmult_zmult1_aux1 zmod_zmult_zmult1_aux2)
done

lemma smod_zmult_zmult1[rule_format]:
       "((2::int)^c) * a smod (c + b) =  (((2::int)^c) * (a smod b))"
apply (case_tac "b = 0", simp)
apply (case_tac "c = 0", simp)
apply (simp_all add: smod_def Let_def)
apply (rule conjI impI)+
apply (insert  zmod_zmult_zmult1 [of "((2::int) ^ c)" "a" "((2::int) ^ b)"])
apply (subgoal_tac "((2::int) ^ (c + b)) = (((2::int) ^ c) * ((2::int) ^ b))")
apply simp
apply (simp add: power_add)
apply (simp add: power_add)
apply (subgoal_tac "((2::int) ^ ((c + b) - (Suc (0::nat)))) =
                    (((2::int) ^ c) * ((2::int) ^ (b -(Suc (0::nat)) )))")
apply simp
apply (frule_tac a = "(a mod ((2::int) ^ b))" and 
                 b = "((2::int) ^ (b - (Suc (0::nat))))" and 
                 c = "((2::int) ^ c)" in i_mult_less_mono)
apply simp
apply simp
apply (insert power_add [of "(2::int)" "c" "(b - (Suc (0::nat)))"])
apply simp
apply simp
apply (rule conjI impI )
apply (insert power_add [of "(2::int)" "c" "b"])
apply simp
apply (subgoal_tac "(\<not> ((a mod ((2::int) ^ b)) < ((2::int) ^ (b - (Suc (0::nat)))))) \<longrightarrow>  
                     (((2::int) ^ (b - (Suc (0::nat)))) \<le> (a mod ((2::int) ^ b)))")
apply (subgoal_tac "(((2::int) ^ (b - (Suc (0::nat)))) \<le> (a mod ((2::int) ^ b))) \<longrightarrow> 
                    ((((2::int) ^ c) * ((2::int) ^ (b - (Suc (0::nat))))) \<le> 
                    (((2::int) ^ c) * (a mod ((2::int) ^ b))))")
apply simp
apply (subgoal_tac "((0::int) < ((2::int) ^ c)) \<longrightarrow>((0::int) \<le> ((2::int) ^ c))")
prefer 2
apply arith
apply simp
apply (insert distrib_left[of "((2::int) ^ c)" "(a mod ((2::int) ^ b))" "( -((2::int) ^ b) )"])
apply simp_all
done

lemma smod_zmult1_eq'[rule_format]:
      "(( ((a::int) * (b::int))smod  (c::nat)) = ( (( a smod c) * b) smod  c))"

apply (case_tac "c = 0")
apply (simp add: "smod_def" )
apply (simp add: "smod_def" Let_def)
proof -
  have "\<And>i ia ib. (i::int) * (ia - ib) mod ib = i * ia mod ib"
    by (metis (no_types) mod_mult_right_eq zmod_zdiff_self2)
  moreover
  { assume "a mod 2 ^ c < 2 ^ (c - Suc 0) \<and> \<not> a * b mod 2 ^ c < 2 ^ (c - Suc 0)"
    then have "(a mod 2 ^ c < 2 ^ (c - Suc 0) \<longrightarrow> 
               (a * b mod 2 ^ c < 2 ^ (c - Suc 0) \<longrightarrow> 
               (a mod 2 ^ c * b mod 2 ^ c < 2 ^ (c - Suc 0) \<longrightarrow> 
                a * b mod 2 ^ c = a mod 2 ^ c * b mod 2 ^ c) \<and> 
                (\<not> a mod 2 ^ c * b mod 2 ^ c < 2 ^ (c - Suc 0) \<longrightarrow> 
                a * b mod 2 ^ c = a mod 2 ^ c * b mod 2 ^ c - 2 ^ c)) \<and> 
               (\<not> a * b mod 2 ^ c < 2 ^ (c - Suc 0) \<longrightarrow> 
               (a mod 2 ^ c * b mod 2 ^ c < 2 ^ (c - Suc 0) \<longrightarrow>
                a * b mod 2 ^ c - 2 ^ c = a mod 2 ^ c * b mod 2 ^ c) \<and> 
               (\<not> a mod 2 ^ c * b mod 2 ^ c < 2 ^ (c - Suc 0) \<longrightarrow> 
                a * b mod 2 ^ c = a mod 2 ^ c * b mod 2 ^ c))) \<and> 
                  (\<not> a mod 2 ^ c < 2 ^ (c - Suc 0) \<longrightarrow> (a * b mod 2 ^ c < 2 ^ (c - Suc 0) \<longrightarrow> 
               ((a mod 2 ^ c - 2 ^ c) * b mod 2 ^ c < 2 ^ (c - Suc 0) \<longrightarrow> a * b mod 2 ^ c = 
               (a mod 2 ^ c - 2 ^ c) * b mod 2 ^ c) \<and> 
               (\<not> (a mod 2 ^ c - 2 ^ c) * b mod 2 ^ c < 2 ^ (c - Suc 0) \<longrightarrow> a * b mod 2 ^ c = 
               (a mod 2 ^ c - 2 ^ c) * b mod 2 ^ c - 2 ^ c)) \<and> 
               (\<not> a * b mod 2 ^ c < 2 ^ (c - Suc 0) \<longrightarrow> 
                ((a mod 2 ^ c - 2 ^ c) * b mod 2 ^ c < 2 ^ (c - Suc 0) \<longrightarrow> 
               a * b mod 2 ^ c - 2 ^ c = (a mod 2 ^ c - 2 ^ c) * b mod 2 ^ c) \<and> 
              (\<not> (a mod 2 ^ c - 2 ^ c) * b mod 2 ^ c < 2 ^ (c - Suc 0) \<longrightarrow> a * b mod 2 ^ c = 
              (a mod 2 ^ c - 2 ^ c) * b mod 2 ^ c)))"
      by (metis (no_types) mod_mult_right_eq mult.commute) }
  ultimately show "(a mod 2 ^ c < 2 ^ (c - Suc 0) \<longrightarrow> 
               (a * b mod 2 ^ c < 2 ^ (c - Suc 0) \<longrightarrow> 
               (a mod 2 ^ c * b mod 2 ^ c < 2 ^ (c - Suc 0) \<longrightarrow> 
                a * b mod 2 ^ c = a mod 2 ^ c * b mod 2 ^ c) \<and> 
                (\<not> a mod 2 ^ c * b mod 2 ^ c < 2 ^ (c - Suc 0) \<longrightarrow> 
                a * b mod 2 ^ c = a mod 2 ^ c * b mod 2 ^ c - 2 ^ c)) \<and> 
               (\<not> a * b mod 2 ^ c < 2 ^ (c - Suc 0) \<longrightarrow> 
               (a mod 2 ^ c * b mod 2 ^ c < 2 ^ (c - Suc 0) \<longrightarrow>
                a * b mod 2 ^ c - 2 ^ c = a mod 2 ^ c * b mod 2 ^ c) \<and> 
               (\<not> a mod 2 ^ c * b mod 2 ^ c < 2 ^ (c - Suc 0) \<longrightarrow> 
                a * b mod 2 ^ c = a mod 2 ^ c * b mod 2 ^ c))) \<and> 
                  (\<not> a mod 2 ^ c < 2 ^ (c - Suc 0) \<longrightarrow> (a * b mod 2 ^ c < 2 ^ (c - Suc 0) \<longrightarrow> 
               ((a mod 2 ^ c - 2 ^ c) * b mod 2 ^ c < 2 ^ (c - Suc 0) \<longrightarrow> a * b mod 2 ^ c = 
               (a mod 2 ^ c - 2 ^ c) * b mod 2 ^ c) \<and> 
               (\<not> (a mod 2 ^ c - 2 ^ c) * b mod 2 ^ c < 2 ^ (c - Suc 0) \<longrightarrow> a * b mod 2 ^ c = 
               (a mod 2 ^ c - 2 ^ c) * b mod 2 ^ c - 2 ^ c)) \<and> 
               (\<not> a * b mod 2 ^ c < 2 ^ (c - Suc 0) \<longrightarrow> 
                ((a mod 2 ^ c - 2 ^ c) * b mod 2 ^ c < 2 ^ (c - Suc 0) \<longrightarrow> 
               a * b mod 2 ^ c - 2 ^ c = (a mod 2 ^ c - 2 ^ c) * b mod 2 ^ c) \<and> 
              (\<not> (a mod 2 ^ c - 2 ^ c) * b mod 2 ^ c < 2 ^ (c - Suc 0) \<longrightarrow> a * b mod 2 ^ c = 
              (a mod 2 ^ c - 2 ^ c) * b mod 2 ^ c)))"
     using mod_mult_right_eq mult.commute
    by (metis (no_types) )
qed



lemma smod_zadd1_eq[rule_format]:
      " (a + b) smod c =  ((  a smod c) + (  b smod c) ) smod c"
  apply (insert mod_add_eq [of "a" "b" "((2::int)^c)"])
  apply (simp add:  smod_def Let_def)
  using zmod_zdiff_self2
  apply (smt )
done

lemma smod_equality[rule_format]:
      "bw \<noteq> 0 \<longrightarrow> (-(2^(bw - 1))) \<le> x \<and> x < (2^(bw - 1)) \<longrightarrow> (x smod bw) = x"
  apply (case_tac "0 =  x")
  apply simp
  apply (case_tac "0 < x")
  apply clarsimp
  apply (simp add: smod_def Let_def)
  
  apply (frule_tac i = "x" and j = "((2::int) ^ (bw - (Suc (0::nat))))" and 
                   k = "((2::int) ^ bw)" in i_less_trans)
  apply simp
  apply (simp add: mod_pos_pos_trivial)
  apply clarsimp
  apply (simp add: smod_def Let_def)
  apply (case_tac "(x = (- ((2::int) ^ (bw - (Suc (0::nat))))) )")
  apply (subgoal_tac "(- ((2::int) ^ (bw - (Suc (0::nat))))) < 0")
  prefer 2
  apply simp
  apply (frule_tac  a = "(- ((2::int) ^ (bw - (Suc (0::nat)))))" and 
                    b = "((2::int) ^ (bw ))" in negative_mod)
  apply simp 
  apply simp
  apply simp
  apply (insert power_add [of "(2::int)" "(bw - (Suc (0::nat)))" "1"])
  apply simp
  apply (subgoal_tac " x < 0")
  prefer 2
  apply simp
  apply auto
  apply (frule_tac  a = "x" and b = "((2::int) ^ (bw ))" in negative_mod)
  apply simp
  apply simp+
  apply (simp add: zmod_less_neg)
done

lemma smod_smod_trivial[rule_format]:"(a smod b) smod b = a smod b"
  by (simp add: "smod_def" Let_def)


end
