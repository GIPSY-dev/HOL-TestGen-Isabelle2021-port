(**
 * Copyright (c) 2003-2007 Igor Averbukh, Matthias Daum, Dirk Leinenbach,
 * Elena Petrova, Alexandra Tsyban.
 * Some rights reserved, Saarland University.
 *
 * This work is licensed under the German-Jurisdiction Creative Commons
 * Attribution Non-commercial Share Alike 2.0 License.
 * See the file LIZENZ for a full copy of the license.
**)
(* $Id: MoreNat.thy 28385 2009-06-15 13:53:55Z MarkHillebrand $ *)
chapter {* Additional theory about natural numbers *}

theory MoreNat imports Main begin




lemma nat_decompose[rule_format]:
  "0 < b \<longrightarrow> (\<exists> q r. r < b \<and> (a::nat) = q * b + r)"
proof (induct a) print_cases
  case 0 show ?case by simp
next
  case (Suc n) show ?case
    apply(insert Suc.hyps)
    apply (rule impI)
    apply (drule mp, assumption)
    apply (elim exE conjE)
    apply (case_tac "Suc r = b")
      apply (rule_tac x = "Suc q" in exI)
      apply (rule_tac x = "0" in exI)
     apply simp
    apply (rule_tac x = "q" in exI)
    apply (rule_tac x = "Suc r" in exI)
    apply simp
    done
qed

lemma mult_add_less[rule_format]: "(i::nat) < j \<longrightarrow> a < s \<longrightarrow> i * s + a < j * s"
apply clarsimp
apply (insert mult_le_mono1[where k="s" and i="i+1" and j="j"])
apply simp
done

lemma mult_add_le[rule_format]: "(i::nat) < j \<longrightarrow> a \<le> s \<longrightarrow> i * s + a \<le> j * s"
apply clarsimp
apply (insert mult_le_mono1[where k="s" and i="i+1" and j="j"])
apply simp
done

subsection{* function for base 2 logarithm computation *}


primrec log2rec :: "nat \<Rightarrow> nat \<Rightarrow> nat"
where  "log2rec 0 n = 0"
     | "log2rec (Suc k) n = (if (2 ^ k < n) then k else (log2rec k n))"


definition log2 :: "nat \<Rightarrow> nat"
where     "log2 n == if(n=1) then 0 else Suc (log2rec n n)"

(*properties*)
lemma log2rec_correct_up1: "\<forall>x y. y>0 \<longrightarrow> log2rec x y < y"
 apply (rule allI)
 apply (induct_tac x)
  apply simp
 apply (rule allI)
 apply (rule impI)
 apply (case_tac "2^n < y")
  apply simp
  apply (subgoal_tac "\<forall>a b. 2^a < b \<longrightarrow> a < b")
   prefer 2
   apply (thin_tac "\<forall>y>0. log2rec n y < y")
   apply (thin_tac "2 ^ n < y")
   apply (rule allI)+
   apply (induct_tac b)
    apply simp
   apply clarsimp 
   apply (case_tac "2 ^ a = na")
    apply simp
    apply (subgoal_tac "\<forall>x y. 2^x = y \<longrightarrow> x < y")
     prefer 2
     apply (rule allI)
     apply (induct_tac x)
      apply simp
     apply simp
    apply (erule_tac x = "a" in allE)
    apply (erule_tac x = "na" in allE)
    apply simp
   apply simp
  apply (thin_tac "\<forall>y>0. log2rec n y < y")
  apply (erule_tac x = "n" in allE)
  apply (erule_tac x = "y" in allE)
  apply simp
 apply simp
done

lemma log2rec_correct_up2: "\<forall>x y. y>0 \<longrightarrow> log2rec x y \<le> x"
 apply (rule allI)
 apply (induct_tac x)
  apply simp
 apply (rule allI)
 apply (rule impI)
 apply clarsimp
 apply (erule_tac x = "y" in allE)
 apply simp
done
 
lemma log2rec_correct_special: "\<forall>x y. log2rec x (2^y) \<le> y"
 apply (rule allI)
 apply (induct_tac x)
  apply simp
 apply (rule allI)
 apply (erule_tac x = "y" in allE)
 apply simp
done

lemma log2rec_cut1: "\<forall>z x y. (2::nat) ^ x \<le> 2 ^ y \<longrightarrow> y \<le> z \<longrightarrow> log2rec y (2 ^ x) = log2rec z (2 ^ x)"
 apply (rule allI)
 apply (induct_tac z)
  apply simp
 apply (rule allI)+
 apply (rule impI)+
 apply (erule_tac x = "x" in allE)
 apply (erule_tac x = "y" in allE)
 apply simp
 apply (case_tac "y = Suc n")
  apply simp
 apply simp
done

lemma log2rec_cut2: "\<forall>z x y. x > 0 \<longrightarrow> x \<le> 2 ^ y \<longrightarrow> y \<le> z \<longrightarrow> log2rec y x = log2rec z x"
 apply (rule allI)
 apply (induct_tac z)
  apply simp
 apply (rule allI)+
 apply (rule impI)+
 apply (erule_tac x = "x" in allE)
 apply (erule_tac x = "y" in allE)
 apply simp
 apply (case_tac "y = Suc n")
  apply simp
 apply simp
 apply (rule impI)
 apply (case_tac "x = 2^y")
  apply simp
 apply simp
 apply (subgoal_tac "x < 2^y")
  prefer 2
  apply simp
 apply clarsimp
 apply (case_tac n)
  apply simp
 apply simp
 apply clarsimp
 apply (subgoal_tac "y \<le> Suc (log2rec y x)")
  prefer 2
  apply simp
 apply clarsimp 
 apply (subgoal_tac "2 ^ (Suc (log2rec y x)) < x")  
  prefer 2
  apply simp
 apply (subgoal_tac "\<forall>a b. a\<le>b \<longrightarrow> (2::nat)^a \<le> 2^b")
  apply (erule_tac x = "y" in allE)
  apply (erule_tac x = "Suc (log2rec y x)" in allE)
  apply simp
 apply simp
done

lemma log2rec_cut3: 
  "\<forall>x y z. x > 0 \<longrightarrow> 2 ^ x \<le> y \<longrightarrow> z < 2 ^ Suc x \<longrightarrow> y \<le> z \<longrightarrow> 
           log2rec x y = log2rec x z \<and> log2rec x y = x - Suc 0"
 apply (rule allI)
 apply (induct_tac x)
  apply simp
 apply clarsimp
done

lemma log2rec_point_correct: 
      "\<forall>x y. x > 0 \<longrightarrow> 2 ^ x \<le> y \<longrightarrow> y < 2 ^ Suc x \<longrightarrow>log2rec x y = x - Suc 0"
 apply (rule allI)
 apply (induct_tac x)
  apply simp
 apply clarsimp
done
   

 lemma log2point_correct: "\<forall>x. log2 (2^x) = x"
 apply (rule allI)
 apply (simp add: log2_def)
 apply (case_tac "x = 0")
  apply simp
 apply simp
  apply (subgoal_tac "\<forall>(a::nat) b. a>b \<longrightarrow> (2::nat)^a > 2^b")
   prefer 2
   apply (thin_tac "0 < x")
   apply clarsimp
  apply (erule_tac  x = "x" in allE)
  apply (erule_tac  x = "0" in allE)
  apply simp
 apply (insert log2rec_cut1)
 apply (erule_tac x = "2 ^ x" in allE)
 apply (erule_tac x = "x" in allE)
 apply (erule_tac x = "x" in allE)
 apply simp
 apply (subgoal_tac "\<forall>a. 2^a \<ge> a")
  prefer 2
  apply clarsimp
  apply (induct_tac a)
   apply simp
  apply (case_tac n)
   apply simp
  apply (case_tac "nat")
   apply simp
  apply simp
 apply (erule_tac x = "x" in allE)
 apply simp
 apply (subgoal_tac "log2rec (2 ^ x) (2 ^ x) = log2rec x (2 ^ x)")
  prefer 2
  apply simp
 apply (rotate_tac -1, erule ssubst)
 apply (case_tac x)
  apply simp
 apply simp
done



lemma log2_correct_up: "\<forall>x. 2 ^ (log2 x) \<ge> x"
 apply (rule allI)
 apply (induct_tac x)
  apply simp
 apply (subgoal_tac "\<forall>a. \<exists>b r. a>0 \<longrightarrow> a = (2::nat)^b + r \<and> r<2^b")
  prefer 2
  apply (thin_tac "n \<le> 2 ^ log2 n")
  apply (rule allI)
  apply (induct_tac a)
   apply simp
  apply (case_tac na)
   apply simp
   apply (rule_tac x = "0" in exI)
   apply (rule_tac x = "0" in exI)
   apply simp
  apply clarsimp
  apply (case_tac "r = 2 ^ b - 1")
   apply simp
   apply (rule_tac x = "b+1" in exI)
   apply (rule_tac x = "0" in exI)
   apply simp
  apply simp
  apply (rule_tac x = "b" in exI)
  apply (rule_tac x = "r+1" in exI)
  apply simp
 apply (erule_tac x = "n" in allE)
 apply (erule exE)+
 apply (case_tac "n = 0")
  apply simp
 apply simp
 apply (case_tac "r = 2^b - 1")
  apply simp
  apply (insert log2point_correct)
  apply (erule_tac x = "b + 1" in allE)
  apply simp
  apply (subgoal_tac "(2::nat) ^ b + 2 ^ b = 2 * 2^b")
   prefer 2
   apply simp
  apply (rotate_tac -1, erule ssubst)
  apply simp
 apply (thin_tac "\<forall>x. log2 (2 ^ x) = x")
 apply (simp add: log2_def)
 apply (rule conjI)  
  apply clarsimp
  apply (subgoal_tac "\<forall>a. 2^a \<ge> a")
   prefer 2
   apply clarsimp
   apply (induct_tac a)
    apply simp
   apply (case_tac n)
    apply simp
   apply (case_tac "nat")
    apply simp
   apply simp
  apply (erule_tac x = "Suc (2 ^ b + r)" in allE)
  apply simp
 apply clarsimp
 apply (case_tac "b = 0")
  apply simp
 apply (insert log2rec_point_correct)
 apply (erule_tac x = "b" in allE)
 apply (erule_tac x = "Suc (2 ^ b + r)" in allE)
 apply simp
 apply (subgoal_tac "Suc r < 2 ^ b")
  prefer 2
  apply arith
 apply simp
 apply (insert log2rec_cut2)
 apply (erule_tac x = "2 ^ b + r" in allE)
 apply (erule_tac x = "Suc (2 ^ b + r)" in allE)
 apply (erule_tac x = "b + 1" in allE)
 apply simp
 apply (subgoal_tac "\<forall>a. 2^a \<ge> Suc a")
  prefer 2
  apply clarsimp
  apply (induct_tac a)
   apply simp
  apply (case_tac n)
   apply simp
  apply (case_tac "nat")
   apply simp
  apply simp
 apply (erule_tac x = "b" in allE)
 apply simp
done 


lemma log2_correct_down:"\<forall>x. x>1 \<longrightarrow> 2 ^ ((log2 x) - Suc 0) < x"
 apply (rule allI)
 apply (induct_tac x)
  apply (simp add: log2_def)
 apply clarsimp
 apply (case_tac "n = 1")
  apply (simp add: log2_def)
 apply clarsimp
 apply (subgoal_tac "\<forall>a. \<exists>b r. a>0 \<longrightarrow> a = (2::nat)^b + r \<and> r<2^b")
  prefer 2
  apply (thin_tac "2 ^ (log2 n - Suc 0) < n")
  apply (thin_tac "n \<noteq> Suc 0")
  apply (rule allI)
  apply (induct_tac a)
   apply simp
  apply (case_tac na)
   apply simp
   apply (rule_tac x = "0" in exI)
   apply (rule_tac x = "0" in exI)
   apply simp
  apply clarsimp
  apply (case_tac "r = 2 ^ b - 1")
   apply simp
   apply (rule_tac x = "b+1" in exI)
   apply (rule_tac x = "0" in exI)
   apply simp
  apply simp
  apply (rule_tac x = "b" in exI)
  apply (rule_tac x = "r+1" in exI)
  apply simp

 apply (erule_tac x = "n" in allE)
 apply (erule exE)+
 apply simp
 apply (erule conjE)
 apply (case_tac "r = 2^b - 1")
  apply simp
  apply (subgoal_tac "(2::nat)^b + 2^b = 2 ^ Suc b")
   prefer 2
   apply simp
  apply (rotate_tac -1, erule ssubst)
  apply (insert log2point_correct)
  apply (erule_tac x = "Suc b" in allE)
  apply simp
 apply (thin_tac "\<forall>x. log2 (2 ^ x) = x")
 apply (simp add: log2_def)
 apply clarsimp
 apply (insert log2rec_cut3)
 apply (erule_tac x = "b" in allE)
 apply (erule_tac x = "2^b" in allE)
 apply (erule_tac x = "Suc (2 ^ b + r)" in allE)
 apply simp
 apply (case_tac "b = 0")
  apply simp
 apply simp
 apply (subgoal_tac "Suc r < 2 ^ b")
  prefer 2
  apply arith
 apply simp
 apply (erule conjE)
 apply (insert log2rec_cut2)
 apply (erule_tac x = "2 ^ b + r" in allE)
 apply (erule_tac x = "Suc (2 ^ b + r)" in allE)
 apply (erule_tac x = "b + 1" in allE)
 apply simp
 apply (subgoal_tac "\<forall>a. 2^a \<ge> Suc a")
  prefer 2
  apply clarsimp
  apply (induct_tac a)
   apply simp
  apply (case_tac n)
   apply simp
  apply (case_tac "nat")
   apply simp
  apply simp
 apply (erule_tac x = "b" in allE)
 apply simp
done



lemma log2correct: "\<forall>n x. x>2^n \<longrightarrow> x\<le>2^Suc n \<longrightarrow> log2 x = Suc n"
 apply clarsimp
 apply (subgoal_tac "\<exists>r. x = 2^n + r \<and> r \<le> 2^n")
  prefer 2
  apply (rule_tac x = "x - 2^n" in exI)
  apply simp
 apply (erule exE)
 apply (erule conjE)
 apply clarsimp 
 apply (simp add: log2_def)
 apply (insert log2rec_cut2)
 apply (erule_tac x = "(2^n) + r" in allE)
 apply (erule_tac x = "(2^n) + r" in allE)
 apply (erule_tac x = "n+1" in allE)
 apply simp
 apply (subgoal_tac "\<forall>a. a<2^a")    
  prefer 2
  apply (rule allI)
  apply (induct_tac a)
   apply clarsimp
  apply clarsimp
 apply (erule_tac x = "n" in allE)
 apply simp
done


lemmas max_positive = Lattices.linorder_class.max.strict_coboundedI1 (*legacy *)

lemmas nat_max_commute = Lattices.linorder_class.max.commute (* legacy *)

lemma min_self[simp]: "min a a = a" unfolding min_def by simp (* legacy ? *)

(* allows ML code generation for max with nat arguments *)
declare Orderings.ord_class.max_def [code]
(* bu did this - equiv ?
lemma [code]:"max (z::nat) y = (if z \<le> y then y else z)"
apply (simp add: max_def)
done
*)


subsection {* addition and difference *}

lemma diff_add_eq_impl_eq: "\<lbrakk> a < c ; b < c ; c = c - a + b \<rbrakk> \<Longrightarrow> a = (b:: nat)" by arith (* legacy *)

lemma diff_Suc_neq: "\<lbrakk> a < c ; b < c ;a \<noteq> b\<rbrakk> \<Longrightarrow> c - Suc a \<noteq> c - Suc b" by arith (* legacy *)

lemma le_imp_diff_le[rule_format]: "(i::nat) \<le> x \<longrightarrow> i - a \<le> x" by arith (* legacy *)

lemma nat_int_plus[rule_format]: "0 \<le> i \<longrightarrow> nat (int n + i) = n + nat i" by arith (* legacy *)

lemma nat_int_minus[rule_format]: "i < 0 \<longrightarrow> nat (int n + i) = n - nat (- i)" by arith (* legacy *)

lemma nat_diff_less_mono[rule_format]: "(a::nat) < b \<longrightarrow> a - x < b" by arith (* legacy *)

lemma suc_sub_suc [rule_format] : "b < a \<longrightarrow> Suc (a - Suc b) = a - b" by arith (* legacy *)

subsection {* multiplication *}

lemma multiplier_less_product: "\<lbrakk>a * b = n; n \<noteq> 0\<rbrakk> \<Longrightarrow> a \<le> (n::nat)" by auto (* legacy *)

lemma nat_is_odd_or_even: "\<exists> q. (n::nat) = q * 2 \<or> n = q * 2 + 1" by arith (* legacy *)


end
