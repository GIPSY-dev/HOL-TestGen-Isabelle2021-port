(**
 * Copyright (c) 2003-2006 Dirk Leinenbach.
 * Some rights reserved, Saarland University.
 *
 * This work is licensed under the German-Jurisdiction Creative Commons
 * Attribution Non-commercial Share Alike 2.0 License.
 * See the file LIZENZ for a full copy of the license.
**)
(* $Id: MorePower.thy 22839 2008-03-26 17:29:26Z MarkHillebrand $ *)
chapter {* Additional theory about power *}

theory MorePower imports MoreNat begin

lemma nat_power_Suc[rule_format]: "0 < b \<longrightarrow> (a::nat)^b= a * a ^(b - 1)"
apply (induct_tac b)
 apply simp
apply simp
done

lemma int_power_Suc[rule_format]: "0 < b \<longrightarrow> (a::int)^b= a * a ^(b - 1)"
apply (induct_tac b)
 apply simp
apply simp
done

lemma power_div_add_eq: "((a::nat) div b^n) div b^m = a div b^(n+m)"
apply (subst power_add)
apply (simp add: div_mult2_eq)
done

lemma nat_power_mod_cancel[rule_format]: "m \<le> n \<longrightarrow> (a::nat)^n mod a^m = 0"
apply clarsimp
apply (subgoal_tac "\<exists> x. n= m + x")
 apply clarsimp
 apply (simp add: power_add)
apply arith
done

lemma nat_power_div[rule_format]: "0 < a \<longrightarrow> m \<le> n \<longrightarrow> (a::nat)^n div a^m = a^(n-m)"
apply clarsimp
apply (subgoal_tac "\<exists> x. n= m + x")
 apply clarsimp
 apply (simp add: power_add)
apply arith
done

lemma power_le: "(0::nat) < i \<Longrightarrow> (a::nat) \<le> a ^ i"
 by (induct i) auto

lemma power_div_base [rule_format] : "0 < b \<longrightarrow> 0 < n \<longrightarrow> (a::nat) * b ^ n div b = a * b ^ (n - 1)"
apply clarify
apply (cut_tac a = "a" and b = "b ^ n" and c = "b" in div_mult1_eq)
apply (erule ssubst)+
apply (subgoal_tac "b ^ n = b ^ ((n - 1) + 1)")
  prefer 2
  apply simp
apply (erule ssubst)
apply (simp only: power_add)
apply simp
done

lemma power_div_power [rule_format] : "0 < b \<longrightarrow> n \<ge> m \<longrightarrow> (a::nat) * b ^ n div b ^ m = a * b ^ (n - m)"
apply clarify
apply (cut_tac a = "a" and b = "b ^ n" and c = "b ^ m" in div_mult1_eq)
apply (erule ssubst)+
apply (subgoal_tac "b ^ n = b ^ ((n - m) + m)")
  prefer 2
  apply simp
apply (erule ssubst)
apply (simp only: power_add)
apply simp
done

end
