(*****************************************************************************
 * HOL-TestGen --- theorem-prover based test case generation
 *                 http://www.brucker.ch/projects/hol-testgen/
 *
 * UPF
 * This file is part of HOL-TestGen.
 *
 * Copyright (c) 2010-2012 ETH Zurich, Switzerland
 *               2010-2012 Achim D. Brucker, Germany
 *               2010-2012 Université Paris-Sud, France
 *
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are
 * met:
 *
 *     * Redistributions of source code must retain the above copyright
 *       notice, this list of conditions and the following disclaimer.
 *
 *     * Redistributions in binary form must reproduce the above
 *       copyright notice, this list of conditions and the following
 *       disclaimer in the documentation and/or other materials provided
 *       with the distribution.
 *
 *     * Neither the name of the copyright holders nor the names of its
 *       contributors may be used to endorse or promote products derived
 *       from this software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
 * "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
 * LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
 * A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
 * OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
 * SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
 * LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
 * DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
 * THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
 * (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
 * OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 ******************************************************************************)
(* $Id: ServiceTest.thy 13165 2017-08-19 07:28:10Z brucker $ *)

theory ServiceTest
imports 
  "$AFP/UPF/ServiceExample"
begin


fun sndI where
   "sndI (x#y#xs) = y"
  |"sndI (x#[]) = x"


fun patients :: "Operation list  \<Rightarrow> patient set" where
   "patients (x#xs) = insert (patientOfOp x) (patients xs) "
  |"patients [] = {}"


fun roles :: "Operation list  \<Rightarrow> role set" where
   "roles (x#xs) = insert (roleOfOp x) (roles xs) "
  |"roles [] = {}"

fun patientOfLR :: "Operation \<Rightarrow> patient set" where 
   "patientOfLR (addLR u r p li us) = set [p]"
  |"patientOfLR x = set []"


fun userOfLR :: "Operation \<Rightarrow> user set" where 
   "userOfLR (addLR u r p li us) = us"
  |"userOfLR x = set []"



definition "correct_role x = ((userOfOp x = alice \<and> roleOfOp x = Nurse) \<or>
                              (userOfOp x = bob \<and> roleOfOp x = ClinicalPractitioner) \<or>
                              (userOfOp x = charlie \<and> roleOfOp x = Clerical))"

fun correct_roles where
   "correct_roles (x#xs) = (correct_role x \<and> correct_roles xs)"
  |"correct_roles [] = True"

declare correct_role_def [simp add]
definition John where "John=(4::patient)"

lemma list_set: "{b} =  (set [b])" by simp

text{*

This theory contains an unordered list of auxiliary lemmas for test
case generation. Needs definitely a cleanup! *}

lemmas p_iffs = policy2MON_def valid_SE_def bind_SE_def unit_SE_def

 
fun notEntry :: "Operation \<Rightarrow> bool" where
   "notEntry (appendEntry u r p ei e) = False"
  |"notEntry(editEntry u r p ei e) = False"
  |"notEntry x = True"

fun noEntries where 
   "noEntries (x#xs) = (notEntry x \<and> noEntries xs)"
  |"noEntries [] = True"


lemma allow_simp[simp]: "(allow () = X) = (X = (allow ()))" by auto

lemma deny_simp[simp]: "(deny () = X) = (X = (deny ()))" by auto


lemma mon_prog: "\<lbrakk>P x s \<noteq> None \<and> (P x s) = Some (a,b)\<rbrakk> \<Longrightarrow> 
                   (s \<Turnstile> (os \<leftarrow> mbind (x#xs) P; (return (os = (r#rs)))))
                 = ((a = r) \<and> (b \<Turnstile> (os \<leftarrow> mbind xs P; (return (os = rs)))))"  
apply (simp_all add: p_iffs)
apply (simp split: option.splits)
done

lemma RBACnMT:  "\<forall>x. RBACPolicy (x) \<noteq> None " by (simp add: RBACPolicy_def) 

lemma LRnMT: "LR_Policy (x,y) \<noteq> None " by (simp add:  PolSimps)


lemma SEnMT: "\<forall> x y. SEPolicy (x,y) \<noteq> None "
by (simp add: PolSimps SEPolicy_def split: Psplits)

lemma domnMT: "(\<forall> x. p x \<noteq> None) = (dom p = UNIV)"  by auto


lemma orDnMT: "\<lbrakk>a x \<noteq> None;b y \<noteq> None\<rbrakk> \<Longrightarrow>
                ( (a \<Otimes>\<^sub>\<or>\<^sub>D b)) (x,y) \<noteq> None"
apply (simp add: prod_orD_def)
apply (simp split: option.splits decision.splits)
apply auto
done


declare not_None_eq [simp del]



lemma orDnMT2: "\<lbrakk>\<forall> x. a x \<noteq> None; \<forall> x. b x \<noteq> None\<rbrakk> \<Longrightarrow>
                 \<forall> z. ( (a \<Otimes>\<^sub>\<or>\<^sub>D b)) z \<noteq> None"
by (auto simp: orDnMT)

lemma domnMTs: "(dom p = UNIV) = (\<forall> x. p x \<noteq> None)" by auto


lemma orDnMT3: "\<lbrakk>dom a = UNIV; dom b = UNIV\<rbrakk> \<Longrightarrow>
                dom (a \<Otimes>\<^sub>\<or>\<^sub>D b) = UNIV"
by (simp add: domnMTs orDnMT2)

lemma domU: "dom a = UNIV \<Longrightarrow> dom (f o_f a) = UNIV" 
apply (simp add: policy_range_comp_def)
apply (auto,simp split: option.splits decision.splits)
apply auto
done


lemma domU2: "dom a = UNIV \<Longrightarrow> dom (a o f) = UNIV"
apply auto
apply (auto simp: not_None_eq)
done



lemma orDU: "\<lbrakk>dom a = UNIV; dom b = UNIV\<rbrakk> \<Longrightarrow> dom (c1 o_f (a \<Otimes>\<^sub>\<or>\<^sub>D b) o c2) = UNIV"
apply (rule domU2)
apply (rule domU)
apply (rule orDnMT3)
apply simp_all
done



lemma PUniv: "dom SE_LR_RBAC_Policy = UNIV"
apply (simp add: SE_LR_RBAC_Policy_def)
apply (rule orDU)
apply (metis domnMTs RBACnMT)
apply (simp add: SE_LR_Policy_def SE_LR_FUN_Policy_def)
apply (rule orDU)
apply (simp add: PolSimps)
apply (simp add: dom_def PolSimps split: option.splits decision.splits)
apply (rule orDU)
apply (simp add: domnMTs, rule SEnMT)
apply (simp add: domnMTs) 
apply (rule allI)+
apply (rule LRnMT)
done


lemma ST_A_Univ: "dom ST_Allow = UNIV"
apply (simp add: PolSimps)
apply auto
apply (simp split: Psplits)
apply (case_tac a,simp_all)
apply (simp_all split: Psplits)
done

lemma ST_D_Univ: "dom ST_Deny = UNIV" by (auto simp: PolSimps)

lemma AD_dom_split: "dom (X \<triangleright> Allow) \<union> dom (X \<triangleright> Deny) = dom X"
apply (simp add: PolSimps not_None_eq dom_def) 
apply auto
apply (case_tac y)
by auto


lemma domorA: "\<lbrakk>\<forall> x. a x \<noteq> None; \<forall> y. b y \<noteq> None\<rbrakk> \<Longrightarrow> \<forall> z. (b \<Otimes>\<^sub>\<or>\<^sub>A a) z \<noteq> None"
apply (simp add: prod_orA_def)
apply (rule allI)+
apply (simp split: decision.splits option.splits)
done


lemma domorAU: "\<lbrakk>dom a = UNIV; dom b = UNIV\<rbrakk> \<Longrightarrow> dom (b \<Otimes>\<^sub>\<or>\<^sub>A a) = UNIV"
apply (simp add: domnMTs)
apply (simp add: domorA)
done

lemma domorAU2: "\<lbrakk>dom a = UNIV; dom b = UNIV\<rbrakk> \<Longrightarrow> dom ((b \<Otimes>\<^sub>\<or>\<^sub>A a) o f) = UNIV"
apply (simp add: domnMTs)
apply (simp add: domorA)
done

(* 
lemma domorAIU: "\<lbrakk>dom a = UNIV; dom b = UNIV\<rbrakk> \<Longrightarrow> dom (b \<Otimes>\<^sub>\<or>\<^sub>A\<^sub>I a) = UNIV"
apply (simp add: prod_orA_id_def)
apply (rule domorAU2)
apply simp_all
done
*)

lemma domplus: "\<lbrakk>\<forall> x. a x \<noteq> None; \<forall> y. b y \<noteq> None\<rbrakk> \<Longrightarrow> \<forall> z. (b \<Oplus> a) z \<noteq> None"
apply (simp add: map_add_def)
apply (rule allI)+
apply (simp split: decision.splits option.splits)
done


lemma domorplusU: "\<lbrakk>dom a = UNIV; dom b = UNIV\<rbrakk> \<Longrightarrow> dom (b \<Oplus> a) = UNIV"
apply (simp only: domnMTs)
apply (simp add: domplus)
done

lemma dom_split: 
     "\<lbrakk>dom x1 \<union> dom x2 = dom X;dom X = UNIV\<rbrakk> \<Longrightarrow> dom (x1 \<Oplus> x2) = UNIV" by auto

(*
lemma dom_orAI1: "\<forall> a. y a \<noteq> None \<Longrightarrow>  \<forall> z. (x z \<noteq> None \<longrightarrow> (x \<Otimes>\<^sub>\<or>\<^sub>A\<^sub>I y) z \<noteq> None)"
apply (simp_all add: PolSimps)
apply (simp_all split:  decision.splits option.splits)
done
*)


text{* Test for completeness of the policy. *}

fun users :: "Operation list  \<Rightarrow> user set" where
   "users (x#xs) = insert (userOfOp x) (users xs) "
  |"users [] = {}"



lemma mbind1:
   "(\<sigma> \<Turnstile> (o1 \<leftarrow> Mon is; return (o1 = X)))
 =  (\<sigma> \<Turnstile> (os \<leftarrow> mbind [is] Mon ; return (os = [X])))"
apply (simp add: valid_SE_def unit_SE_def bind_SE_def)
apply (simp split: option.splits)
apply (simp add: valid_SE_def unit_SE_def bind_SE_def)
done

lemma option_split1: 
  "P (option_case f1 f2 x) = ((x = None \<longrightarrow> P f1) \<and> (\<forall>a. x = Some a \<longrightarrow> P (f2 a)))"
by (simp split: option.splits)


lemma option_split2: "P (option_case f1 f2 x) = (\<not> (x = None \<and> \<not> P f1 \<or> (\<exists>a. x = Some a \<and> \<not> P (f2 a))))"
by (simp split: option.splits)


lemma dsplits1: "P (decision_case f1 f2 x) =
((\<forall>\<alpha>. x = allow \<alpha> \<longrightarrow> P (f1 \<alpha>)) \<and> (\<forall>\<alpha>. x = deny \<alpha> \<longrightarrow> P (f2 \<alpha>)))"
by (simp split: decision.splits)


lemma dsplits2: "P (decision_case f1 f2 x) =
(\<not> ((\<exists>\<alpha>. x = allow \<alpha> \<and> \<not> P (f1 \<alpha>)) \<or> (\<exists>\<alpha>. x = deny \<alpha> \<and> \<not> P (f2 \<alpha>))))"
by (simp split: decision.splits)


definition rolesEx 
where "rolesEx = {(alice,Nurse), (alice,Clerical),(bob,Clerical),(charlie,ClinicalPractitioner)}"


lemma F3[simp]: "alice \<noteq> charlie"
by (simp add: PolSimps)

lemma F4[simp]: "alice \<noteq> bob"
by (simp add: PolSimps)

lemma F41[simp]: "bob \<noteq> alice"
by (simp add: PolSimps)

lemma F42[simp]: "bob \<noteq> charlie"
by (simp add: PolSimps)

lemma F43[simp]: "charlie \<noteq> bob"
by (simp add: PolSimps)

lemma F44[simp]: "charlie \<noteq> alice"
by (simp add: PolSimps)


lemma valid_propoagate_1[simp]: (*replace *)
"(\<sigma> \<Turnstile> (return P)) = P"
by(simp_all add: valid_SE_def unit_SE_def split: prod.splits)


lemma valid_failure'[simp]:
"A \<sigma> = None \<Longrightarrow> 
 \<not>(\<sigma> \<Turnstile> ((s \<leftarrow> A ; M s)))"
by(simp add: valid_SE_def unit_SE_def bind_SE_def)


lemma valid_successElem[simp]: (* atomic boolean Monad "Query Functions" *) 
"M \<sigma> = Some(f \<sigma>,\<sigma>) \<Longrightarrow> (\<sigma> \<Turnstile> M) = f \<sigma>"
by(simp add: valid_SE_def unit_SE_def bind_SE_def )


lemma valid_success'[simp]: 
"A \<sigma> = Some(b,\<sigma>') \<Longrightarrow> (\<sigma> \<Turnstile> ((s \<leftarrow> A ; M s))) = (\<sigma>' \<Turnstile> (M b))"
by(simp add: valid_SE_def unit_SE_def bind_SE_def )


lemma valid_failure''[simp]: 
"ioprog a \<sigma> = None \<Longrightarrow> 
   (\<sigma> \<Turnstile> (s \<leftarrow> mbind (a#S) ioprog ; M s)) = 
   (\<sigma> \<Turnstile> (M []))"
by(simp add: valid_SE_def unit_SE_def bind_SE_def)


lemma valid_success''[simp]: 
"ioprog a \<sigma> = Some(b,\<sigma>') \<Longrightarrow> 
   (\<sigma>  \<Turnstile> (s \<leftarrow> mbind (a#S) ioprog ; M s)) = 
   (\<sigma>' \<Turnstile> (s \<leftarrow> mbind S ioprog ; M (b#s)))"
apply(simp add: valid_SE_def unit_SE_def bind_SE_def )
apply(cases "mbind S ioprog \<sigma>'", simp_all)
apply auto
done


lemma valid_propagate_2''[simp]:
"\<sigma> \<Turnstile> ((s \<leftarrow> A ; M s)) \<Longrightarrow> 
 \<exists> v \<sigma>'. A \<sigma> = Some(v,\<sigma>') \<and> \<sigma>' \<Turnstile> (M v)"
apply(auto simp: valid_SE_def unit_SE_def bind_SE_def)
apply(cases "A \<sigma>", simp_all)
apply(simp add: Product_Type.prod_case_unfold)
apply(drule_tac x="A \<sigma>" and f=the in arg_cong, simp add: not_None_eq)
apply(rule_tac x="fst aa" in exI)
apply(rule_tac x="snd aa" in exI, auto)
done



lemma valid_propoagate_3[simp]: "(\<sigma>0 \<Turnstile> (\<lambda>\<sigma>. Some (f \<sigma>, \<sigma>))) = (f \<sigma>0)"
by(simp add: valid_SE_def )


lemma valid_propoagate_3'[simp]: "\<not>(\<sigma>0 \<Turnstile> (\<lambda>\<sigma>. None))"
by(simp add: valid_SE_def )


lemma prog: "\<lbrakk>(s \<Turnstile> (o1 \<leftarrow> Mon x; return o1 = y1));
        (s \<Turnstile> (o1 \<leftarrow> mbind (x#xs) Mon; return o1 = (y2#ys)))\<rbrakk> \<Longrightarrow>
 y1 = y2" 
apply (auto simp: valid_SE_def unit_SE_def bind_SE_def)
apply (simp split: option.splits )
apply (case_tac "ab")
apply simp_all
apply (case_tac "ac")
apply simp_all
apply (simp split: option.splits )
apply (case_tac "af")
apply simp_all
done

lemma prog2: "\<lbrakk>(s \<Turnstile> (o1 \<leftarrow> Mon x; return o1 = y1)); y1 \<noteq> y2\<rbrakk> \<Longrightarrow> 
      \<not>  (s \<Turnstile> (o1 \<leftarrow> mbind (x#xs) Mon; return o1 = (y2#ys)))" 
by (metis prog)



lemma G3: "\<lbrakk> (\<sigma>0 \<Turnstile> (o1 \<leftarrow> PolMon Y; return o1 = X))\<rbrakk> \<Longrightarrow>
 (\<exists> Z. X = allow Z) \<or> (\<exists> Z. X = deny Z) "
apply (case_tac X)
apply simp_all
done


lemma rsimp[simp]: "(X127X127 = Clerical \<and> X127X127 = Nurse) = False"
by auto

lemmas p_simps = PolSimps userHasAccess_def PolMon_def mon_prog 
                  ran_def  John_def
                  


end
