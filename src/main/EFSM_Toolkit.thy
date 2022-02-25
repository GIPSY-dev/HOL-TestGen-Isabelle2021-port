(*****************************************************************************
 * HOL-TestGen --- theorem-prover based test case generation
 *                 http://www.brucker.ch/projects/hol-testgen/
 *                                                                            
 * TestRefinements.thy --- for sequence testing.
 * This file is part of HOL-TestGen.
 *
 * Copyright (c) 2005-2007, ETH Zurich, Switzerland
 *               2009 B. Wolff, Univ. Paris-Sud, France 
 *               2009 Achim D. Brucker, Germany
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
(* $Id:$ *)

chapter {* Test-Refinements (IOCO and Friends) *}

theory EFSM_Toolkit imports Monads Automata
begin 


definition impl :: "['\<sigma>\<Rightarrow>'\<iota>\<Rightarrow>bool, '\<iota> \<Rightarrow> ('o,'\<sigma>)MON\<^sub>S\<^sub>B] \<Rightarrow> '\<iota> \<Rightarrow> ('o,'\<sigma>)MON\<^sub>S\<^sub>E"
where     "impl pre post \<iota> = (\<lambda> \<sigma>. if pre \<sigma> \<iota>
                                     then Some(SOME(out,\<sigma>'). (out,\<sigma>') \<in> post \<iota> \<sigma>)
                                     else undefined)"

definition strong_impl :: "['\<sigma>\<Rightarrow>'\<iota>\<Rightarrow>bool, '\<iota>\<Rightarrow>('o,'\<sigma>)MON\<^sub>S\<^sub>B] \<Rightarrow> '\<iota>\<Rightarrow>('o, '\<sigma>)MON\<^sub>S\<^sub>E"
where     "strong_impl pre post \<iota> =
                               (\<lambda> \<sigma>. if pre \<sigma> \<iota>
                                     then Some(SOME(out,\<sigma>'). (out,\<sigma>') \<in> post \<iota> \<sigma>)
                                     else None)"

definition strong_impl' :: "['\<sigma>\<Rightarrow>'\<iota>\<Rightarrow>bool, '\<iota>\<Rightarrow>('o,'\<sigma>)MON\<^sub>S\<^sub>B] \<Rightarrow> '\<iota>\<Rightarrow>('o, '\<sigma>)MON\<^sub>S\<^sub>E"
where     "strong_impl' pre post \<iota> =
                               (\<lambda> \<sigma>. if pre \<sigma> \<iota>
                                     then Some(SOME(out,\<sigma>'). (out,\<sigma>') \<in> post \<iota> \<sigma>)
                                     else 
                                       (if post \<iota> \<sigma> \<noteq> {}
                                        then Some(SOME(out,\<sigma>'). (out,\<sigma>') \<in> post \<iota> \<sigma>)
                                        else None))"


definition implementable :: "['\<sigma> \<Rightarrow> '\<iota> \<Rightarrow> bool,'\<iota> \<Rightarrow> ('o,'\<sigma>)MON\<^sub>S\<^sub>B] \<Rightarrow> bool"
where     "implementable pre post =(\<forall> \<sigma> \<iota>. pre \<sigma> \<iota> \<longrightarrow>(\<exists> out \<sigma>'. (out,\<sigma>') \<in> post \<iota> \<sigma> ))"

definition is_strong_impl :: "['\<sigma> \<Rightarrow> '\<iota> \<Rightarrow> bool,
                              '\<iota> \<Rightarrow> ('o,'\<sigma>)MON\<^sub>S\<^sub>B,
                              '\<iota> \<Rightarrow> ('o, '\<sigma>)MON\<^sub>S\<^sub>E] \<Rightarrow> bool"
where     "is_strong_impl pre post ioprog =
                             (\<forall> \<iota> \<sigma>. (\<not>pre \<sigma> \<iota> \<and> ioprog \<iota> \<sigma> = None) \<or>
                                     (pre \<sigma> \<iota> \<and> (\<exists> x. ioprog \<iota> \<sigma> = Some x)))"

lemma is_strong_impl :
      "is_strong_impl pre post (strong_impl pre post)"
by(simp add: is_strong_impl_def strong_impl_def)


text{* This following characterization of implementable
specifications has actually a quite complicated form due to the fact
that post expects its arguments in curried form - should
be improved \ldots *}
lemma implementable_charn:
     "\<lbrakk>implementable pre post; pre \<sigma> \<iota> \<rbrakk> \<Longrightarrow>
      (the(strong_impl pre post \<iota> \<sigma>)) \<in> post \<iota> \<sigma>"
apply(auto simp: implementable_def strong_impl_def)
apply(erule_tac x=\<sigma> in allE)
apply(erule_tac x=\<iota> in allE)
apply(simp add: Eps_case_prod)
apply(rule someI_ex, auto)
done
 

locale efsm_det =
   fixes   pre  :: "'\<sigma> \<Rightarrow> '\<iota> \<Rightarrow> bool"
   fixes   post :: "'\<iota> \<Rightarrow> '\<sigma> \<Rightarrow> ('o \<times> '\<sigma>) set"
   fixes   efsm :: "'\<iota> \<Rightarrow> '\<sigma> \<Rightarrow> ('o \<times> '\<sigma>) option"
   fixes   in_ev:: "'\<iota>"
   fixes   out_ev:: "'\<sigma> \<Rightarrow> 'o"
   fixes   upd  :: "'\<sigma> \<Rightarrow> '\<sigma>"
   fixes   E    :: "'\<sigma> \<Rightarrow> bool"
   assumes SPEC:   "efsm \<equiv> (strong_impl pre post)"
   assumes pre_red  :   "\<And> \<sigma>. pre \<sigma> in_ev = E \<sigma>"
   assumes post_red :   "\<And> \<sigma>. pre \<sigma> in_ev \<Longrightarrow> (SOME(res,\<sigma>'). (res,\<sigma>') \<in> post in_ev \<sigma>) = (out_ev \<sigma>,upd \<sigma>)"
begin

lemma impl_def:"efsm in_ev = (\<lambda>\<sigma>. if E \<sigma> then Some(out_ev \<sigma>, upd \<sigma>) else None)"
      by(rule ext, auto simp: SPEC strong_impl_def pre_red post_red)

lemma exec_succes:
     "(efsm in_ev \<sigma> = Some(b,\<sigma>'))  = (E \<sigma> \<and> (b=out_ev \<sigma>) \<and> \<sigma>'= upd \<sigma>)"
      by(auto simp: impl_def  split:if_split_asm)


lemma exec_failure:
     "(efsm in_ev \<sigma> = None) = (\<not> E \<sigma>)"
      by(auto simp: impl_def  split:if_split_asm)



lemma exec_mbindFSave_If[simp]:
"(\<sigma> \<Turnstile> (s \<leftarrow> mbind\<^sub>F\<^sub>a\<^sub>i\<^sub>l\<^sub>S\<^sub>a\<^sub>v\<^sub>e (in_ev # S) efsm; return (P s))) = 
    (if E \<sigma>
     then ((upd \<sigma>) \<Turnstile> (s \<leftarrow> mbind\<^sub>F\<^sub>a\<^sub>i\<^sub>l\<^sub>S\<^sub>a\<^sub>v\<^sub>e S efsm; return (P (out_ev \<sigma> # s))))
     else (\<sigma> \<Turnstile> (return (P []))))"
by(auto simp:  exec_mbindFSave impl_def)

lemma exec_mbindFSave_E:
assumes A:"(\<sigma> \<Turnstile> (s \<leftarrow> mbind\<^sub>F\<^sub>a\<^sub>i\<^sub>l\<^sub>S\<^sub>a\<^sub>v\<^sub>e (in_ev # S) efsm; return (P s)))"
   and  B:"E \<sigma> \<Longrightarrow>  ((upd \<sigma>) \<Turnstile> (s\<leftarrow>mbind\<^sub>F\<^sub>a\<^sub>i\<^sub>l\<^sub>S\<^sub>a\<^sub>v\<^sub>e S efsm;return(P(out_ev \<sigma> # s)))) \<Longrightarrow> Q"
   and  C:"\<not> E \<sigma> \<Longrightarrow>\<sigma> \<Turnstile> (return (P [])) \<Longrightarrow> Q"
shows "Q"
apply(insert A, subst (asm) exec_mbindFSave_If, case_tac "E \<sigma>", simp_all only: if_True if_False)
by(auto elim: B C)



lemma exec_mbindFStop[simp]:
"(\<sigma> \<Turnstile> (s \<leftarrow> mbind\<^sub>F\<^sub>a\<^sub>i\<^sub>l\<^sub>S\<^sub>t\<^sub>o\<^sub>p (in_ev#S) efsm; return (P s))) = 
    (E \<sigma> \<and> ((upd \<sigma>) \<Turnstile> (s \<leftarrow> mbind\<^sub>F\<^sub>a\<^sub>i\<^sub>l\<^sub>S\<^sub>t\<^sub>o\<^sub>p S efsm; return (P (out_ev \<sigma> # s)))))"
apply(rule iffI)
apply(erule Monads.exec_mbindFStop_E,simp add: exec_succes,auto)  
apply(subst exec_bind_SE_success[OF exec_succes[THEN iffD2]], auto)
done


lemma exec_mbindFStop_E:
assumes A:"(\<sigma> \<Turnstile> (s \<leftarrow> mbind\<^sub>F\<^sub>a\<^sub>i\<^sub>l\<^sub>S\<^sub>t\<^sub>o\<^sub>p (in_ev # S) efsm; return (P s)))"
   and  B:"E \<sigma> \<Longrightarrow>  ((upd \<sigma>) \<Turnstile> (s\<leftarrow>mbind\<^sub>F\<^sub>a\<^sub>i\<^sub>l\<^sub>S\<^sub>t\<^sub>o\<^sub>p S efsm;return(P(out_ev \<sigma> # s)))) \<Longrightarrow> Q"
shows "Q"
by(insert A, rule B, simp_all del: mbind'_bind)

(*
lemmas impl_1'' = exec_failure
lemmas impl_1' = exec_succes
*)

end

end
