(*****************************************************************************
* HOL-TestGen --- theorem-prover based test case generation
*                 http://www.brucker.ch/projects/hol-testgen/
*                                                                            
* STATUS : Half-baked.
* TODO : - check red-black-tree implementation.
*          (should be correct even if we not fully
*           use it in the first part.)
*        - KNOWN BUG: several PUT's in TNF not possible,
*          therefore wrong Uniformity-Hyp's.
*        - splitting in the abstract scenario not deep enough -
*          splitting should continue for insert a and delete a.
*
* RBT_test.thy --- sequence testing red-black trees
* This file is part of HOL-TestGen.
*
* Copyright (c) 2005-2007 ETH Zurich, Switzerland
*               2011      Univ. Paris-Sud, France
*               2011      Achim D. Brucker, Germany
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
(* $Id: RBT_test.thy 9041 2010-11-10 17:40:39Z krieger $ *)


chapter {* Testing Properties of Red-Black Trees *}


theory 
 RBT_seq_test
imports 
 "../../unit/RBT/RBT_def"
 Testing 
begin

declare [[testgen_profiling]]


section{* Standard Sequence-Testing of Red-Black-Trees*}

subsection{* Test Against a Reference Implementation *}

definition insert :: "['a::LINORDER, 'a tree] \<Rightarrow> 'a tree"
where "insert a t = (case ins (a,t) of
                      E \<Rightarrow> E
                    | T R (T R l' e' r') e r \<Rightarrow> T B (T R l' e' r') e r
                    | T R E e r              \<Rightarrow> T R E e r (* id *)
                    | T R l e (T R l' e' r') \<Rightarrow> T R l e (T R l' e' r')
                    | T R l e E              \<Rightarrow> T R l e E (* id *))"

declare insert_def[simp] (* this definition is a computational rule *)



text{* The following definitions are essentially wrapper of the
  RBT - theory to the world of state-exception monads used for
  the formulation of the test specification. *}

definition   insert' :: "'a::LINORDER \<Rightarrow> (unit, 'a tree) MON\<^sub>S\<^sub>E"
where       "insert' a = (\<lambda> \<sigma>. Some((), insert a \<sigma>))"

text{* This definition leads to the following  symbolic evaluation rules:  *}
(* TODO: generation should be automated !!! Hidden behind an isar-supported process
   called "interface-abstraction". *)

lemmas insert'_reduce1[simp] =
       exec_bind_SE_success[of "insert' a", OF insert'_def [THEN fun_cong]]


lemmas insert'_reduce2[simp] =
       exec_mbindFSave_success[of "insert'", OF insert'_def [THEN fun_cong]]


definition  isin' :: "'a::LINORDER \<Rightarrow> (bool, 'a tree) MON\<^sub>S\<^sub>E"
where      "isin'  a = (\<lambda> \<sigma>. Some(isin a \<sigma>, \<sigma>))"

text{* This definition leads to the following symbolic evaluation rules:  *}

lemmas isin'_reduce1[simp] =
       exec_bind_SE_success[of "isin' a", 
                            OF isin'_def [THEN fun_cong]]

lemmas isin'_reduce2[simp] =
       exec_mbindFSave_success[of "isin'", OF isin'_def [THEN fun_cong]]

lemmas isin'_reduce3[simp] =
       exec_bind_SE_success'[of "isin' a", 
                             OF isin'_def [THEN fun_cong]]


text{* Positive case : Are elements that should be in the RBT  really in it ? *}
declare [[testgen_trace = true]]



test_spec "(E \<Turnstile>  (_  \<leftarrow> mbind \<iota>s insert'; out \<leftarrow> isin' (A::int);  return(out)))
           \<longrightarrow>
           (E \<Turnstile>  (_   \<leftarrow> mbind \<iota>s PUT_INSERT; out \<leftarrow> PUT_ISIN A;  return(out)))"
apply(gen_test_cases  "PUT_INSERT" "PUT_ISIN" split: ml_order.split ml_order.split_asm )
mk_test_suite "positive_rbt_test_on_concrete_model"




test_spec "E \<Turnstile>  (_  \<leftarrow> mbind \<iota>s insert'; out \<leftarrow> isin' A; return(\<not> out))
           \<Longrightarrow>
           E \<Turnstile>  (_ \<leftarrow> mbind \<iota>s PUT_INSERT; out \<leftarrow> PUT_ISIN (A::int); return(\<not> out))"
apply(gen_test_cases  "PUT_ISIN" "PUT_INSERT"
      split: ml_order.split ml_order.split_asm )
mk_test_suite "negative_rbt_test_on_concrete_model"



text{* Note that in this scenario the test sequences were constructed over the same statespace. *}


subsection{* Test Against an Abstract Implementation *}


text{* We introduce an abstract interface and its interpretation. *}
datatype        'a events = insert 'a | delete 'a
type_synonym    'a state_conc = "'a tree"
type_synonym    'a state_abs  = "'a set"

fun I_abs :: "'a events \<Rightarrow> (unit, 'a state_abs)MON\<^sub>S\<^sub>E"
where I_abs_insert : "I_abs (insert a) = (\<lambda>\<sigma>. Some((),{a} \<union> \<sigma>))"
     |I_abs_delete : "I_abs (delete a) = (\<lambda>\<sigma>. Some((), \<sigma> - {a}))"

text{* From this, we derive the usual symbolic exection rules:*}

lemmas I_abs_insert_reduce1[simp] =  exec_bind_SE_success[of "I_abs (insert a)", 
                                                          OF I_abs_insert [THEN fun_cong]]

lemmas I_abs_delete_reduce1[simp] = exec_bind_SE_success[of "I_abs (delete a)", 
                                                         OF I_abs_delete [THEN fun_cong]]

lemmas I_abs_insert_reduce2[simp] = exec_mbindFSave_success[of "I_abs" "(insert a)", 
                                                            OF I_abs_insert[THEN fun_cong]]

lemmas I_abs_delete_reduce2[simp] = exec_mbindFSave_success[of "I_abs" "(delete a)", 
                                                            OF I_abs_delete[THEN fun_cong]]


fun     is_in'_abs :: "'a \<Rightarrow> (bool, 'a state_abs)MON\<^sub>S\<^sub>E"
where  "is_in'_abs a =  (\<lambda> \<sigma>. Some(a \<in> \<sigma>, \<sigma>))"

lemmas is_in'_abs_reduce1[simp] = exec_bind_SE_success[of "is_in'_abs a", 
                                                       OF is_in'_abs.simps [THEN fun_cong]]

lemmas is_in'_abs_reduce2[simp] = exec_mbindFSave_success[of "is_in'_abs", 
                                                          OF is_in'_abs.simps [THEN fun_cong]]

lemmas is_in'_abs_reduce3[simp] = exec_bind_SE_success'[of "is_in'_abs a" "\<sigma>" "\<lambda>x. a \<in> \<sigma>", 
                                                        OF is_in'_abs.simps [THEN fun_cong]]

text{* We introduce (for specification purposes) an abstraction
relation $R_a$ linking concrete and abstract states. This paves the
way for understanding testing as a form of refinement. *}
definition    R_a :: "('a::LINORDER) state_conc \<Rightarrow> 'a state_abs"
where        "R_a t \<equiv> {x. isin x t}"

lemma R_a_E[simp]: "(R_a E) = {}"
by(simp add: R_a_def)

lemma R_a_T[simp]: "R_a (T a t (x::int) t') = {x} \<union> R_a t \<union> R_a t' "
by(auto simp: R_a_def)

text{* On this basis, we can define a forward simulation relation
  between $I_{abs}$ and $is\_in'_{abs}$ on the one hand and
  $PUT\_OP$ and $PUT\_ISIN$ on the other. *}


(* just to experiment : *)
lemma "({} \<Turnstile>  (_ \<leftarrow> mbind [] I_abs;out \<leftarrow> is_in'_abs A; return(out)))
      \<longrightarrow>
            (E \<Turnstile>  (_   \<leftarrow> mbind [] PUT_OP;
                           out \<leftarrow> PUT_ISIN A;
                           return(out)))"
by simp (* testcase vacuous *)

lemma "({} \<Turnstile> (_ \<leftarrow> mbind [insert a] I_abs; out \<leftarrow> is_in'_abs A; return(out)))
       \<longrightarrow>
       (E \<Turnstile> (_ \<leftarrow> mbind [insert a] PUT_OP; out \<leftarrow> PUT_ISIN A; return(out)))"
apply simp
oops (* testcase A = a *)

lemma "({} \<Turnstile> (_ \<leftarrow> mbind [insert a, delete a] I_abs; out \<leftarrow> is_in'_abs A; return(out)))
       \<longrightarrow>
       (E \<Turnstile> (_ \<leftarrow> mbind [insert a, delete a] PUT_OP; out \<leftarrow> PUT_ISIN A; return(out)))"
apply simp
done (* testcase vacuous *)


lemma "a \<noteq> b \<Longrightarrow> 
       ({} \<Turnstile> (_ \<leftarrow> mbind [insert a, delete b] I_abs; out \<leftarrow> is_in'_abs A; return(out)))
       \<longrightarrow>
       (E \<Turnstile> (_ \<leftarrow> mbind [insert a, delete b] PUT_OP; out \<leftarrow> PUT_ISIN A; return(out)))"
apply simp
(* testcase 
 a \<noteq> b \<Longrightarrow>
    A = a \<longrightarrow>
    (E \<Turnstile> ( _ \<leftarrow> mbind [events.insert a, delete b] PUT_OP; PUT_ISIN a))
*)
oops

test_spec " ({}\<Turnstile> (_ \<leftarrow> mbind \<iota>s I_abs; out \<leftarrow> is_in'_abs A; return(out)))
            \<longrightarrow>
            (E \<Turnstile> (_ \<leftarrow> mbind \<iota>s PUT_OP; out \<leftarrow> PUT_ISIN A; return(out)))"
apply(gen_test_cases 6 1 "PUT_ISIN"
      split: events.split events.split_asm )
mk_test_suite "positive_rbt_test_on_abstract_model"

(* HOL-TestGen Problem here : Splitting is not deep enough  !!! *)

test_spec "({} \<Turnstile> (_ \<leftarrow> mbind \<iota>s I_abs; out \<leftarrow> is_in'_abs A; return(\<not> out)))
           \<longrightarrow>
           (E \<Turnstile>  (_ \<leftarrow> PUT_OP; out \<leftarrow> PUT_ISIN A; return(\<not> out)))"
apply(gen_test_cases  "PUT_ISIN" 
      split: events.split events.split_asm )
mk_test_suite "negative_rbt_test_on_abstract_model"

end
