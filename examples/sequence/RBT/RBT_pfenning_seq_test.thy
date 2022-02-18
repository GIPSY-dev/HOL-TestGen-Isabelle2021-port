
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
* Copyright (c) 2005-2007, ETH Zurich, Switzerland
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
 RBT_pfenning_seq_test
imports 
 "../../unit/RBT/RBT_def"
 Testing
begin

declare [[testgen_profiling]]

section{* Standard Sequence-Testing of Red-Black-Trees*}

subsection{* Test Against a Reference Implementation *}

(* Stolen from Frank Pfennig,
http://www.cs.cmu.edu/afs/cs/user/rowan/www/src/red-black-okasaki.sml.

  (*[ restore_right <: 'a badRight -> 'a rbt ]*)
  fun restore_right (Black(e:'a entry, Red lt, Red (rt as (_,Red _,_)))) =
         Red(e, Black lt, Black rt)     (* re-color *)
    | restore_right (Black(e, Red lt, Red (rt as (_,_,Red _)))) =
         Red(e, Black lt, Black rt)     (* re-color *)
    | restore_right (Black(e, l, Red(re, Red(rle, rll, rlr), rr))) =
         (* l is black, deep rotate *)
         Black(rle, Red(e, l, rll), Red(re, rlr, rr))
    | restore_right (Black(e, l, Red(re, rl, rr as Red _))) =
         (* l is black, shallow rotate *)
         Black(re, Red(e, l, rl), rr)
    | restore_right dict = dict


  (* restore_left is like restore_right, except *)
  (* the color invariant may be violated only at the root of left child *)
  (*[ restore_left <: 'a badLeft -> 'a rbt ]*)
  fun restore_left (Black(e:'a entry, Red (lt as (_,Red _,_)), Red rt)) =
         Red(e, Black lt, Black rt)     (* re-color *)
    | restore_left (Black(e, Red (lt as (_,_,Red _)), Red rt)) =
         Red(e, Black lt, Black rt)     (* re-color *)
    | restore_left (Black(e, Red(le, ll as Red _, lr), r)) =
         (* r is black, shallow rotate *)
         Black(le, ll, Red(e, lr, r))
    | restore_left (Black(e, Red(le, ll, Red(lre, lrl, lrr)), r)) =
         (* r is black, deep rotate *)
         Black(lre, Red(le, ll, lrl), Red(e, lrr, r))
    | restore_left dict = dict


 fun 'a insert (dict, entry as (key,datum)) =
    let
      (* val ins : 'a dict -> 'a dict  inserts entry *)
      (* ins (Red _) may violate color invariant at root *)
      (* ins (Black _) or ins (Empty) will be red/black tree *)
      (* ins preserves black height *)
      (*[ ins1 <: 'a rbt -> 'a badRoot   & 'a bt -> 'a rbt  ]*)
      fun ins1 (Empty) = Red(entry, Empty, Empty)
        | ins1 (Red(entry1 as (key1, datum1), left, right)) =
          (case compare(key,key1)
             of EQUAL => Red(entry, left, right)
              | LESS => Red(entry1, ins1 left, right)
              | GREATER => Red(entry1, left, ins1 right))
        | ins1 (Black(entry1 as (key1, datum1), left, right)) =
          (case compare(key,key1)
             of EQUAL => Black(entry, left, right)
              | LESS => restore_left (Black(entry1, ins1 left, right))
              | GREATER => restore_right (Black(entry1, left, ins1 right)))
    in                (* the second conjuct is needed for the recursive cases *)
      case ins1 dict
        of Red (t as (_, Red _, _)) => Black t (* re-color *)
         | Red (t as (_, _, Red _)) => Black t (* re-color *)
         | dict => dict                        (* depend on sequential matching *)
    end
*)

fun restore_right :: "'a tree \<Rightarrow> 'a tree"
where 
  re_color1: "restore_right (T B (* lt as *) (T R l1 e1 r1)
                                 e
                                 (* rt as *) (T R (T R l4 e4 r4) e3 r3))
                          = (T R (T B l1 e1 r1)
                                 e
                                 (T B (T R l4 e4 r4) e3 r3))"
|re_color2: "restore_right (T B (* lt as *) (T R l1 e1 r1)
                                e
                                (* rt as *) (T R l3 e3 (T R l4 e4 r4)))
                          = (T R (T B l1 e1 r1)
                                 e
                                 (T R l3 e3 (T R l4 e4 r4)))"
|deep_rot:  "restore_right (T B l e (T R (T R rll rle rlr) re rr)) =
                            (T B  (T R l e rll) rle (T R rlr re rr))"
|shall_rot: "restore_right (T B l e (T R rl re (T R l1 e1 r1))) =
                            (T B (T R l e rl) re (T R l1 e1 r1))"
|default:"restore_right dict = dict"

fun restore_left :: "'a tree \<Rightarrow> 'a tree"
where "restore_left t = t "   (* TO BE DONE !!! *)

fun    ins :: "['a::LINORDER, 'a tree] \<Rightarrow> 'a tree"
where  mt : "ins entry E = (T R E entry E)"
     | red: "ins entry (T R left entry1 right) =
                 (case compare entry entry1 of
                     EQUAL   \<Rightarrow> (T R left entry right)
                   | LESS    \<Rightarrow> (T R (ins entry left) entry1 right)
                   | GREATER \<Rightarrow> (T R left  entry1 (ins entry right))
                 )"
     | black: "ins entry (T B left entry1 right) =
                 (case compare entry entry1 of
                     EQUAL   \<Rightarrow> (T B left entry right)
                   | LESS    \<Rightarrow> (* restore_left *) (T B (ins entry left) entry1 right)
                   | GREATER \<Rightarrow> (* restore_right*) (T B left  entry1 (ins entry right))
                 )"

definition insert :: "['a::LINORDER, 'a tree] \<Rightarrow> 'a tree"
where "insert a t = (case ins a t of
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

text{* This definition leads to the following 
       symbolic evaluation rules: 
       (TODO: generation should be automated !!! ) *}

lemmas insert'_reduce1[simp] =
       exec_bind_SE_success[of "insert' a", OF insert'_def [THEN fun_cong]]


lemmas insert'_reduce2[simp] =
       exec_mbindFSave_success[of "insert'", OF insert'_def [THEN fun_cong]]


definition  isin' :: "'a::LINORDER \<Rightarrow> (bool, 'a tree) MON\<^sub>S\<^sub>E"
where      "isin'  a = (\<lambda> \<sigma>. Some(isin a \<sigma>, \<sigma>))"

text{* This definition leads to the following 
       symbolic evaluation rules: 
       (TODO: generation should be automated !!! ) *}

lemmas isin'_reduce1[simp] =
       exec_bind_SE_success[of "isin' a", OF isin'_def [THEN fun_cong]]



lemmas isin'_reduce2[simp] =
       exec_mbindFSave_success[of "isin'", OF isin'_def [THEN fun_cong]]

lemmas isin'_reduce3[simp] =
       exec_bind_SE_success'[of "isin' a", OF isin'_def [THEN fun_cong]]


text{* Positive case : Are elements that should be in the RBT  really in it ? *}

declare [[testgen_trace = true]]

test_spec "(E \<Turnstile> (_  \<leftarrow> mbind \<iota>s insert'; out \<leftarrow> isin' (A::int);  return(out)))
           \<longrightarrow>
           (E \<Turnstile> (_   \<leftarrow> mbind \<iota>s PUT_INSERT; out \<leftarrow> PUT_ISIN A;  return(out)))"
apply(gen_test_cases  "PUT_ISIN" "PUT_INSERT" split: ml_order.split ml_order.split_asm )
mk_test_suite "positive_rbt_test_on_concrete_model"


text{* Negative case : Are elements that should not be in the RBT  not in it ? *}


test_spec "(E \<Turnstile>  (_  \<leftarrow> mbind \<iota>s insert'; out \<leftarrow> isin' A;  return(\<not> out)))
           \<longrightarrow>
           (E \<Turnstile>  (_ \<leftarrow> mbind \<iota>s PUT_INSERT; out \<leftarrow> PUT_ISIN (A::int); return(\<not> out)))"
apply(gen_test_cases  "PUT_ISIN"  "PUT_INSERT"
      split: ml_order.split ml_order.split_asm )
mk_test_suite "negative_rbt_test_on_concrete_model"

(* Problem observed:
15. PO ((??X61X9 < ??X60X8 \<and> ??X62X10 < ??X60X8) \<and>
         \<not> isin ??X58X6 undefined)
This is likely due to a bug in the insert-operation. CHECK THIS !
*)


text{* Note that in this scenario the test sequences were constructed
  over the same statespace () *}


text{* To the sceptical referee: We admit that, although there are numerous
  attempts to prove empirically the relevance of Formal Methods in General
  and Model-based Testing in particular, none of them is fully convincing.
  We actually believe that, as in similar technological 
  paradigm shifts in the past (say: the transition from assembly language to 
  more abstract languages and C at the beginning of the 70ies), there will 
  never be an empirical proof of justification as a whole; methodological 
  problems of such a proof (non-reproducibility of projects, high number of 
  observables, inherently difficult to mesure trade-offs like "mastering 
  complexity and novelty" vs.  "impact of attractivity of a method to engineers") 
  will prevent this. Philosophical sceptics may therefore insist on the view, that
  CC-EAL5 - EAL7 certifications factually require formal methods is just
  unfounded and some kind of religious belief.
  We assume the pragmatic view that 

-\<dots>

  For all others, or those who just pragmatically attempt to comply to higher
  levels of CC standards, we believe that our technology is competetive.

  *}



subsection{* Test Against an Abstract Implementation *}


(*
declare insert'_reduce1[simp del]
declare insert'_reduce2[simp del]
declare isin'_reduce1[simp del]
declare isin'_reduce2[simp del]

declare insert'_reduce1[simp]
declare insert'_reduce2[simp]
declare isin'_reduce1[simp]
declare isin'_reduce2[simp]
  *)


text{* We introduce an abstract interface and its interpretation. *}
datatype      'a events = insert 'a | delete 'a
type_synonym  'a state_conc = "'a tree"
type_synonym  'a state_abs  = "'a set"

fun I_abs :: "'a events \<Rightarrow> (unit, 'a state_abs)MON\<^sub>S\<^sub>E"
where I_abs_insert : "I_abs (insert a) = (\<lambda>\<sigma>. Some((),{a} \<union> \<sigma>))"
     |I_abs_delete : "I_abs (delete a) = (\<lambda>\<sigma>. Some((), \<sigma> - {a}))"

text{* From this, we derive the usual symbolic exection rules:*}

lemmas I_abs_insert_reduce1[simp] =
       exec_bind_SE_success[of "I_abs (insert a)", 
       OF I_abs_insert [THEN fun_cong]]

lemmas I_abs_delete_reduce1[simp] =
       exec_bind_SE_success[of "I_abs (delete a)", 
       OF I_abs_delete [THEN fun_cong]]


lemmas I_abs_insert_reduce2[simp] =
       exec_mbindFSave_success[of "I_abs" "(insert a)", OF I_abs_insert[THEN fun_cong]]

lemmas I_abs_delete_reduce2[simp] =
       exec_mbindFSave_success[of "I_abs" "(delete a)", OF I_abs_delete[THEN fun_cong]]

fun               is_in'_abs :: "'a \<Rightarrow> (bool, 'a state_abs)MON\<^sub>S\<^sub>E"
where is_in'_abs: "is_in'_abs a =  (\<lambda> \<sigma>. Some(a \<in> \<sigma>, \<sigma>))"


lemmas is_in'_abs_reduce1[simp] =
       exec_bind_SE_success[of "is_in'_abs a",OF is_in'_abs [THEN fun_cong]]

lemmas is_in'_abs_reduce2[simp] =
       exec_mbindFSave_success[of "is_in'_abs", OF is_in'_abs [THEN fun_cong]]

lemmas is_in'_abs_reduce3[simp] =
       exec_bind_SE_success'[of "is_in'_abs a" "\<sigma>" "\<lambda>x. a\<in>\<sigma>",OF is_in'_abs[THEN fun_cong]]


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
lemma "({} \<Turnstile>  (_    \<leftarrow> mbind [] I_abs; out \<leftarrow> is_in'_abs A; return(out)))
       \<longrightarrow>
       (E \<Turnstile>  (_   \<leftarrow> mbind [] PUT_OP; out \<leftarrow> PUT_ISIN A; return(out)))"
by simp (* testcase vacuous *)

lemma "({} \<Turnstile>  (_ \<leftarrow> mbind [insert a] I_abs; out \<leftarrow> is_in'_abs A; return(out)))
        \<longrightarrow>
       (E \<Turnstile>  (_   \<leftarrow> mbind [insert a] PUT_OP; out \<leftarrow> PUT_ISIN A; return(out)))"
apply simp
oops (* testcase A = a *)

lemma "({} \<Turnstile>  (_    \<leftarrow> mbind [insert a, delete a] I_abs;
                            out \<leftarrow> is_in'_abs A;
                            return(out)))
            \<longrightarrow>
            (E \<Turnstile>  (_   \<leftarrow> mbind [insert a, delete a] PUT_OP;
                           out \<leftarrow> PUT_ISIN A;
                           return(out)))"
apply simp
done (* testcase vacuous *)


lemma "a \<noteq> b \<Longrightarrow>
             ({} \<Turnstile>  (_    \<leftarrow> mbind [insert a, delete b] I_abs;
                            out \<leftarrow> is_in'_abs A;
                            return(out)))
            \<longrightarrow>
            (E \<Turnstile>  (_   \<leftarrow> mbind [insert a, delete b] PUT_OP;
                           out \<leftarrow> PUT_ISIN A;
                           return(out)))"
apply simp
oops

test_spec " ({} \<Turnstile>  (_    \<leftarrow> mbind \<iota>s I_abs;
                            out \<leftarrow> is_in'_abs A;
                            return(out)))
            \<longrightarrow>
            (E \<Turnstile>  (_   \<leftarrow> mbind \<iota>s PUT_OP;
                           out \<leftarrow> PUT_ISIN A;
                           return(out)))"
apply(gen_test_cases 6 1 "PUT_ISIN" "PUT_OP"
      split: events.split events.split_asm )
mk_test_suite "positive_rbt_test_on_abstract_model"

(* HOL-TestGen Problem here : Splitting is not deep enough  !!! *)

test_spec "({} \<Turnstile>  (_   \<leftarrow> mbind \<iota>s I_abs;
                           out \<leftarrow> is_in'_abs A;
                           return(\<not> out)))
           \<Longrightarrow>
           (E \<Turnstile> (_   \<leftarrow> PUT_OP;
                           out \<leftarrow> PUT_ISIN A;
                           return(\<not> out)))"
apply(gen_test_cases  "PUT_ISIN" "PUT_OP"
      split: events.split events.split_asm )
mk_test_suite "negative_rbt_test_on_abstract_model"


end
