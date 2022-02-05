(*****************************************************************************
 * HOL-TestGen --- theorem-prover based test case generation
 *                 http://www.brucker.ch/projects/hol-testgen/
 *                                                                            
 * Automata.thy --- the base testing theory for automatas in sequence testing.
 * This file is part of HOL-TestGen.
 *
 * Copyright (c) 2005-2007 ETH Zurich, Switzerland
 *               2009-2017 Univ. Paris-Sud, France 
 *               2009-2015 Achim D. Brucker, Germany
 *               2015-2017 The University of Sheffield, UK
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

chapter {* Basic Automaton Theory *}

theory Automata imports Main
begin 

text{* Re-Definition of the following type synonyms from Monad-Theory - 
apart from that, these theories are independent. *}
type_synonym ('o, '\<sigma>) MON\<^sub>S\<^sub>E = "'\<sigma> \<rightharpoonup> ('o \<times> '\<sigma>)" (* = '\<sigma> \<Rightarrow> ('o \<times> '\<sigma>)option *) 
type_synonym ('o, '\<sigma>) MON\<^sub>S\<^sub>B = "'\<sigma> \<Rightarrow> ('o \<times> '\<sigma>) set"
type_synonym ('o, '\<sigma>) MON\<^sub>S\<^sub>B\<^sub>E = "'\<sigma> \<Rightarrow> (('o \<times> '\<sigma>) set) option"

 
subsection{* Deterministic I/O Automaton  *}


class fin = 
  assumes finite: "finite(UNIV::'a set)"
 

record ('\<alpha>, '\<sigma>) DA =
       init   :: "'\<sigma>"
       step   :: "'\<sigma> \<times> '\<alpha> \<Rightarrow> '\<sigma>"
       accept :: "'\<sigma> set"


typedef ('\<alpha>::fin, '\<sigma>::fin) DFA = "{x::('\<alpha>, '\<sigma>) DA. True}"
proof -
  show "\<exists>x. x \<in> {x. True}" by auto
qed

record ('\<alpha>, '\<sigma>) pDA =
       init :: "'\<sigma>"
       step :: "'\<sigma> \<times> '\<alpha> \<rightharpoonup> '\<sigma>"
       accept :: "'\<sigma> set"

typ "'a option"
record ('\<alpha>, '\<sigma>) NDA =
       init :: "'\<sigma>"
       step :: "('\<sigma> \<times> '\<alpha> \<times> '\<sigma>)set"
       accept :: "'\<sigma> set"


type_synonym ('\<iota>, 'o, '\<sigma>) ioNDA = "('\<iota> \<times> 'o, '\<sigma>) NDA"

record ('\<alpha>, '\<sigma>) EFSM =
       init :: "'\<sigma>"
       step :: "('\<sigma> \<times> '\<alpha> \<times> '\<sigma>)set"
       accept :: "'\<sigma> set"


record ('\<iota>, 'o, '\<sigma>) det_io_atm =
       init :: "'\<sigma>"
       step :: "'\<iota> \<Rightarrow> ('o, '\<sigma>) MON\<^sub>S\<^sub>E"


subsection{* Non-deterministic I/O automaton *}

text{* 
  We will use two styles of non-deterministic automaton: Labelled Transition
  Systems (LTS), which are intensively used in the literature, but tend to anihilate
  the difference between input and output, and non-deterministic automaton, which
  make this difference explicit and which have a closer connection to monads used
  for the operational aspects of testing.
*}

text{* 
  There we are: labelled transition systems. 
*}

record ('\<iota>, 'o, '\<sigma>) lts =
       init :: "'\<sigma> set"
       step :: "('\<sigma> \<times> ('\<iota> \<times> 'o) \<times> '\<sigma>) set"  (* false : this must be "('\<sigma> \<times> ('\<iota> + 'o) \<times> '\<sigma>) set" *)

text{* And, equivalently; non-deterministic io automata. *}

record ('\<iota>, 'o, '\<sigma>) ndet_io_atm =
       init :: "'\<sigma> set"
       step :: "'\<iota> \<Rightarrow> ('o, '\<sigma>) MON\<^sub>S\<^sub>B"


text{*
  First, we will prove the fundamental equivalence of these two notions.

  We refrain from a formal definition of explicit conversion functions
  and leave this internally in this proof (i.e. the existential witnesses).
*}

definition det2ndet :: "('\<iota>, 'o, '\<sigma>) det_io_atm \<Rightarrow> ('\<iota>, 'o, '\<sigma>) ndet_io_atm"
where     "det2ndet A = \<lparr>ndet_io_atm.init = {det_io_atm.init A},
                         ndet_io_atm.step = 
                                 \<lambda> \<iota> \<sigma>. if \<sigma> \<in> dom(det_io_atm.step A \<iota>) 
                                        then {the(det_io_atm.step A \<iota> \<sigma>)} 
                                        else {} \<rparr>" 

text{* 
  The following theorem establishes the fact that deterministic 
  automaton can be injectively embedded in non-deterministic ones. 
*}
lemma det2ndet_injective : "inj det2ndet"
    apply(auto simp: inj_on_def det2ndet_def)
    apply(tactic {* Record.split_simp_tac @{context} [] (K ~1) 1*}, simp)
    apply(simp (no_asm_simp) add: fun_eq_iff, auto)
    apply(drule_tac x=x in fun_cong, drule_tac x=xa in fun_cong)
    apply(case_tac "xa \<in> dom (step x)", simp_all)
    apply(case_tac "xa \<in> dom (stepa x)", 
          simp_all add: fun_eq_iff[symmetric], auto)
    apply(case_tac "xa \<in> dom (stepa x)", auto simp: fun_eq_iff[symmetric])
    apply(erule contrapos_np, simp)
    apply(drule Product_Type.split_paired_All[THEN iffD2])+ 
    apply(simp only: Option.not_Some_eq)
done


text{*
  We distinguish two forms of determinism - global determinism, where for each 
  state and input \emph{at most} one output-successor state 
  is assigned. 
*}
definition deterministic :: "('\<iota>, 'o, '\<sigma>) ndet_io_atm \<Rightarrow> bool"
where     "deterministic atm = (((\<exists> x. ndet_io_atm.init atm = {x}) \<and> 
                                (\<forall> \<iota> out. \<forall> p1 \<in> step atm \<iota> out.
                                         \<forall> p2 \<in> step atm \<iota> out.
                                           p1 = p2)))"

text{* In contrast, transition relations *}
definition \<sigma>deterministic :: "('\<iota>, 'o, '\<sigma>) ndet_io_atm \<Rightarrow> bool"
where     "\<sigma>deterministic atm = (\<exists> x. ndet_io_atm.init atm = {x} \<and>
                                    (\<forall> \<iota> out. 
                                       \<forall> p1 \<in> step atm \<iota> out.
                                         \<forall> p2 \<in> step atm \<iota> out.
                                           fst p1 = fst p2 \<longrightarrow> snd p1 = snd p2))"


lemma det2ndet_deterministic: "deterministic (det2ndet atm)"
  by(auto simp:deterministic_def det2ndet_def)

lemma det2ndet_\<sigma>deterministic: "\<sigma>deterministic (det2ndet atm)"
  by(auto simp: \<sigma>deterministic_def det2ndet_def)


text{* 
  The following theorem establishes the isomorphism of the two concepts
  IO-automata and LTS. We will therefore concentrate in the sequel on IO-Automata, 
  which have a slightly more realistic operational behaviour: you give the program 
  under test an input and get a possible set of responses rather than "agreeing 
  with the program under test" on a set of input-output-pairs. 
*}

definition ndet2lts :: "('\<iota>, 'o, '\<sigma>) ndet_io_atm \<Rightarrow> ('\<iota>, 'o, '\<sigma>) lts"
where     "ndet2lts A = \<lparr>lts.init = init A,
                         lts.step = {(s,io,s').(snd io,s') \<in> step A (fst io) s}\<rparr>"

definition lts2ndet :: " ('\<iota>,'o,'\<sigma>) lts \<Rightarrow> ('\<iota>, 'o, '\<sigma>) ndet_io_atm"
where     "lts2ndet A = \<lparr>init = lts.init A,
                         step = \<lambda> i s. {(out,s'). (s, (i,out), s') 
                                                     \<in> lts.step A}\<rparr>"

lemma ndet_io_atm_isomorph_lts : "bij ndet2lts"
  apply (auto simp: bij_def inj_on_def surj_def ndet2lts_def)
    apply (tactic {* Record.split_simp_tac @{context} [] (K ~1) 1*}, simp)
    apply (rule ext, rule ext, simp add: set_eq_iff)
  apply (rule_tac x = "lts2ndet y" in exI)
  apply (simp add: lts2ndet_def)
  done


(* Lemma missing: for deterministic ndet_atm's, det2ndet is even bijective,
i.e the definition above is indeed a characterization. *)

text{* 
  The following well-formedness property is important: for every state,
  there is a valid transition. Otherwise, some states may never be part of an
  (infinite) trace. 
*}    

definition is_enabled :: "['\<iota> \<Rightarrow> ('o, '\<sigma>) MON\<^sub>S\<^sub>B, '\<sigma> ] \<Rightarrow> bool"
where     "is_enabled rel \<sigma> = (\<exists> \<iota>. rel \<iota> \<sigma> \<noteq> {})"

definition is_enabled' :: "['\<iota> \<Rightarrow> ('o, '\<sigma>) MON\<^sub>S\<^sub>E, '\<sigma> ] \<Rightarrow> bool"
where     "is_enabled' rel \<sigma> = (\<exists> \<iota>. \<sigma> \<in> dom(rel \<iota>))"


definition live_wff:: "('\<iota>, 'o, '\<sigma>) ndet_io_atm \<Rightarrow> bool"
where     "live_wff atm = (\<forall> \<sigma>. \<exists> \<iota>. step atm \<iota> \<sigma> \<noteq> {})"

lemma life_wff_charn: "live_wff atm = (\<forall> \<sigma>. is_enabled (step atm) \<sigma>)"
  by(auto simp: live_wff_def is_enabled_def)

text{* 
  There are essentially two approaches: either we disallow non-enabled transition 
  systems---via life\_wff\_charn---or we restrict our machinery for traces and prefixed closed
  sets of runs over them 
*}

section{* Rich Traces and its Derivatives *}
text{* 
  The easiest way to define the concept of traces is on LTS. Via the injections described 
  above, we can define notions like deterministic automata rich trace, and i/o automata rich 
  trace. Moreover, we can easily project event traces or state traces from rich traces. *}

type_synonym      ('\<iota>, 'o, '\<sigma>) trace  = "nat \<Rightarrow> ('\<sigma> \<times> ('\<iota> \<times> 'o) \<times> '\<sigma>)"
type_synonym           ('\<iota>, 'o) etrace     = "nat \<Rightarrow> ('\<iota> \<times> 'o)"  (* event traces *)
type_synonym           '\<sigma> \<sigma>trace          = "nat \<Rightarrow> '\<sigma>"
type_synonym           '\<iota> in_trace         = "nat \<Rightarrow> '\<iota>"
type_synonym           'o out_trace        = "nat \<Rightarrow> 'o"  
type_synonym           ('\<iota>, 'o, '\<sigma>) run    = "('\<sigma> \<times> ('\<iota> \<times> 'o) \<times> '\<sigma>) list"
type_synonym           ('\<iota>, 'o) erun       = "('\<iota> \<times> 'o) list"
type_synonym           '\<sigma> \<sigma>run            = "'\<sigma> list"
type_synonym           '\<iota> in_run           = "'\<iota> list"
type_synonym           'o out_run          = "'o list"  

definition rtraces ::"('\<iota>, 'o, '\<sigma>) ndet_io_atm \<Rightarrow> ('\<iota>, 'o, '\<sigma>) trace set"
where     "rtraces atm = { t. fst(t 0) \<in> init atm \<and>
                              (\<forall> n. fst(t (Suc n)) = snd(snd(t n))) \<and>
                              (\<forall> n. if is_enabled (step atm) (fst(t n))
                                    then t n \<in> {(s,io,s'). (snd io,s') 
                                                       \<in> step atm (fst io) s}
                                    else t n = (fst(t n),undefined,fst(t n)))}"   

lemma init_rtraces[elim!]: "t \<in> rtraces atm \<Longrightarrow> fst(t 0) \<in> init atm"
by(auto simp: rtraces_def)

lemma post_is_pre_state[elim!]:  "t \<in> rtraces atm \<Longrightarrow> fst(t (Suc n)) = snd(snd(t n))"
by(auto simp: rtraces_def)


lemma enabled_transition[elim!]:
"\<lbrakk>t \<in> rtraces atm; is_enabled (step atm) (fst(t n)) \<rbrakk> 
 \<Longrightarrow>  t n \<in> {(s,io,s'). (snd io,s') \<in> step atm (fst io) s}"
apply(simp add: rtraces_def split_def, safe)
apply (erule allE)+
apply (auto simp add: split: if_split_asm)
done

lemma nonenabled_transition[elim!]: "\<lbrakk>t \<in> rtraces atm; \<not> is_enabled (step atm) (fst(t n)) \<rbrakk> 
                                      \<Longrightarrow>  t n = (fst(t n),undefined,fst(t n))"
by(simp add: rtraces_def split_def)


text{* 
  The latter definition solves the problem of inherently finite traces, i.e. those that reach 
  a state in which they are no longer enabled. They are represented by stuttering steps on 
  the same state. 
*}

definition fin_rtraces :: "('\<iota>, 'o, '\<sigma>) ndet_io_atm \<Rightarrow> ('\<iota>, 'o, '\<sigma>) trace set"
where     "fin_rtraces atm = { t . t \<in> rtraces atm \<and> 
                                  (\<exists> n. \<not> is_enabled (step atm) (fst(t n)))}"

lemma fin_rtraces_are_rtraces : "fin_rtraces atm \<subseteq> rtraces atm"
by(auto simp: rtraces_def fin_rtraces_def)


definition \<sigma>traces ::"('\<iota>, 'o, '\<sigma>) ndet_io_atm \<Rightarrow> '\<sigma> \<sigma>trace set"   
where     "\<sigma>traces atm = {t . \<exists> rt \<in> rtraces atm. t = fst o rt }"

definition etraces ::"('\<iota>, 'o, '\<sigma>) ndet_io_atm \<Rightarrow> ('\<iota>, 'o) etrace set"   
where     "etraces atm = {t . \<exists> rt \<in> rtraces atm. t = fst o snd o rt }"

definition in_trace :: "('\<iota>, 'o) etrace \<Rightarrow> '\<iota> in_trace"  
where     "in_trace rt = fst o rt"

definition out_trace :: "('\<iota>, 'o) etrace \<Rightarrow> 'o out_trace"  
where     "out_trace rt = snd o rt"

definition prefixes :: "(nat \<Rightarrow> '\<alpha>) set \<Rightarrow> '\<alpha> list set"  
where     "prefixes ts = {l. \<exists> t \<in> ts. \<exists> (n::int). l = map (t o nat) [0..n]}"

definition rprefixes :: "['\<iota> \<Rightarrow> ('o, '\<sigma>) MON\<^sub>S\<^sub>B,
                           ('\<iota>, 'o, '\<sigma>) trace set] \<Rightarrow> ('\<iota>, 'o, '\<sigma>) run set"  
where     "rprefixes rel ts = {l. \<exists> t \<in> ts. \<exists> n. (is_enabled rel (fst(t (nat n))) \<and>
                                                  l = map (t o nat) [0..n])}"
definition eprefixes :: "['\<iota> \<Rightarrow> ('o, '\<sigma>) MON\<^sub>S\<^sub>B,
                           ('\<iota>, 'o, '\<sigma>) trace set] \<Rightarrow> ('\<iota>, 'o) erun set"  
where     "eprefixes rel ts = (map (fst o snd)) ` (rprefixes rel ts)"

definition \<sigma>prefixes :: "['\<iota> \<Rightarrow> ('o, '\<sigma>) MON\<^sub>S\<^sub>B,
                           ('\<iota>, 'o, '\<sigma>) trace set] \<Rightarrow> '\<sigma> \<sigma>run set"  
where     "\<sigma>prefixes rel ts = (map fst) ` (rprefixes rel ts)"



section{* Extensions: Automata with Explicit Final States *}


text{* 
  We model a few widely used variants of automata as record extensions. In particular, we 
  define automata with final states and internal (output) actions. 
*}

record ('\<iota>, 'o, '\<sigma>) det_io_atm' = "('\<iota>, 'o, '\<sigma>) det_io_atm" + 
       final :: "'\<sigma> set"

text{* 
  A natural well-formedness property to be required from this type of atm  is as follows: whenever 
  an atm' is in a final state, the transition operation is undefined. 
*}

definition final_wff:: "('\<iota>, 'o, '\<sigma>) det_io_atm' \<Rightarrow> bool"
where     "final_wff atm' =
                   (\<forall>\<sigma> \<in> final atm'. \<forall>\<iota>. \<sigma> \<notin> dom (det_io_atm.step atm' \<iota>))"

text{* 
  Another extension provides the concept of internal actions, which are considered as part of 
  the output alphabet here. If internal actions are also used for synchronization, further 
  extensions admitting internal input actions will be necessary, too, which we do not model here. 
*}
       
record ('\<iota>, 'o, '\<sigma>) det_io_atm'' = "('\<iota>, 'o, '\<sigma>) det_io_atm'" + 
       internal :: "'o set"

text{* 
  A natural well-formedness property to be required from this type of atm is as follows: whenever 
  an atm' is in a final state, the transition operation is required to provide a state that is 
  again final and an output that is considered internal. 
*}   
    
definition final_wff2:: "('\<iota>, 'o, '\<sigma>) det_io_atm'' \<Rightarrow> bool"
where     "final_wff2 atm'' = (\<forall>\<sigma> \<in> final atm''.
                                \<forall> \<iota>. \<sigma> \<in> dom (det_io_atm.step atm'' \<iota>) \<longrightarrow> 
                                  (let (out, \<sigma>') = the(det_io_atm.step atm'' \<iota> \<sigma>)
                                   in out \<in> internal atm'' \<and> \<sigma>' \<in> final atm''))"

text{* 
  Of course, for this type of extended automata, it is also possible to impose the additional 
  requirement that the step function is total---undefined steps would then be represented as 
  steps leading to final states. 

  The standard extensions on deterministic automata are also redefined for the non-deterministic 
  (specification) case. 
*}

record ('\<iota>, 'o, '\<sigma>) ndet_io_atm' = "('\<iota>, 'o, '\<sigma>) ndet_io_atm" + 
       final :: "'\<sigma> set"

definition final_wff_ndet_io_atm2 :: "('\<iota>, 'o, '\<sigma>) ndet_io_atm' \<Rightarrow> bool"
  where "final_wff_ndet_io_atm2 atm' = (\<forall>\<sigma> \<in> final atm'. \<forall>\<iota>. ndet_io_atm.step atm' \<iota> \<sigma> = {})"

record ('\<iota>, 'o, '\<sigma>) ndet_io_atm'' = "('\<iota>, 'o, '\<sigma>) ndet_io_atm'" + 
       internal :: "'o set"

definition final_wff2_ndet_io_atm2 :: "('\<iota>, 'o, '\<sigma>) ndet_io_atm'' \<Rightarrow> bool"
  where "final_wff2_ndet_io_atm2 atm'' =
                     (\<forall>\<sigma> \<in> final atm''.
                        \<forall>\<iota>. step atm'' \<iota> \<sigma> \<noteq> {} \<longrightarrow> step atm'' \<iota> \<sigma>  \<subseteq> internal atm'' \<times> final atm'')"

end
