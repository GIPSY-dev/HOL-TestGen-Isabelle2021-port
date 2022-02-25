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

theory TestRefinements imports Monads Automata
begin 



text{* converts infinite trace sets to prefix-closed sets of finite traces,
reconciling the most common different concepts of traces ... *}

consts    cnv :: "(nat \<Rightarrow> '\<alpha>) \<Rightarrow> '\<alpha> list"
(* NAIV !!! *)
  
(* I WOULD PREFER A SYMMETRIC NOTION OF REFINEMENT ... However, this makes the use
of mbind less clear and evident. Sufficient conditions when these two things
are equivalent need to be explored ... *)


definition  input_refine ::
             "[('\<iota>,'o,'\<sigma>) det_io_atm,('\<iota>,'o,'\<sigma>) ndet_io_atm] \<Rightarrow> bool"
where     
  input_refine_def:  
       "input_refine I SP = 
       (({det_io_atm.init I} = ndet_io_atm.init SP) \<and> 
        (\<forall> t \<in> cnv ` (in_trace `(etraces SP)). 
                   (det_io_atm.init I) 
                   \<Turnstile> (os \<leftarrow> (mbind t (det_io_atm.step I)) ;
                      return(length t = length os))))"
notation  input_refine ("(_/ \<sqsubseteq>\<^sub>I _)" [51, 51] 50)

text{* This testing notion essentially says: whenever we can run an
input sequence succesfully on the PUT (the program does not throw an exception),
it is ok. *}

definition   input_output_refine ::
             "[('\<iota>,'o,'\<sigma>) det_io_atm,('\<iota>,'o,'\<sigma>) ndet_io_atm] \<Rightarrow> bool" 
where
 input_output_refine_def:
         "input_output_refine i s  \<equiv> 
              ({det_io_atm.init i} = ndet_io_atm.init s) \<and> 
               (\<forall> t \<in> prefixes (etraces s). 
                     (det_io_atm.init i) 
                     \<Turnstile> (os \<leftarrow> (mbind (map fst t) (det_io_atm.step i));
                              return((map snd t) = os)))"
                         
notation  input_output_refine ("(_/ \<sqsubseteq>\<^sub>IO _)" [51, 51] 50)                          
text{* Our no-frills-approach to I/O conformance testing:
no quiescense, and strict alternation between input and output. *}

text{* PROBLEM : Tretmanns / Belinfantes notion of ioco is inherently 
different from Gaudels, which is refusal based. 
See definition in accompanying IOCO.thy file:
\begin{verbatim}

definition ioco :: "[('\<iota>,'o option,'\<sigma>)IO_TS,('\<iota>,'o option,'\<sigma>)IO_TS] \<Rightarrow> bool" 
                     (infixl "ioco" 200)
         "i ioco s \<equiv> (\<forall> t \<in> Straces(s). 
                       out i (i after t) \<subseteq> out s (s after t))"

\end{verbatim}

*}


definition  after   :: "[('\<iota>, 'o, '\<sigma>) ndet_io_atm, ('\<iota> \<times> 'o) list] \<Rightarrow> '\<sigma> set"  
            (infixl "after" 100)
where      "atm after l = {\<sigma>' . \<exists> t \<in> rtraces atm. (\<sigma>' = fst(t (length l)) \<and>  
              (\<forall> n \<in> {0 .. (length l) - 1}. l!n = fst(snd(t n))))}"

definition out     :: "[('\<iota>, 'o, '\<sigma>) ndet_io_atm,'\<sigma> set, '\<iota>] \<Rightarrow> 'o set"
where     "out atm ss \<iota> = {a. \<exists>\<sigma> \<in> ss. \<exists>\<sigma>'. (a,\<sigma>') \<in> ndet_io_atm.step atm \<iota> \<sigma>}"

(* OLD:
definition ioco    :: "[('\<iota>, 'o, '\<sigma>) det_io_atm,('\<iota>, 'o, '\<sigma>) ndet_io_atm] \<Rightarrow> bool" 
                     (infixl "ioco" 200)
where     "i ioco s = (({det_io_atm.init i} = ndet_io_atm.init s) \<and> 
                      (\<forall> t \<in> cnv ` (etraces s). 
                           \<forall> \<iota> \<omega>. 
                              ((det_io_atm.init i) 
                                \<Turnstile> (os \<leftarrow> (mbind (map fst t @ [\<iota>]) (det_io_atm.step i)) ;
                                     return(os =  map snd t @ [\<omega>]))) 
                              \<longrightarrow> 
                              \<omega> \<in> out s (s after t)))" *)

definition ready     :: "[('\<iota>, 'o, '\<sigma>) ndet_io_atm,'\<sigma> set] \<Rightarrow> '\<iota> set"
where     "ready atm ss = {\<iota>. \<exists>\<sigma> \<in> ss. ndet_io_atm.step atm \<iota> \<sigma> \<noteq> {}}"

definition ioco    :: "[('\<iota>,'o,'\<sigma>)ndet_io_atm, ('\<iota>,'o,'\<sigma>)ndet_io_atm] \<Rightarrow> bool" 
                     (infixl "ioco" 200)
where     "i ioco s = (\<forall> t \<in> prefixes(etraces s).
		         \<forall> \<iota> \<in> ready s (s after t). out i (i after t) \<iota> \<subseteq> out s (s after t) \<iota>)"

definition oico    :: "[('\<iota>,'o,'\<sigma>)ndet_io_atm,('\<iota>,'o,'\<sigma>)ndet_io_atm] \<Rightarrow> bool"
                     (infixl "oico" 200)
where     "i oico s = (\<forall> t \<in> prefixes(etraces s).
                        ready i (i after t) \<supseteq> ready s (s after t))"

definition ioco2    :: "[('\<iota>,'o,'\<sigma>)ndet_io_atm, ('\<iota>,'o,'\<sigma>)ndet_io_atm] \<Rightarrow> bool" 
                     (infixl "ioco2" 200)
where     "i ioco2 s = (\<forall> t \<in> eprefixes (ndet_io_atm.step s) (rtraces s).
		                      \<forall> \<iota> \<in> ready s (s after t).
                             out i (i after t) \<iota> \<subseteq> out s (s after t) \<iota>)"

definition ico    :: "[('\<iota>, 'o, '\<sigma>) det_io_atm,('\<iota>, 'o, '\<sigma>) ndet_io_atm] \<Rightarrow> bool"
                     (infixl "ico" 200)
where     "i ico s = (\<forall> t \<in> prefixes(etraces s).
		       let i' = det2ndet i  in  ready i' (i' after t) \<supseteq> ready s (s after t))"

lemma full_det_refine: "s = det2ndet s' \<Longrightarrow> 
  (det2ndet i) ioco s \<and> (det2ndet i) oico s \<longleftrightarrow> input_output_refine i s"
apply(safe)
oops

definition ico2    :: "[('\<iota>,'o,'\<sigma>)ndet_io_atm,('\<iota>,'o,'\<sigma>)ndet_io_atm] \<Rightarrow> bool"
                     (infixl "ico2" 200)
where     "i ico2 s \<equiv> \<forall> t \<in> eprefixes (ndet_io_atm.step s) (rtraces s).
                        ready i (i after t) \<supseteq> ready s (s after t)"


text{* There is lots of potential for optimization.
\begin{itemize}
\item only maximal prefixes
\item draw the $\omega$ tests inside the return
\item compute the $\omega$ by the $\ioprog$, not quantify over it.
\end{itemize}
*}

section{* Generic Monadic Test Refinement Notions  *}

text{* Generic Notion *}

definition monadic_test_refinement ::
                       "('\<iota> \<Rightarrow> ('o, '\<sigma>)MON\<^sub>S\<^sub>E) \<Rightarrow> 
                       '\<sigma> set \<Rightarrow> (* state invariant *)
                        '\<iota> list set \<Rightarrow> (* coverage or test-purpose *) 
                        ('\<iota> list \<Rightarrow>  'o list  \<Rightarrow> '\<alpha> \<Rightarrow> bool) \<Rightarrow>  (* post-cond *)
                       ('\<iota> \<Rightarrow> ('o, '\<sigma>)MON\<^sub>S\<^sub>E) \<Rightarrow> bool"   
                       ("_ \<sqsubseteq>\<^sub>\<langle>_,_,_\<^sub>\<rangle> _" [100,100,100,100,100]101)
where 


    "(MODEL \<sqsubseteq>\<^sub>\<langle>Init,CovCrit,conf\<^sub>\<rangle> SUT) = 
           (\<forall> \<sigma>\<^sub>0 \<in> Init.  \<forall>  \<iota>s \<in> CovCrit. \<forall> res.
                 (\<sigma>\<^sub>0 \<Turnstile> (os \<leftarrow> mbind \<iota>s MODEL; return (conf \<iota>s os res)))
                 \<longrightarrow> 
                 (\<sigma>\<^sub>0 \<Turnstile> (os \<leftarrow> mbind \<iota>s SUT; return (conf \<iota>s os res))))"

subsection{* Inclusion Test Refinements *}

definition incl_ref :: "('\<iota> \<Rightarrow> ('o, '\<sigma>)MON\<^sub>S\<^sub>E) \<Rightarrow> 
                        '\<sigma> set \<Rightarrow> (* state invariant *)
                        '\<iota> list set \<Rightarrow> (* coverage or test-purpose *) 
                       ('\<iota> \<Rightarrow> ('o, '\<sigma>)MON\<^sub>S\<^sub>E) \<Rightarrow> bool"   
                       ("_ \<sqsubseteq>\<^sub>I\<^sub>\<langle>_,_\<^sub>\<rangle> _" [100,100,100,100]101)
where "(S \<sqsubseteq>\<^sub>I\<^sub>\<langle>Init,CC\<^sub>\<rangle> I) = (S \<sqsubseteq>\<^sub>\<langle>Init,CC,(\<lambda> is os x. length is = length os \<and> os=x)\<^sub>\<rangle> I)"


lemma inclusion_test_I : 
       "(\<And>\<sigma>\<^sub>0 \<iota>s res.
            \<sigma>\<^sub>0 \<in> Init \<Longrightarrow>
            \<iota>s \<in> CC \<Longrightarrow>
            \<sigma>\<^sub>0 \<Turnstile> ( os \<leftarrow> mbind\<^sub>F\<^sub>a\<^sub>i\<^sub>l\<^sub>S\<^sub>a\<^sub>v\<^sub>e \<iota>s S; unit\<^sub>S\<^sub>E (length \<iota>s = length os \<and> os = res))
         \<Longrightarrow>
            \<sigma>\<^sub>0 \<Turnstile> ( os \<leftarrow> mbind\<^sub>F\<^sub>a\<^sub>i\<^sub>l\<^sub>S\<^sub>a\<^sub>v\<^sub>e \<iota>s I;  unit\<^sub>S\<^sub>E (length \<iota>s = length os \<and> os = res)))
         \<Longrightarrow> (S \<sqsubseteq>\<^sub>I\<^sub>\<langle>Init,CC\<^sub>\<rangle> I)"
unfolding incl_ref_def monadic_test_refinement_def
by auto

lemma inclusion_test_I_opt : 
       "(\<And>\<sigma>\<^sub>0 \<iota>s res.
            \<sigma>\<^sub>0 \<in> Init \<Longrightarrow>
            \<iota>s \<in> CC \<Longrightarrow>
            \<sigma>\<^sub>0 \<Turnstile> ( os \<leftarrow> mbind\<^sub>F\<^sub>a\<^sub>i\<^sub>l\<^sub>S\<^sub>t\<^sub>o\<^sub>p \<iota>s S; unit\<^sub>S\<^sub>E (os = res))
         \<Longrightarrow>
            \<sigma>\<^sub>0 \<Turnstile> ( os \<leftarrow> mbind\<^sub>F\<^sub>a\<^sub>i\<^sub>l\<^sub>S\<^sub>t\<^sub>o\<^sub>p \<iota>s I; unit\<^sub>S\<^sub>E (os = res)))
         \<Longrightarrow> (S \<sqsubseteq>\<^sub>I\<^sub>\<langle>Init,CC\<^sub>\<rangle> I)"
apply(rule inclusion_test_I) 
apply(subst Monads.mbindFSave_vs_mbindFStop)
apply(subst (asm) Monads.mbindFSave_vs_mbindFStop)
by(auto)



subsection{* Inclusion Test Refinements with Abort *}

text{* The abort scenario allows operations to fail, so violations
       to input-enabledness are permitted. The model assumes that a particular
       abort-semantics is respected: the operation is assumed to fail explicitly,
       \ie{} observably by the tester, and to leave the state unchanged. *}
       

definition incl_aborts_ref :: "('\<iota> \<Rightarrow> ('o, '\<sigma>)MON\<^sub>S\<^sub>E) \<Rightarrow> 
                        '\<sigma> set \<Rightarrow> (* state invariant *)
                        '\<iota> list set \<Rightarrow> (* coverage or test-purpose *) 
                       ('\<iota> \<Rightarrow> ('o, '\<sigma>)MON\<^sub>S\<^sub>E) \<Rightarrow> bool"   
                       ("_ \<sqsubseteq>\<^sub>I\<^sub>A\<^sub>\<langle>_,_\<^sub>\<rangle> _" [100,100,100,100]101)
where "(S \<sqsubseteq>\<^sub>I\<^sub>A\<^sub>\<langle>Inv,IS\<^sub>\<rangle> I) = (S \<sqsubseteq>\<^sub>\<langle>Inv,IS,(\<lambda> is os x. os=x)\<^sub>\<rangle> I)"


(* TODO : Deadlock Refinement *)

(* TODO : Monadic IOCO *)


end
