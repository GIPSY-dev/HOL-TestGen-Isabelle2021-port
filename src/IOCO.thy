(*****************************************************************************
 * HOL-TestGen --- theorem-prover based test case generation
 *                 http://www.brucker.ch/projects/hol-testgen/
 *                                                                            
 * IOCO --- formalizing the IOCO theory
 * This file is part of HOL-TestGen.
 *
 * Copyright (c) 2005-2007 ETH Zurich, Switzerland
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
(* $Id: IOCO.thy 8455 2009-04-08 07:58:38Z wolff $ *)

chapter {* Basic Testing Setup *}

theory IOCO imports Main begin

section{* A Bit of IOCO Theory *}
text{* See Jan Tretmanns, Axel Belinfante: Automatic Testing with Formal
       Methods. We follow more or less the notation here, but are more
       detailed wrt. concepts such as ``initial states'' which are part of
       the concept of a transition system. *}


text{* Transition systems and IO-Transition Systems *}

record ('\<alpha>, '\<sigma>) TS =
   init :: "'\<sigma> set"
   trans :: "('\<sigma>\<times>'\<alpha>\<times>'\<sigma>) set"

type_synonym ('\<iota>,'o,'\<sigma>) io_lts = "('\<iota> + 'o,'\<sigma>) TS"



inductive_set mult :: "('\<alpha>, '\<sigma>) TS \<Rightarrow> ('\<sigma> \<times> '\<alpha> list \<times> '\<sigma>) set"
for TS :: "('\<alpha>, '\<sigma>) TS"
where refl: "(s,[],s) \<in> mult(TS)"
    | step: "\<lbrakk> (s,a,s') \<in> (trans TS); (s',R,s'') \<in> mult(TS)\<rbrakk> \<Longrightarrow> (s,a#R,s'') \<in> mult(TS)"   

definition  Straces :: "('\<alpha>,'\<sigma>) TS \<Rightarrow> '\<alpha> list set" where
           "Straces TS \<equiv> {l. \<exists> \<sigma>\<^sub>0 \<in>(init TS). \<exists> s'. (\<sigma>\<^sub>0,l,s') \<in> mult(TS)}"
definition  after   :: "[('\<alpha>,'\<sigma>) TS, '\<alpha> list] \<Rightarrow> '\<sigma> set"  (infixl "after" 100) where
           "TS after l \<equiv> {s' . \<exists> \<sigma>\<^sub>0 \<in>(init TS). (\<sigma>\<^sub>0,l,s') \<in> mult(TS)}"
           (* again, we make the set of initial states explicit here *)
           
definition  out     :: "[('\<iota>,'o ,'\<sigma>) io_lts,'\<sigma> set] \<Rightarrow> ('o ) set" where
           "out TS ss \<equiv> {a. \<exists> s \<in> ss. \<exists> s'. (s,Inr a,s') \<in> (trans TS)}" 
 
definition  ioco    :: "[('\<iota>,'o ,'\<sigma>)io_lts,('\<iota>,'o ,'\<sigma>)io_lts] \<Rightarrow> bool" (infixl "ioco" 200) where
           "i ioco s \<equiv> (\<forall> t \<in> Straces(s). out i (i after t) \<subseteq> out s (s after t))"



(* The following notation is based on a concrete ts. *)
consts  ts   :: "('\<alpha>, '\<sigma>) TS" 
(* underspecified *)
        

syntax "_ts" :: "['\<sigma>,'\<alpha>,'\<sigma>] \<Rightarrow> bool" ("_ --<_>--> _" [0,0,60] 60)

syntax (xsymbols)
  "_tc" :: "['\<sigma>,'\<alpha>,'\<sigma>] \<Rightarrow> bool" ("_ --<_>\<longrightarrow> _" [0,0,60] 60)

syntax "_tsm" :: "['\<sigma>,'\<alpha>,'\<sigma>] \<Rightarrow> bool" ("_ ==<_>==> _" [0,0,60] 60)

syntax (xsymbols)
  "_tc," :: "['\<sigma>,'\<alpha>,'\<sigma>] \<Rightarrow> bool" ("_ =<_>\<Rightarrow> _" [0,0,60] 60)

translations  "s --<c>--> s'" == "(s,c,s') \<in> CONST ts"

text{* Purpose: Prove under which conditions Mfold-Test is equivalent
       to ioco, i.e. under which conditions do we actually test ioco.
       I foresee two problems:
       \begin{enumerate}
       \item \textbf{Quiescense} IOCO theory assumes in the notion of
             output elements "quit actions" $\delta$ which were treated 
             as "non-observable" conceptually. Actually, in our testing approach, 
             we will assume that termination of a program under test is
             observable, so the test harness will always at least deliver
             "None" (representing $\delta$).
       \item \textbf{Deep Nondeterminism}. IOCO theory assumes the possibilty
             of a branching of the LTS whose concequences can be observed
             in terms of output actions much later; i.e. there are transitions
             such as $(s,a,s') \isasymin (snd TS)$ and $(s,a,s'') \isasymin (snd TS)$
             with $s' \isasymnoteq s''$.
       \item \textbf{IO Nondeterminism}. A system under test should always
             accept one (possibly trivial) input and produce an output; there
             should be no possibility for it to decide non-deterministically
             to produce input or output.
       \end{enumerate}

       \textbf{Conjecture}: Our Mfold-Testing corresponds exactly to IOCO testing
             if the underlying transition systems are deterministic and 
             quiescence is observable.
*}  
       

end
