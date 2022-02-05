(*****************************************************************************
 * HOL-TestGen --- theorem-prover based test case generation
 *                 http://www.brucker.ch/projects/hol-testgen/
 *                                                                            
 * Observers.thy --- the base testing theory for reactive sequence testing.
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

chapter {* Observers managing Abstract State*}

theory Observers imports Monads
begin 


section{* IO-stepping Function Transfomers *}

text{* The following adaption combinator converts an input-output
   program under test of type: $\iota \Rightarrow \sigma
   \rightharpoonup o \times \sigma$ with program state $\sigma$ into a
   state transition program that can be processed by mbind.  The key
   idea to turn mbind into a test-driver for a reactive system is by
   providing an internal state $\sigma'$, managed by the test driver,
   and external, problem-specific functions ``rebind'' and
   ``substitute'' that operate on this internal state. For example,
   this internal state can be instantiated with an environment $var
   \rightharpoonup value$. The output (or parts of it) can then be
   bound to vars in the environment.  In contrast, substitute can then
   explicit substitute variables occuring in value representations
   into pure values, e.g. is can substitue $c~("X")$ into $c~3$
   provided the environment contained the map with $X \leadsto 3$. *}

text{* The state of the test-driver consists of two parts: the state
   of the observer (or: adaptor) $\sigma$ and the internal state $\sigma'$ of the
   the step-function of the system under test $ioprog$ is allowed to use. *} 

definition observer :: "['\<sigma> \<Rightarrow> 'o \<Rightarrow> '\<sigma>, '\<sigma> \<Rightarrow> '\<iota> \<Rightarrow> '\<iota>, '\<sigma>\<times>'\<sigma>' \<Rightarrow> '\<iota> \<Rightarrow> 'o \<Rightarrow> bool]
                       \<Rightarrow>  ('\<iota> \<Rightarrow> '\<sigma>' \<rightharpoonup> 'o \<times>'\<sigma>') 
                       \<Rightarrow>  ('\<iota> \<Rightarrow> ('\<sigma>\<times>'\<sigma>' \<rightharpoonup> '\<sigma>\<times>'\<sigma>'))"

where    "observer rebind substitute postcond ioprog  =
          (\<lambda> input. (\<lambda> (\<sigma>, \<sigma>'). let input'= substitute \<sigma> input in 
                                 case ioprog input' \<sigma>' of
                                    None \<Rightarrow> None  (* ioprog failure - eg. timeout ... *)  
                                  | Some (output, \<sigma>''') \<Rightarrow> let \<sigma>'' = rebind \<sigma> output in
                                                          (if postcond (\<sigma>'',\<sigma>''') input' output
                                                          then Some(\<sigma>'', \<sigma>''')
                                                          else None (* postcond failure *) )))"  

text{* The subsequent $observer$ version is more powerful: it admits also preconditions
of $ioprog$, which make reference to the observer state $\sigma_{obs}$. The observer-state
may contain an environment binding values to explicit variables. In such a scenario, the 
$precond\_solve$ may consist of a \emph{solver} that constructs a solution from
\begin{enumerate}
\item this environment,
\item the observable state of the $ioprog$,
\item the abstract input
 (which may be related to a precondition which contains references to explicit
 variables)
\end{enumerate}
such that all the explicit variables contained in the preconditions and the
explicit variables in the abstract input are substituted against values
that make the preconditions true. The values must be stored in the
environment and are reported in the observer-state $\sigma_{obs}$. 
*}

definition observer1 :: "['\<sigma>_obs \<Rightarrow> 'o_c \<Rightarrow> '\<sigma>_obs, 
                         '\<sigma>_obs \<Rightarrow> '\<sigma> \<Rightarrow> '\<iota>_a \<Rightarrow> ('\<iota>_c \<times> '\<sigma>_obs), 
                         '\<sigma>_obs \<Rightarrow> '\<sigma> \<Rightarrow> '\<iota>_c \<Rightarrow> 'o_c \<Rightarrow> bool] 
                       \<Rightarrow>  ('\<iota>_c \<Rightarrow> ('o_c, '\<sigma>)MON\<^sub>S\<^sub>E) 
                       \<Rightarrow>  ('\<iota>_a \<Rightarrow> ('o_c, '\<sigma>_obs \<times>'\<sigma>)MON\<^sub>S\<^sub>E) "

where     "observer1 rebind precond_solve postcond ioprog  =
          (\<lambda> in_a. (\<lambda> (\<sigma>_obs, \<sigma>). let (in_c,\<sigma>_obs') = precond_solve \<sigma>_obs \<sigma> in_a  
                                  in  case ioprog in_c \<sigma> of
                                          None \<Rightarrow> None  (* ioprog failure - eg. timeout ... *)  
                                        | Some (out_c, \<sigma>') \<Rightarrow>(let \<sigma>_obs'' = rebind \<sigma>_obs' out_c 
                                                              in if postcond \<sigma>_obs'' \<sigma>' in_c out_c
                                                                 then Some(out_c, (\<sigma>_obs', \<sigma>'))
                                                                 else None (* postcond failure *) )))"  


definition observer2 :: "['\<sigma>_obs \<Rightarrow> 'o_c \<Rightarrow> '\<sigma>_obs, '\<sigma>_obs \<Rightarrow> '\<iota>_a \<Rightarrow> '\<iota>_c, '\<sigma>_obs \<Rightarrow> '\<sigma> \<Rightarrow> '\<iota>_c \<Rightarrow> 'o_c \<Rightarrow> bool] 
                       \<Rightarrow>  ('\<iota>_c \<Rightarrow> ('o_c, '\<sigma>)MON\<^sub>S\<^sub>E) 
                       \<Rightarrow>  ('\<iota>_a \<Rightarrow> ('o_c, '\<sigma>_obs \<times>'\<sigma>)MON\<^sub>S\<^sub>E) "

where    "observer2 rebind substitute postcond ioprog  =
          (\<lambda> in_a. (\<lambda> (\<sigma>_obs, \<sigma>). let in_c = substitute \<sigma>_obs in_a  
                                   in  case ioprog in_c \<sigma> of
                                          None \<Rightarrow> None  (* ioprog failure - eg. timeout ... *)  
                                        | Some (out_c, \<sigma>') \<Rightarrow>(let \<sigma>_obs' = rebind \<sigma>_obs out_c 
                                                              in if postcond \<sigma>_obs' \<sigma>' in_c out_c
                                                                 then Some(out_c, (\<sigma>_obs', \<sigma>'))
                                                                 else None (* postcond failure *) )))"  

text{* Note that this version of the observer is just a
monad-transformer; it transforms the i/o stepping function $ioprog$
into another stepping function, which is the combined sub-system
consisting of the observer and, for example, a program under test
$\PUT$. The observer takes the \emph{abstract} input $in_a$,
substitutes explicit variables in it by concrete values stored by its
own state $\sigma_{obs}$ and constructs \emph{concrete} input $in_c$,
runs $ioprog$ in this context, and evaluates the return: the concrete
output $out_c$ and the successor state $\sigma'$ are used to extract
from concrete output concrete values and stores them inside its own
successor state $\sigma_{obs}'$. Provided that a post-condition is
passed succesfully, the output and the combined successor-state is
reported as success.

Note that we made the following testability assumptions:
\begin{enumerate}
\item $ioprog$ behaves wrt. to the reported state and input as a function, i.e. it behaves
      deterministically, and
\item it is not necessary to destinguish internal failure and post-condition-failure.
      (Modelling Bug? This is superfluous and blind featurism ... One could do this by 
       introducing an own "weakening"-monad endo-transformer.)
\end{enumerate}

*} 

text{* observer2 can actually be decomposed into two combinators - one
dealing with the management of explicit variables and one that tackles 
post-conditions. *}

definition observer3 :: "['\<sigma>_obs \<Rightarrow> 'o \<Rightarrow> '\<sigma>_obs, '\<sigma>_obs \<Rightarrow> '\<iota>_a \<Rightarrow> '\<iota>_c] 
                       \<Rightarrow>  ('\<iota>_c \<Rightarrow> ('o, '\<sigma>)MON\<^sub>S\<^sub>E) 
                       \<Rightarrow>  ('\<iota>_a \<Rightarrow> ('o, '\<sigma>_obs \<times>'\<sigma>)MON\<^sub>S\<^sub>E) "

where     "observer3 rebind substitute ioprog  =
          (\<lambda> in_a. (\<lambda> (\<sigma>_obs, \<sigma>). 
                let in_c = substitute \<sigma>_obs in_a  
                in  case ioprog in_c \<sigma> of
                       None \<Rightarrow> None  (* ioprog failure - eg. timeout ... *) 
                     | Some (out_c, \<sigma>') \<Rightarrow>(let \<sigma>_obs' = rebind \<sigma>_obs out_c 
                                           in  Some(out_c, (\<sigma>_obs', \<sigma>')) )))"  



definition observer4 :: "['\<sigma> \<Rightarrow> '\<iota> \<Rightarrow> 'o \<Rightarrow> bool] 
                       \<Rightarrow>  ('\<iota> \<Rightarrow> ('o, '\<sigma>)MON\<^sub>S\<^sub>E) 
                       \<Rightarrow>  ('\<iota> \<Rightarrow> ('o, '\<sigma>)MON\<^sub>S\<^sub>E)"

where     "observer4 postcond ioprog  =
          (\<lambda> input. (\<lambda> \<sigma>. case ioprog input \<sigma> of
                            None \<Rightarrow> None  (* ioprog failure - eg. timeout ... *)  
                          | Some (output, \<sigma>') \<Rightarrow> (if postcond \<sigma>' input output
                                                  then Some(output, \<sigma>')
                                                  else None (* postcond failure *) )))"  

text{* The following lemma explains the relationsship between $observer2$ and the
decoposed versions  $observer3$ and $observer4$. The full equality does not hold - 
the reason is that the two kinds of preconditions are different in a subtle way:
the postcondition may make reference to the abstract state. (See our example 
\verb+Sequence_test+ based on a symbolic environment in the observer state.)
If the postcondition does not do this, they are equivalent. *}
 
find_theorems name:"prod" name:"case" name:"beta"
lemma observer_decompose: 
  " observer2 r s (\<lambda> x. pc) io = (observer3 r s (observer4 pc io))"
    apply(rule ext, rule ext)
    apply(auto simp: observer2_def observer3_def 
                     observer4_def Let_def case_prod_beta)
    apply(case_tac "io (s a x) b", auto)
done

end
