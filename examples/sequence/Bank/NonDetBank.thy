(*****************************************************************************
 * HOL-TestGen --- theorem-prover based test case generation
 *                 http://www.brucker.ch/projects/hol-testgen/
 *
 * NonDetBank.thy --- an BirthdayBook inspired, elementary
 *              example for sequence testing based on a state deterministic
 *              specification.
 *
 * This file is part of HOL-TestGen.
 *
 * Copyright (c) 2009-2016 University Paris-Sud, France
 *               2009-2015 Achim D. Brucker, Germany
 *               2016      The University of Sheffield, UK
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

chapter {* A Simple Non-Deterministic Bank Model *}
theory  
  NonDetBank
imports 
   Testing
begin

declare [[testgen_profiling]]

text{* This testing scenario is a modification of the Bank example.
The purpose is to explore specifications which are nondetermistic,
but at least $\sigma$-deterministic,
i.e. from the observable output, the internal state can be constructed
(which paves the way for symbolic executions based on the specification). 
 *}

text{* The state of our bank is just modeled by a map from
client/account information to the balance. *}
type_synonym client = string

type_synonym account_no = int

type_synonym register = "(client \<times> account_no) \<rightharpoonup> int"


subsubsection{* Operation definitions *}

text {* We use a similar setting as for the Bank example ---
with one minor modification: the withdraw operation gets
a non-deterministic behaviour: it may withdraw any amount
between 1 and the demanded amount.

\begin{verbatim}
op deposit (c : client, no : account_no, amount:nat) : unit
pre  (c,no) : dom(register)
post register'=register[(c,no) := register(c,no) + amount]

op balance (c : client, no : account_no) : int
pre  (c,no) : dom(register)
post register'=register and result = register(c,no)

op withdraw(c : client, no : account_no, amount:nat) : nat
pre  (c,no) : dom(register) and register(c,no) >= amount
post result <= amount and
     register'=register[(c,no) := register(c,no) - result]
\end{verbatim}
*}


text{* Interface normalization turns this interface into the
following input type: *}

datatype in_c = deposit client account_no nat
              | withdraw client account_no nat
              | balance client account_no

datatype out_c = depositO| balanceO nat | withdrawO nat

fun    precond :: "register \<Rightarrow> in_c \<Rightarrow> bool"
where "precond \<sigma> (deposit c no m) = ((c,no) \<in> dom \<sigma>)"
|     "precond \<sigma> (balance c no) = ((c,no) \<in> dom \<sigma>)"
|     "precond \<sigma> (withdraw c no m) = ((c,no) \<in> dom \<sigma> \<and> (int m) \<le> the(\<sigma>(c,no)))"

fun    postcond :: "in_c \<Rightarrow> register \<Rightarrow> (out_c \<times> register) set"
where "postcond (deposit c no m) \<sigma> =
            ({ (n,\<sigma>'). (n = depositO \<and> \<sigma>'=\<sigma>((c,no)\<mapsto> the(\<sigma>(c,no)) + int m))})"
|      "postcond (balance c no) \<sigma> =
         ({ (n,\<sigma>'). (\<sigma>=\<sigma>' \<and> (\<exists> x. balanceO x = n \<and> x = nat(the(\<sigma>(c,no)))))})"
|      "postcond (withdraw c no m) \<sigma> =
         ({ (n,\<sigma>'). (\<exists> x\<le>m. n = withdrawO x \<and> \<sigma>'=\<sigma>((c,no)\<mapsto> the(\<sigma>(c,no)) - int x))})"



subsubsection{* Proving Symbolic Execution Rules for the Abstractly 
               Constructed Program *}

text{* Using the Operators \verb+impl+ and \verb+strong_impl+, we can 
synthesize an abstract program right away from the specification, i.e. the pair 
of pre and  postcondition defined above. Since this program is even 
deterministic, we derive a set of symbolic execution rules used in the test case 
generation process which will produce symbolic results against which the PUT can 
be compared in the test driver. *}

definition implementable :: "['\<sigma> \<Rightarrow> '\<iota> \<Rightarrow> bool,'\<iota> \<Rightarrow> ('o,'\<sigma>)MON\<^sub>S\<^sub>B] \<Rightarrow> bool"
where     "implementable pre post =(\<forall> \<sigma> \<iota>. pre \<sigma> \<iota> \<longrightarrow>(\<exists> out \<sigma>'. (out,\<sigma>') \<in> post \<iota> \<sigma> ))"


lemma precond_postcond_implementable: 
     "implementable precond postcond"
apply(auto simp: implementable_def)
apply(case_tac "\<iota>", simp_all)
apply auto
done


text{* The following lemmas reveal that this "constructed" program is actually
(due to determinism of the spec) *}

lemma impl_1:
     "strong_impl precond postcond (deposit c no m) = 
      (\<lambda>\<sigma> . if (c, no) \<in> dom \<sigma>
           then Some(depositO,\<sigma>((c, no) \<mapsto> the (\<sigma> (c, no)) + int m))
           else None)"
by(rule ext, auto simp: strong_impl_def )



lemma valid_both_spec1[simp]:
"(\<sigma> \<Turnstile> (s \<leftarrow> mbind ((deposit c no m)#S) (strong_impl precond postcond); 
                    return (P s))) = 
    (if (c, no) \<in> dom \<sigma>
     then (\<sigma>((c, no) \<mapsto> the (\<sigma> (c, no)) + int m) )\<Turnstile> (s \<leftarrow> mbind S (strong_impl precond postcond); 
                        return (P (depositO#s)))
     else (\<sigma> \<Turnstile> (return (P []))))"
by(auto simp: exec_mbindFSave impl_1)


lemma impl_2:
     "strong_impl precond postcond (balance c no) = 
      (\<lambda>\<sigma>. if (c, no) \<in> dom \<sigma>
           then Some(balanceO(nat(the (\<sigma> (c, no)))),\<sigma>)
           else None)"
by(rule ext, auto simp: strong_impl_def)

lemma valid_both_spec2 [simp]:
"(\<sigma> \<Turnstile> (s \<leftarrow> mbind ((balance c no)#S) (strong_impl precond postcond); 
                    return (P s))) = 
    (if (c, no) \<in> dom \<sigma>
     then (\<sigma> \<Turnstile> (s \<leftarrow> mbind S (strong_impl precond postcond); 
                        return (P (balanceO(nat(the (\<sigma> (c, no))))#s))))
     else (\<sigma> \<Turnstile> (return (P []))))"
by(auto simp: exec_mbindFSave impl_2)

text{* So far, no problem; however, so far, everything was deterministic. 
The following key-theorem does not hold: 
*}

lemma impl_3:
     "strong_impl precond postcond (withdraw c no m) = 
      (\<lambda>\<sigma>. if (c, no) \<in> dom \<sigma> \<and> (int m) \<le> the(\<sigma>(c,no)) \<and> x \<le> m
           then Some(withdrawO x,\<sigma>((c, no) \<mapsto> the (\<sigma> (c, no)) - int x))
           else None)"
oops
text{*This also breaks our deterministic approach to compute
the sequence aforehand and to run the test of PUT against this sequence. 

However, we can give an acceptance predicate (an automaton) for correct behaviour
of our PUT: *}

fun     accept :: "(in_c list \<times> out_c list \<times> int) \<Rightarrow> bool"
where   "accept((deposit c no n)#S,depositO#S', m) = accept (S,S', m + (int n))"
     |  "accept((withdraw c no n)#S, (withdrawO k)#S',m) = (k \<le> n \<and> accept (S,S', m - (int k)))"
     |  "accept([balance c no], [balanceO n], m) = (int n = m)"
     |  "accept(a,b,c) = False"


text{* This format has the advantage *}

text{* TODO: Work out foundation. accept works on an abstract state
(just one single balance of a user), while PUT works on the (invisible) 
concrete state. A data-refinement is involved, and it has to be established
why it is correct.
*}

subsubsection{* Test Specifications 

*}
fun test_purpose :: "[client, account_no, in_c list] \<Rightarrow> bool"
where
  "test_purpose c no [] = False"
| "test_purpose c no (a#R) = (case R of 
                               [] \<Rightarrow> a = balance c no
                              | a'#R' \<Rightarrow> (((\<exists> m. a = deposit c no m) \<or> 
                                          (\<exists> m. a = withdraw c no m)) \<and>
                                          test_purpose c no R))"



test_spec test_balance:
assumes account_defined: "(c,no) \<in> dom \<sigma>\<^sub>0" 
and     test_purpose   : "test_purpose c no \<iota>s"
shows  " \<sigma>\<^sub>0 \<Turnstile> (os \<leftarrow> mbind \<iota>s PUT; return (accept(\<iota>s, os, the(\<sigma>\<^sub>0 (c,no)))))"
apply(insert (* store_finite *)  account_defined test_purpose)
apply(gen_test_cases "PUT" split: HOL.if_split_asm)
(* some massage by hand ... should be automated at some point ...*)
mk_test_suite "nbank"

declare [[testgen_iterations=0]]
gen_test_data "nbank"
(*
thm nbank.concrete_tests
*)
end







