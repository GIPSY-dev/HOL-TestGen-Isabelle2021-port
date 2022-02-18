(*****************************************************************************
 * HOL-TestGen --- theorem-prover based test case generation
 *                 http://www.brucker.ch/projects/hol-testgen/
 *
 * MyKeOS.thy --- a Study for OS opertions, modelling atomic actions
 *                for sequence testing based on a 
 *                deterministic specification.
 *
 * This file is part of HOL-TestGen.
 *
 * Copyright (c) 2016 Univ. Paris-Sud, France
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

chapter{* The MyKeOS Case Study *}

theory  MyKeOS
imports 
   "Testing"
begin
(*
declare [[testgen_profiling]]
*)

text{* This example is drawn from the operating system testing domain; it is a rough abstraction
of PiKeOS and explains the underlying techniques of this particular case study on a small example.
The full paper can be found under \cite{DBLP:conf/vstte/BruckerHNW15}. *}

 
text{* This is a fun-operating system --- closely following the Bank example ---
intended to explain the principles of symbolic execution used in our PikeOS study.

Moreover, in this scenario, we assume that the system under test is
deterministic.
 *}

text{* The state of a thread (belonging to a task, \ie{} a Unix/PosiX like ``process'' 
just modeled by a map from task-id/thread-id information to the number of a resource
(a communication channel descriptor, for example) that was allocated to a thread. *}
type_synonym task_id = int

type_synonym thread_id = int

type_synonym thread_local_var_tab = " thread_id \<rightharpoonup> int"


subsubsection{* Operation definitions *}

text {* A standard, JML or OCL or VCC like interface specification
might look like:

\begin{verbatim}

Init:  forall (c,no) : dom(data_base::thread_local_var_tab). data_base(c,no)>=0

op alloc (c : task_id, no : thread_id, amount:nat) : unit
pre  (c,no) : dom(data_base)
post data_base'=data_base[(c,no) := data_base(c,no) + amount]

op release(c : task_id, no : thread_id, amount:nat) : unit
pre  (c,no) : dom(data_base) and data_base(c,no) >= amount
post data_base'=data_base[(c,no) := data_base(c,no) - amount]

op status (c : task_id, no : thread_id) : int
pre  (c,no) : dom(data_base)
post data_base'=data_base and result = data_base(c,no)


\end{verbatim}

*}



text{* Interface normalization turns this interface into the following input type: *}


datatype in_c   = send    thread_id thread_id nat
                | rec     thread_id thread_id nat
                | status  thread_id

datatype in\<^sub>f\<^sub>c    = send\<^sub>f\<^sub>c   thread_id thread_id nat
                | rec\<^sub>f\<^sub>c     thread_id thread_id nat
                | alloc\<^sub>f\<^sub>c   thread_id nat
                | release\<^sub>f\<^sub>c thread_id nat
                | stat\<^sub>f\<^sub>c    thread_id
              
typ "MyKeOS.in_c"

datatype out_c = send_ok | rec_ok | status_ok nat 
datatype out\<^sub>f\<^sub>c = send_ok\<^sub>f\<^sub>c | rec_ok\<^sub>f\<^sub>c |  alloc_ok\<^sub>f\<^sub>c | release_ok\<^sub>f\<^sub>c | stat_ok\<^sub>f\<^sub>c nat 

fun    precond :: "thread_local_var_tab \<Rightarrow> in_c \<Rightarrow> bool"
where "precond \<sigma> (send tid tid' m) = (tid \<in> dom \<sigma>  \<and> tid' \<in> dom \<sigma>  \<and> (int m) \<le> the(\<sigma> tid))"
    | "precond \<sigma> (rec tid tid' m) = (tid \<in> dom \<sigma> \<and> tid' \<in> dom \<sigma>)"
    | "precond \<sigma> (status tid) = (tid \<in> dom \<sigma>)"


fun    precond\<^sub>f\<^sub>c :: "thread_local_var_tab \<Rightarrow> in\<^sub>f\<^sub>c \<Rightarrow> bool"
where "precond\<^sub>f\<^sub>c \<sigma>  (send\<^sub>f\<^sub>c tid tid' m) = (tid \<in> dom \<sigma>  \<and> tid' \<in> dom \<sigma> \<and> (int m) \<le> the(\<sigma> tid))"
    | "precond\<^sub>f\<^sub>c \<sigma>  (rec\<^sub>f\<^sub>c tid tid' m) = (tid \<in> dom \<sigma> \<and> tid' \<in> dom \<sigma>)"
    | "precond\<^sub>f\<^sub>c \<sigma>  (alloc\<^sub>f\<^sub>c tid m) = (tid \<in> dom \<sigma>)"
    | "precond\<^sub>f\<^sub>c \<sigma>  (release\<^sub>f\<^sub>c tid m) = (tid \<in> dom \<sigma>)"
    | "precond\<^sub>f\<^sub>c \<sigma>  (stat\<^sub>f\<^sub>c tid) = (tid \<in> dom \<sigma>)"




fun    postcond :: "in_c \<Rightarrow> thread_local_var_tab \<Rightarrow> (out_c \<times> thread_local_var_tab) set"
where "postcond (send tid tid' m) \<sigma> =
         { (n,\<sigma>'). n = send_ok \<and> \<sigma>'=\<sigma>(tid \<mapsto> the(\<sigma> tid) - int m)}"
    | "postcond (rec tid tid' m) \<sigma> =
         { (n,\<sigma>'). (n = rec_ok \<and> \<sigma>'=\<sigma>(tid' \<mapsto> the(\<sigma> tid') + int m))}"
    | "postcond (status tid) \<sigma> =
         { (n,\<sigma>'). (\<sigma>=\<sigma>' \<and> (\<exists> x. status_ok x = n \<and> x = nat(the(\<sigma> tid))))}"


fun    postcond\<^sub>f\<^sub>c :: "in\<^sub>f\<^sub>c \<Rightarrow> thread_local_var_tab \<Rightarrow> (out\<^sub>f\<^sub>c \<times> thread_local_var_tab) set"
where "postcond\<^sub>f\<^sub>c (send\<^sub>f\<^sub>c tid tid' m) \<sigma> =
         { (n,\<sigma>'). n = send_ok\<^sub>f\<^sub>c \<and> \<sigma>'=\<sigma>(tid \<mapsto> the(\<sigma> tid) - int m)}"
    | "postcond\<^sub>f\<^sub>c (rec\<^sub>f\<^sub>c tid tid' m) \<sigma> =
         { (n,\<sigma>'). (n = rec_ok\<^sub>f\<^sub>c \<and> \<sigma>'=\<sigma>(tid' \<mapsto> the(\<sigma> tid') + int m))}"
    | "postcond\<^sub>f\<^sub>c (stat\<^sub>f\<^sub>c tid) \<sigma> =
         { (n,\<sigma>'). (\<sigma>=\<sigma>' \<and> (\<exists> x. stat_ok\<^sub>f\<^sub>c x = n \<and> x = nat(the(\<sigma> tid))))}"



subsubsection{* Constructing an Abstract Program *}

text{* Using the Operators \verb+impl+ and \verb+strong_impl+, we can 
synthesize an abstract program right away from the specification, i.e. the pair 
of pre- and  postcondition defined above. Since this program is even 
deterministic, we derive a set of symbolic execution rules used in the test case 
generation process which will produce symbolic results against which the PUT can 
be compared in the test driver. *}
(*
definition implementable :: "['\<sigma> \<Rightarrow> '\<iota> \<Rightarrow> bool,'\<iota> \<Rightarrow> ('o,'\<sigma>)MON_SB] \<Rightarrow> bool"
where     "implementable pre post =(\<forall> \<sigma> \<iota>. pre \<sigma> \<iota> \<longrightarrow>(\<exists> out \<sigma>'. (out,\<sigma>') \<in> post \<iota> \<sigma> ))"
*)

lemma precond_postcond_implementable: 
     "implementable precond postcond"
apply(auto simp: implementable_def)
apply(case_tac "\<iota>", simp_all)
done

text{* Based on this machinery, it is now possible to construct the system model as the 
       canonical completion of the (functional) specification consisting of pre-  and 
       post-conditions*}

definition "SYS = (strong_impl precond postcond)"

lemma SYS_is_strong_impl : "is_strong_impl precond postcond SYS"
by(simp add: SYS_def is_strong_impl)

thm SYS_is_strong_impl[simplified is_strong_impl_def,THEN spec,of "(send tid tid' m)", simplified]
(*automatic, but logically not strong enough *)

subsubsection{* Proving Symbolic Execution Rules for the  Abstractly Program *}
text{* The following lemmas reveal that this "constructed" program is actually
(due to determinism of the spec): *}

lemma Eps_split_eq' : "(SOME (x', y'). x'= x  \<and> y'= y) = (SOME (x', y'). x = x' \<and> y = y')"
by(rule arg_cong[of _ _ "Eps"], auto)

interpretation send : efsm_det 
                      "precond" "postcond" "SYS" "(send tid tid' m)" "\<lambda>_. send_ok" 
                      "\<lambda> \<sigma>. \<sigma>(tid \<mapsto>  (the(\<sigma> tid) - int m))" "\<lambda> \<sigma>. (tid \<in> dom \<sigma>  \<and> tid' \<in> dom \<sigma>  \<and> (int m) \<le> the(\<sigma> tid))"
               by unfold_locales (auto simp: SYS_def Eps_split_eq')

interpretation receive : efsm_det 
                        "precond" "postcond" "SYS" "(rec tid tid' m)" "\<lambda>_. rec_ok" 
                         "\<lambda> \<sigma>. \<sigma>(tid' \<mapsto>  (the(\<sigma> tid')+int m))" 
                         "\<lambda> \<sigma>.(tid\<in>dom \<sigma> \<and> tid' \<in> dom \<sigma>)"
               by unfold_locales (auto simp: SYS_def Eps_split_eq')

interpretation status : efsm_det 
                       "precond" "postcond" "SYS" "(status tid)" 
                       "\<lambda>\<sigma>. (status_ok (nat(the(\<sigma> tid))))" 
                       "\<lambda> \<sigma>. \<sigma>" "\<lambda> \<sigma>. (tid \<in> dom \<sigma>)"
               by unfold_locales (auto simp: SYS_def Eps_split_eq')




subsection{* Setup *}

text{* Now we close the theory of symbolic execution by \emph{exluding} elementary rewrite
steps on @{term mbind}, \ie{} the rules @{thm mbind.simps(1)} @{thm mbind.simps(2)} *}

declare mbind.simps(1) [simp del]
        mbind.simps(2) [simp del]

text{* Here comes an interesting detail revealing the power of the
approach: The generated sequences still respect the preconditions
imposed by the specification  - in this case, where we are talking about
a \verb$task_id$ for which a defined account exists and for which we will never
produce traces in which we release more money than available on it. *}

subsubsection{* Restricting the Test-Space by Test Purposes *}
text{* We introduce a constraint on the input sequence, in order to limit the test-space
       a little and eliminate logically possible, but irrelevant test-sequences for a specific
       test-purpose. In this case, we narrow down on test-sequences concerning a specific
       \verb$task_id$ @{term c} with a specific bank-account number @{term no}.
       
       We make the (in this case implicit, but as constraint explicitly stated) test hypothesis,
       that the @{term SUT} is correct if it behaves correct for a single \verb$task_id$.
       This boils down to the assumption that they are implemented as atomic transactions
       and interleaved processing does not interfere with a single thread. *}

term "List.member y x"

fun test_purpose :: "[task_id list, in_c list] \<Rightarrow> bool"
where
  "test_purpose R [status tid] = (tid \<in> set R)" 
| "test_purpose R ((send tid tid' m) # S) = (tid \<in> set R  \<and> tid' \<in> set R  \<and> test_purpose R S)"
| "test_purpose R ((rec tid tid' m) # S) = (tid \<in> set R  \<and> tid' \<in> set R  \<and> test_purpose R S)"
| "test_purpose _ _ = False"

(* Definition buggy --- the R list must be separated into two parts, but one can not throw 
   away elements) *)

lemma [simp] : "test_purpose [] a = False" by(induct a, simp_all, case_tac "a1", 
                                                        simp_all, case_tac "a2", simp_all)
lemma [simp] : "test_purpose r [] = False" by simp

lemma [simp] : "test_purpose (tid#R) [a] = ((a = status tid) \<or> test_purpose R [a])"
proof (induct "R" )
  case Nil show ?case by(cases "a", simp_all)
next
  case (Cons a' R') then show ?case  by(cases a, simp_all)
qed


lemma [rule_format,simp,dest] : "test_purpose R (S@[a]) \<longrightarrow> (\<exists> tid \<in> set R. (a = status tid))"
proof (induct S arbitrary: R)
  case Nil then show ?case apply(auto)
                      by (metis in_c.exhaust test_purpose.simps(1) test_purpose.simps(2) 
                          test_purpose.simps(3) test_purpose.simps(4))
next 
  case (Cons a list) show ?case  apply(insert Cons.hyps)
                      by (metis append_Cons hd_Cons_tl in_c.exhaust snoc_eq_iff_butlast 
                                test_purpose.simps(2) test_purpose.simps(3) test_purpose.simps(5))
qed

schematic_goal sdf:"(\<exists> tid \<in> set [1,2,3]. (a = status tid)) = ?X"
apply(rule trans)
apply simp
oops



lemma [simp] : 
 "test_purpose H (a#R) = ((((\<exists>m. \<exists>tid\<in>set H. \<exists>tid'\<in>set H. a = send tid tid' m) \<or> 
                             (\<exists>m. \<exists>tid\<in>set H. \<exists>tid'\<in>set H. a = rec tid tid' m)) 
                            \<and> test_purpose H R) \<or>
                            (R=[] \<and> (\<exists>tid\<in>set H. a = status tid)))"
proof(induct R arbitrary: a) 
  case Nil then show ?case  by(simp,case_tac "a", simp_all)
next
  case (Cons a list aa)   then show ?case by(simp,case_tac "aa", simp_all)
qed


text{* The following scenario checks send-operations to itself *}
lemma exhaust1[simp] : 
 "test_purpose [tid] (a#R) = ((((\<exists>m. a = send tid tid m) \<or> 
                                (\<exists>m. a = rec  tid tid m)) 
                                \<and> test_purpose [tid] R) \<or>
                                (R=[] \<and> (a = status tid)))"
by simp  

lemma exhaust2[simp] : 
 "test_purpose [tid,tid'] (a#R) = ((((\<exists>m. a = send tid tid m) \<or> (\<exists>m. a = send tid' tid' m) \<or>
                                     (\<exists>m. a = send tid tid' m) \<or> (\<exists>m. a = send tid' tid m) \<or>
                                     (\<exists>m. a = rec tid tid' m) \<or> (\<exists>m. a = rec  tid' tid m)  \<or>
                                     (\<exists>m. a = rec tid tid m) \<or> (\<exists>m. a = rec  tid' tid' m)) 
                                     \<and> test_purpose [tid,tid'] R) \<or>
                                   (R=[] \<and> ((a = status tid) \<or> (a = status tid'))))"
by auto


section {* Well-formed traces *}

fun compair :: "in_c \<Rightarrow> in_c \<Rightarrow> bool"
where     "compair (send x y z) (rec x' y' z') = ((x=x') \<and> (y=y') \<and> (z = z'))"  
        | "compair _ _ = False"


definition wf_trace  :: "in_c list \<Rightarrow> bool"
where     "wf_trace t = (\<exists>f. \<forall> n\<in>{0..<length t}. f n \<in>{0..<length t} \<and> 
                                                 f (f n) = n \<and> (* derivable ? *)
                                                 (case (t!n) of
                                                   (send _ _ _) \<Rightarrow>  
                                                              (compair (t!n) (t!(f n)) \<and> f n > n)
                                                 |(rec _ _ _)   \<Rightarrow>  
                                                              (compair (t!n) (t!(f n)) \<and> f n < n)                  
                                                 |(status _)    \<Rightarrow>  (f n) =  n)
                        )"


section {* Misc *}

(* PUT must be a constant for coding conventions ... *)
consts PUT :: "in_c \<Rightarrow> '\<sigma> \<Rightarrow> (out_c \<times> '\<sigma>) option"



end
