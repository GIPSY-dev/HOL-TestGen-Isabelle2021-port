(*****************************************************************************
 * HOL-TestGen --- theorem-prover based test case generation
 *                 http://www.brucker.ch/projects/hol-testgen/
 *
 * MyKeOS.thy  --- an example for a concurrent test scenario.
 *
 * This file is part of HOL-TestGen.
 *
 * Copyright (c) 2009-15 Univ. Paris-Sud, France
 *               2009-15 Achim D. Brucker, Germany
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

chapter{* The MyKeOS ``Traditional'' Data-sequence enumeration approach *}

theory  MyKeOS_test
imports MyKeOS   (* includes Testing *) 
      (*  Code_Integer_Fsharp *)
begin

text{* The purpose of these test-scenarios is to apply the bute-force 
data-exploration approach to a little operation system example. 
It is conceptually very close the the Bank-example, essentially a renaming.
However, the present "data-exploration" based approach is
an interesting intermediate step to the subsequently shown
scenarios based on:
\begin{enumerate}
\item exploration if the interleaving space 
\item optimized exploration if the interleaving space,
      including theory for partial-order reduction. 
\end{enumerate}
*}

declare [[testgen_profiling]]


subsubsection{* The TestGen Setup*} 
text{* The default configuration of \verb$gen_test_cases$ does
\emph{not} descend into sub-type expressions of type constructors (since this is not always
desirable, the choice for the default had been for "non-descent"). This case is relevant here since
@{typ "MyKeOS.in_c list"} has just this structure but we need ways to explore the input sequence
type further. Thus, we need configure, for all test cases, and derivation descendants of the
relusting clauses during splitting, again splitting for all parameters of input type 
@{typ "MyKeOS.in_c"}: *}

set_pre_safe_tac{*
  (fn ctxt => TestGen.ALLCASES(
                  TestGen.CLOSURE (
                      TestGen.case_tac_typ ctxt ["MyKeOS.in_c"]))) 
*}

subsubsection{* The Scenario*}
 
text{* We construct test-sequences for a concrete \verb$task_id$ (implicitely assuming 
that interleaving actions with other \verb$task_id$'s will not influence the system behaviour.
In order to prevent \testgen to perform case-splits over names --- i.e. list of 
characters --- we define it as constant.
*}
(* fixing the init-space a little *)
definition tid\<^sub>0 :: "task_id"    where "tid\<^sub>0 = 0"
definition tid\<^sub>1 :: "task_id"    where "tid\<^sub>1 = 1"



declare[[goals_limit = 500]]
(* declare[[testgen_trace]] *)

subsubsection{* Making my own test-data generation --- temporarily *}
lemma HH : "(A \<and> (A \<longrightarrow> B)) = (A \<and>  B)" by auto

subsubsection{* Some Experiments with nitpick as Testdata Selection Machine. *}

text{* Exists in two formats : General Fail-Safe Tests (which allows for scenarios 
with normal \emph{and} exceptional behaviour; and Fail-Stop Tests, which generates Tests 
only for normal behaviour and correspond to inclusion test refinement. *}

(* Problem : nitpick behaves not very clever in presence of schematic variables. This has to
be filtered before use. *)


lemma H: "((((X586X11506, X587X11507) \<in> dom X588X11508 \<longrightarrow>
         [status_ok (nat (the (X588X11508 (X586X11506, X587X11507))))] = X590X11510 \<and>
         X588X11508 (X586X11506, X587X11507) = Some X589X11509) \<and>
        ((X586X11506, X587X11507) \<notin> dom X588X11508 \<longrightarrow>
         [] = X590X11510 \<and> X588X11508 (X586X11506, X587X11507) = Some X589X11509)))"
nitpick[satisfy,debug]
oops
(* After instantiating the schematic variables by free variables, nitpick behaves fairly well
even for the 2-order variable X588X11508. Without debug option, the time consumption is minimal.*)

lemma H: "(((X586X11506, X587X11507) \<in> dom 
         ([(X586X11506, X587X11507) \<mapsto> X589X11509]) \<longrightarrow>
         [status_ok (nat (the (
         ([(X586X11506, X587X11507) \<mapsto> X589X11509]) (X586X11506, X587X11507))))] = X590X11510 \<and>
         ([(X586X11506, X587X11507) \<mapsto> X589X11509]) (X586X11506, X587X11507) = Some X589X11509) \<and>
        ((X586X11506, X587X11507) \<notin> dom 
         ([(X586X11506, X587X11507) \<mapsto> X589X11509]) \<longrightarrow>
         [] = X590X11510 \<and> ([(X586X11506, X587X11507) \<mapsto> X589X11509]) (X586X11506, X587X11507) = Some X589X11509))"
nitpick[satisfy,debug,timeout=500]
oops
(* Example for grounding / filtering the second order variable. No mesurable positive effect for
   nitpick. (Still could be necessary for good old random_solve *)


text{* In the following, we discuss a test-scenario with error-abort semantics; \ie{} in each
test-case, a sequence may be chosen (by the test data selection) where the \verb$task_id$ has  several
accounts. . . *}
test_spec test_status:
assumes account_def   : "no \<in> dom \<sigma>\<^sub>0 \<and> no' \<in> dom \<sigma>\<^sub>0" 
and     test_purpose  : "test_purpose [no,no'] S"
and     sym_exec_spec : " \<sigma>\<^sub>0 \<Turnstile> (s \<leftarrow> mbind\<^sub>F\<^sub>a\<^sub>i\<^sub>l\<^sub>S\<^sub>a\<^sub>v\<^sub>e S SYS; return (s = x))"
shows                   " \<sigma>\<^sub>0 \<Turnstile> (s \<leftarrow> mbind\<^sub>F\<^sub>a\<^sub>i\<^sub>l\<^sub>S\<^sub>a\<^sub>v\<^sub>e S PUT; return (s = x))"


txt{* Prelude: Massage of the test-theorem --- representing the assumptions of the test explicitely
      in HOL and blocking @{term x} from beeing case-splitted (which complicates the process).*}
apply(rule rev_mp[OF sym_exec_spec])
apply(rule rev_mp[OF account_def])
apply(rule rev_mp[OF test_purpose])
apply(rule_tac x=x in spec[OF allI])

txt{*  Starting the test generation process.*}
(* Variant I :
using[[no_uniformity]]
apply(gen_test_cases 3 1 "PUT" simp:  HH split: HOL.if_split_asm)
txt{* So lets go for a more non-destructive approach: *}
*)
(* Variant II : *)
apply(gen_test_cases 3 1 "PUT")
(* and symbolic execution separately *)
apply(simp_all add:  HH split: HOL.if_split_asm)
mk_test_suite "mykeos_simpleSNXB"



text{* And now the Fail-Stop scenario --- this corresponds exactly to inclusion test. *}
declare Monads.mbind'_bind [simp del]
test_spec test_status2: 
assumes system_def   : "tid \<in> dom \<sigma>\<^sub>0 \<and> tid' \<in> dom \<sigma>\<^sub>0" 
and     test_purpose  : "test_purpose [tid,tid'] S"
and     sym_exec_spec :
       " \<sigma>\<^sub>0 \<Turnstile> (s \<leftarrow> mbind\<^sub>F\<^sub>a\<^sub>i\<^sub>l\<^sub>S\<^sub>t\<^sub>o\<^sub>p S SYS; return (s = x))"
shows  " \<sigma>\<^sub>0 \<Turnstile> (s \<leftarrow> mbind\<^sub>F\<^sub>a\<^sub>i\<^sub>l\<^sub>S\<^sub>t\<^sub>o\<^sub>p S PUT; return (s = x))"
txt{* Prelude: Massage of the test-theorem --- representing the assumptions of the test explicitely
in HOL and blocking @{term x} from beeing case-splitted (which complicates the process).*}
apply(rule rev_mp[OF sym_exec_spec])
apply(rule rev_mp[OF system_def])
apply(rule rev_mp[OF test_purpose])
apply(rule_tac x=x in spec[OF allI])
txt{*  Starting the test generation process.*}
using[[no_uniformity]] (* bug in uniformity *)
apply(gen_test_cases 3 1 "PUT")
txt{* So lets go for a more non-destructive approach: *}
apply simp_all

using[[no_uniformity=false]]    
apply(tactic "TestGen.ALLCASES(TestGen.uniformityI_tac @{context} [\"PUT\"])") 

mk_test_suite "mykeos_simpleNB"

ML{* Isar_Cmd.done_proof; Proof.global_done_proof*}

(* TO DO NEXT: SOLVE Problem with sigma 0. *)
(* TO DO OVERNEXT: Inclusion Test Scenario. *)

subsection{*  Test-Data Generation *}
(*
ML{*Isar_Cmd.done_proof; Proof.global_done_proof*}
ML{* 
local open Proof in

fun conclude_goal ctxt goal propss =
  let
    val thy = Proof_Context.theory_of ctxt;

    val _ =
      Context.subthy_id (Thm.theory_id_of_thm goal, Context.theory_id thy) orelse
        error "Bad background theory of goal state";
    val _ = Thm.no_prems goal orelse error (Proof_Display.string_of_goal ctxt goal);

    fun err_lost () = error ("Lost goal structure:\n" ^ Thm.string_of_thm ctxt goal);

    val th =
      (Goal.conclude (if length (flat propss) > 1 then Thm.close_derivation goal else goal)
        handle THM _ => err_lost ())
      |> Drule.flexflex_unique (SOME ctxt)
      |> Thm.check_shyps ctxt
       |> Thm.check_hyps (Context.Proof ctxt);

    val goal_propss = filter_out null propss;
    val results =
      Conjunction.elim_balanced (length goal_propss) th
      |> map2 Conjunction.elim_balanced (map length goal_propss)
      handle THM _ => err_lost ();
    val _ =
      Unify.matches_list (Context.Proof ctxt) (flat goal_propss) (map Thm.prop_of (flat results))
        orelse error ("Proved a different theorem:\n" ^ Thm.string_of_thm ctxt th);

    fun recover_result ([] :: pss) thss = [] :: recover_result pss thss
      | recover_result (_ :: pss) (ths :: thss) = ths :: recover_result pss thss
      | recover_result [] [] = []
      | recover_result _ _ = err_lost ();
  in recover_result propss results end;

fun generic_qed state =
  let
    val (goal_ctxt, {statement = (_, propss, _), goal, after_qed, ...}) =
      current_goal state;
    val results = tl (conclude_goal goal_ctxt goal propss); (* conclude goal ! ! !*)
  in state |> close_block |> pair (after_qed, (goal_ctxt, results)) end;

end;

Thm.close_derivation
*}
*)
ML{* Thm.close_derivation 
*}
(* thm mykeos_simpleSNXB.test_thm *)

declare [[testgen_iterations=0]]
declare [[testgen_SMT]]          (* switch on Z3 *)
(* usual problems with the random solver - snd order variables like $\sigma_0$
   should be fitered out before an attempt. Iterations must be set to 0 therefore,
   in order to shut up the random solver. Bizarre non-termination in case of 
   presence of snd order variables.
   However, quickcheck and nitpick work fine for this setting. *)
(* We give Z3 access to the definitions that are used by the test theorem *)

declare tid\<^sub>0_def [testgen_smt_facts]
declare tid\<^sub>1_def [testgen_smt_facts]

declare mem_Collect_eq    [testgen_smt_facts]
declare Collect_mem_eq    [testgen_smt_facts]
declare dom_def           [testgen_smt_facts]
declare Option.option.sel [testgen_smt_facts]


gen_test_data "mykeos_simpleSNXB"
print_conc_tests mykeos_simpleSNXB


  
gen_test_data "mykeos_simpleNB"
print_conc_tests mykeos_simpleNB


subsection {* Generating the Test-Driver for an SML and C implementation *}

text{* The generation of the test-driver is non-trivial in this exercise since it is
essentially two-staged: Firstly, we chose to generate an SML test-driver, which is then
secondly, compiled to a C program that is linked to the actual program under test.
Recall that a test-driver consists of four components:
\begin{itemize}
\item \verb+../../../../../harness/sml/main.sml+ the global controller 
      (a fixed element in the library),
\item \verb+../../../../../harness/sml/main.sml+ a statistic evaluation library
      (a fixed element in the library),   
\item \verb+bank_simple_test_script.sml+ the test-script that corresponds merely
      one-to-one to the generated test-data (generated)
\item \verb+bank_adapter.sml+ a hand-written program; in our scenario, it replaces
      the usual (black-box) program under test by SML code, that calls the 
      external C-functions  via a foreign-language interface.
\end{itemize}
*}

text{* On all three levels, the HOL-level, the SML-level, and the C-level, there are
different representations of basic data-types possible; the translation process of data 
to and from the C-code under test has therefore to be carefully designed 
(and the sheer space of options is sometimes a pain in the neck).
Integers, for example, are represented in two ways inside Isabelle/HOL; there is the mathematical
quotient construction and a "numerals" representation providing 'bit-string-representation-behind-
the-scene" enabling relatively efficient symbolic computation. Both representations can be
compiled "natively" to data types in the SML level. By an appropriate configuration, the 
code-generator can map "int" of HOL to three different implementations:
the SML standard library \verb+Int.int+, the native-C interfaced by \verb+Int32.int+, and the
\verb+IntInf.int+ from the multi-precision library \verb+gmp+ underneath the polyml-compiler.
*}

text{* We do a three-step compilation of data-reresentations model-to-model, model-to-SML, 
SML-to-C. *}

text{* A basic preparatory step for the initializing the test-environment to enable
code-generation is: *}
generate_test_script "mykeos_simpleNB"
thm                   mykeos_simpleNB.test_script
generate_test_script "mykeos_simpleSNXB"
(*
text{* In the following, we describe the interface of the SML-program under test, which is 
in our scenario an \emph{adapter} to the C code under test. This is the heart of the
model-to-SML translation.
The the SML-level stubs for the program under test are declared as follows: *}
consts     status_stub :: "thread_id        \<Rightarrow> (int, '\<sigma>)MON\<^sub>S\<^sub>E"
code_const status_stub    (SML "MyKeOSAdapter.status")
consts     alloc_stub  :: "thread_id \<Rightarrow> int \<Rightarrow> (unit, '\<sigma>)MON\<^sub>S\<^sub>E"
code_const alloc_stub     (SML "MyKeOSAdapter.alloc")
consts     release_stub:: "thread_id \<Rightarrow> int \<Rightarrow> (unit, '\<sigma>)MON\<^sub>S\<^sub>E"
code_const release_stub   (SML "MyKeOSAdapter.release")

text{*Note that this translation step prepares already the data-adaption; the type \verb+nat+
is seen as an predicative constraint on integer (which is actually not tested).
On the model-to-model level, we provide a global step function that distributes to
individual interface functions via stubs (mapped via the code generation to SML ...).
This translation also represents uniformly nat by int's.
*}

(* hack : codegenerator does not work for "nat" now ! Therefore an own conversion function:*)
fun    my_nat_conv :: "int \<Rightarrow> nat"
where "my_nat_conv x =(if x <= 0 then 0 else Suc (my_nat_conv(x - 1)))"   

fun   stepAdapter :: "(in_c \<Rightarrow>(out_c, '\<sigma>)MON\<^sub>S\<^sub>E)" 
where "stepAdapter(status tid ) = 
                 (x \<leftarrow> status_stub tid ; return(status_ok (my_nat_conv x)))"
   | "stepAdapter(send tid amount) = 
                 (_ \<leftarrow> alloc_stub thid thid (int amount); return(alloc_ok))"
   | "stepAdapter(rec tid  amount)= 
                 (_ \<leftarrow> release_stub tid thid (int amount); return(release_ok))"

text{* The @{term stepAdapter} function links the HOL-world and establishes the logical link
       to HOL stubs which were mapped by the code-generator to adapter functions in SML (which call 
       internally to C-code inside \verb+bank_adapter.sml+ via a foreign language interface) 
       ... We configure the code-generator to identify the \verb+PUT+ with the generated SML code 
       implicitely defined by the above @{term stepAdapter} definition. *}
 
code_const PUT  (SML    "stepAdapter")

text{* And there we go and generate the \verb+mykeos_simpleNB_test_script.sml+
as well as the \verb+mykeos_simpleSNXB_test_script.sml+: *}
export_code                   stepAdapter mykeos_simpleSNXB.test_script in SML    
module_name TestScript file  "impl/c/mykeos_simpleSNXB_test_script.sml"
export_code                   stepAdapter mykeos_simpleNB.test_script in SML    
module_name TestScript file  "impl/c/mykeos_simpleNB_test_script.sml"
*)


subsection{* More advanced Test-Case Generation Scenarios *}

text{* Exploring a bit the limits ... *}

text{* Rewriting based approach of symbolic execution ... FailSave Scenario *}
test_spec test_status:
assumes account_def   : "(no) \<in> dom \<sigma>\<^sub>0 \<and> (no') \<in> dom \<sigma>\<^sub>0" 
and     test_purpose  : "test_purpose [no,no'] S"
and     sym_exec_spec :
       " \<sigma>\<^sub>0 \<Turnstile> (s \<leftarrow> mbind\<^sub>F\<^sub>a\<^sub>i\<^sub>l\<^sub>S\<^sub>a\<^sub>v\<^sub>e S SYS; return (s = x))"
shows  " \<sigma>\<^sub>0 \<Turnstile> (s \<leftarrow> mbind\<^sub>F\<^sub>a\<^sub>i\<^sub>l\<^sub>S\<^sub>a\<^sub>v\<^sub>e S PUT; return (s = x))"
txt{* Prelude: Massage of the test-theorem --- representing the assumptions of the test explicitely
in HOL and blocking @{term x} from beeing case-splitted (which complicates the process).*}
apply(insert  account_def test_purpose sym_exec_spec)
apply(tactic "TestGen.mp_fy @{context} 1",rule_tac x=x in spec[OF allI])
txt{*  Starting the test generation process.*}
apply(gen_test_cases 3 1 "PUT")
(* Measurements 20.2. Revision 11395
   5 : 1 =>  31 test cases in 7.609 seconds
   6 : 1 =>  63 test cases in 26.977 seconds 
   7 : 1 => 127 test cases in 125.183 seconds
*)
txt{* Symbolic Execution: *}
apply(simp_all add:  HH split: HOL.if_split_asm)
mk_test_suite "mykeos_large"

gen_test_data "mykeos_large"
print_conc_tests mykeos_large


text{* Rewriting based approach of symbolic execution ... FailSave Scenario *}
test_spec test_status:
assumes account_def   : "(no) \<in> dom \<sigma>\<^sub>0 \<and> (no') \<in> dom \<sigma>\<^sub>0" 
and     test_purpose  : "test_purpose [(no),(no')] S"
and     sym_exec_spec : 
       " \<sigma>\<^sub>0 \<Turnstile> (s \<leftarrow> mbind\<^sub>F\<^sub>a\<^sub>i\<^sub>l\<^sub>S\<^sub>t\<^sub>o\<^sub>p S SYS; return (s = x))"
shows  " \<sigma>\<^sub>0 \<Turnstile> (s \<leftarrow> mbind\<^sub>F\<^sub>a\<^sub>i\<^sub>l\<^sub>S\<^sub>t\<^sub>o\<^sub>p S PUT; return (s = x))"
txt{* Prelude: Massage of the test-theorem --- representing the assumptions of the test explicitely
in HOL and blocking @{term x} from beeing case-splitted (which complicates the process).*}
apply(insert (* store_finite *)  account_def test_purpose sym_exec_spec)
apply(tactic "TestGen.mp_fy @{context} 1",rule_tac x=x in spec[OF allI])
txt{*  Starting the test generation process.*}
using [[no_uniformity]] (* To circumvent BUG in uniformityI *)
apply(gen_test_cases 3 1 "PUT")
(* Measurements 20.2. Revision 11395
   5 : 1 => 31 test cases in 3.704 secondso
   6 : 1 => 63 test cases in 5.726 seconds
   7 : 1 => 127 test cases in 25.700 seconds
   8 : 1 => 255 test cases in 119.720 seconds
   9 : 1 => 511 test cases in 755.510 seconds
  10 : 1 => 1023 test cases in 6505.396 seconds
*)
txt{* Symbolic Execution: *}
apply(simp_all add:  HH split: HOL.if_split_asm)
(* test data selection by hand !!! *)
apply(auto)
mk_test_suite "mykeos_large2"

gen_test_data "mykeos_large2"
print_conc_tests mykeos_large2


text{* And now, to compare, elimination based procedures ... *}

declare (* alloc.exec_mbindFSave_If   [simp del] *)
        status.exec_mbindFSave_If  [simp del]
    (*    release.exec_mbindFSave_If [simp del]
        alloc.exec_mbindFStop      [simp del]*)
        status.exec_mbindFStop     [simp del]
(*        release.exec_mbindFStop    [simp del] *)
(*
thm alloc.exec_mbindFSave_E release.exec_mbindFSave_E status.exec_mbindFSave_E
*)
(*
declare exec_mbindFSave_allocE[elim!]
declare exec_mbindFSave_releaseE[elim!]
declare exec_mbindFSave_statusE[elim!]
*)

ML{* open Tactical; *}
test_spec test_status:
assumes account_defined: "(no) \<in> dom \<sigma>\<^sub>0 \<and> (no') \<in> dom \<sigma>\<^sub>0" 
and     test_purpose   : "test_purpose [(no),(no')] S"
and     sym_exec_spec :
       " \<sigma>\<^sub>0 \<Turnstile> (s \<leftarrow> mbind\<^sub>F\<^sub>a\<^sub>i\<^sub>l\<^sub>S\<^sub>t\<^sub>o\<^sub>p S SYS; return (s = x))"
shows  " \<sigma>\<^sub>0 \<Turnstile> (s \<leftarrow> mbind\<^sub>F\<^sub>a\<^sub>i\<^sub>l\<^sub>S\<^sub>t\<^sub>o\<^sub>p S PUT; return (s = x))"  
apply(insert (* store_finite *)  account_defined test_purpose sym_exec_spec)
apply(tactic "TestGen.mp_fy @{context} 1",rule_tac x=x in spec[OF allI])
apply(tactic "asm_full_simp_tac @{context} 1")
using [[no_uniformity]]
apply(gen_test_cases 3 1 "PUT" )
(* Measurements 20.2. Revision 11395
   5 : 1 =>   31 test cases in 0.423 seconds
   6 : 1 =>   63 test cases in 1.319 seconds
   7 : 1 =>  127 test cases in 4.626 seconds
   8 : 1 =>  255 test cases in 17.063 seconds
   9 : 1 =>  511 test cases in 86.938 seconds
  10 : 1 =>  1023 test cases in 409.183 seconds
*)
(*
apply(tactic "ALLGOALS(TestGen.REPEAT'(ematch_tac @{context} [@{thm status.exec_mbindFStop_E},
                                                              @{thm release.exec_mbindFStop_E},
                                                              @{thm alloc.exec_mbindFStop_E},
                                                              @{thm valid_mbind'_mtE}
                          ]))")
apply(simp_all)
mk_test_suite "mykeos_very_large" 

*)
oops
end
