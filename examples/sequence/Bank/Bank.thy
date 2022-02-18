(*****************************************************************************
 * HOL-TestGen --- theorem-prover based test case generation
 *                 http://www.brucker.ch/projects/hol-testgen/
 *
 * Bank.thy --- an BirthdayBook inspired, elementary
 *              example for sequence testing based on a 
 *              deterministic specification.
 *
 * This file is part of HOL-TestGen.
 * 
 * Copyright (c) 2009-2016 University Paris-Sud, France
 *               2009-2015 Achim D. Brucker, Germany
 *               2016      The University of Sheffield, UK
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

chapter {* A Simple Deterministic Bank Model *}
theory  
  Bank
imports 
   "~~/src/HOL/Library/Code_Target_Numeral"
   Testing 
begin

section{* The Bank Example: Test of a Distributed Transaction Machine *}

declare [[testgen_profiling]]

text{* The intent of this little example is to model deposit,
check and withdraw operations of a little Bank model
in pre-postcondition style, formalize them in a setup
for \testgen{} test sequence generation and to generate elementary
test cases for it. The test scenarios will be restricted to
strict sequence checking; this excludes aspects of account
creation which will give the entire model a protocol character
(a create-operation would create an account number, and then
all later operations are just refering to this number; thus there
would be a dependence between system output and input as in
reactive sequence test scenarios.).

Moreover, in this scenario, we assume that the system under test is
deterministic.

The theory of Proof-based Sequence Test Methodology can be 
found in \cite{brucker.ea:theorem-prover:2012}.
 *}

text{* The state of our bank is just modeled by a map from
client/account information to the balance. *}
type_synonym client = string

type_synonym account_no = int

type_synonym data_base = "(client \<times> account_no) \<rightharpoonup> int"


subsection{* Operation definitions: Concept *}

text {* A standard, JML or OCL or VCC like interface specification
might look like:

\begin{verbatim}
Init:  forall (c,no) : dom(data_base). data_base(c,no)>=0

op deposit (c : client, no : account_no, amount:nat) : unit
pre  (c,no) : dom(data_base)
post data_base'=data_base[(c,no) := data_base(c,no) + amount]

op balance (c : client, no : account_no) : int
pre  (c,no) : dom(data_base)
post data_base'=data_base and result = data_base(c,no)

op withdraw(c : client, no : account_no, amount:nat) : unit
pre  (c,no) : dom(data_base) and data_base(c,no) >= amount
post data_base'=data_base[(c,no) := data_base(c,no) - amount]
\end{verbatim}
*}

subsection{* Operation definitions: The model as ESFM *}


text{* Interface normalization turns this interface into the following input type: *}

datatype in_c = deposit  client account_no nat
              | withdraw client account_no nat
              | balance  client account_no
              
typ "Bank.in_c"

datatype out_c = depositO| balanceO nat | withdrawO

fun    precond :: "data_base \<Rightarrow> in_c \<Rightarrow> bool"
where "precond \<sigma> (deposit c no m) = ((c,no) \<in> dom \<sigma>)"
    | "precond \<sigma> (balance c no) = ((c,no) \<in> dom \<sigma>)"
    | "precond \<sigma> (withdraw c no m) = ((c,no) \<in> dom \<sigma> \<and> (int m) \<le> the(\<sigma>(c,no)))"

fun    postcond :: "in_c \<Rightarrow> data_base \<Rightarrow> (out_c \<times> data_base) set"
where "postcond (deposit c no m) \<sigma> =
         { (n,\<sigma>'). (n = depositO \<and> \<sigma>'=\<sigma>((c,no)\<mapsto> the(\<sigma>(c,no)) + int m))}"
    | "postcond (balance c no) \<sigma> =
         { (n,\<sigma>'). (\<sigma>=\<sigma>' \<and> (\<exists> x. balanceO x = n \<and> x = nat(the(\<sigma>(c,no)))))}"
    | "postcond (withdraw c no m) \<sigma> =
         { (n,\<sigma>'). (n = withdrawO \<and> \<sigma>'=\<sigma>((c,no)\<mapsto> the(\<sigma>(c,no)) - int m))}"


definition init :: "data_base \<Rightarrow> bool"
where     "init \<sigma> \<equiv> \<forall>x \<in> dom \<sigma>. the(\<sigma> x) \<ge> 0"  

subsubsection{* Constructing an Abstract Program *}

text{* Using the Operators \verb+impl+ and \verb+strong_impl+, we can 
synthesize an abstract program right away from the specification, i.e. the pair 
of pre- and  postcondition defined above. Since this program is even 
deterministic, we will derive a set of symbolic execution rules used in the test case 
generation process which will produce symbolic results against which the PUT can 
be compared in the test driver. *}



lemma precond_postcond_implementable: 
     "implementable precond postcond"
apply(auto simp: implementable_def)
apply(case_tac "\<iota>", simp_all)
done

text{* Based on this input-output specification, we construct the system model as the 
       canonical completion of the (functional) specification consisting of pre-  and 
       post-conditions. \emph{Canonical completion} means that the step function 
       explicitely fails (returns @{term None}) if the precondition fails;
       this makes it possible to to treat sequential execution failures in a uniform way.
       The system @{text SYS} can be seen as the step function
       in an input-output automata or, alternatively, a kind of Mealy machine
       over symbolic states, or, as an extended finite state machine.*}

definition   SYS  :: "in_c \<Rightarrow>(out_c, data_base)MON\<^sub>S\<^sub>E"
where       "SYS = (strong_impl precond postcond)"

text{* The combinator @{term strong_impl} turns the pre-post pair in a suitable 
step functions with the aforementioned characteristics for failing pre-conditions.*}

section{* Prerequisites *}

subsection{* Proving Symbolic Execution Rules for the  Abstractly Program *}
text{* The following lemmas reveal that this "constructed" program is actually
(due to determinism of the spec): *}

lemma Eps_split_eq' : "(SOME (x', y'). x'= x  \<and> y'= y) = (SOME (x', y'). x = x' \<and> y = y')"
by(rule arg_cong[of _ _ "Eps"], auto)

text{*deposit*}
interpretation deposit : efsm_det 
                 "precond" "postcond" "SYS" "(deposit c no m)" "\<lambda>_. depositO" 
                 "\<lambda> \<sigma>. \<sigma>((c, no) \<mapsto>  (the(\<sigma>(c, no)) + int m))" "\<lambda> \<sigma>. ((c, no) \<in> dom \<sigma>)"
               by unfold_locales (auto simp: SYS_def Eps_split_eq')

find_theorems name:"deposit"

text{* withdraw *}
interpretation withdraw : efsm_det 
                  "precond" "postcond" "SYS" "(withdraw c no m)" "\<lambda>_. withdrawO" 
                  "\<lambda> \<sigma>. \<sigma>((c, no) \<mapsto>  (the(\<sigma>(c, no))-int m))" "\<lambda> \<sigma>.((c, no)\<in>dom \<sigma>) \<and> (int m)\<le>the(\<sigma>(c,no))"
               by unfold_locales (auto simp: SYS_def Eps_split_eq')

text{* balance *}
interpretation balance : efsm_det 
                  "precond" "postcond" "SYS" "(balance c no)" "\<lambda>\<sigma>. (balanceO (nat(the(\<sigma>(c, no)))))" 
                  "\<lambda> \<sigma>. \<sigma>" "\<lambda> \<sigma>. ((c, no) \<in> dom \<sigma>)"
               by unfold_locales (auto simp: SYS_def Eps_split_eq')


text{* Now we close the theory of symbolic execution by \emph{exluding} elementary rewrite
steps on @{term mbind}, \ie{} the rules @{thm mbind.simps(1)} @{thm mbind.simps(2)} *}

declare mbind.simps(1) [simp del]
        mbind.simps(2) [simp del]

text{* Here comes an interesting detail revealing the power of the
approach: The generated sequences still respect the preconditions
imposed by the specification  - in this case, where we are talking about
a client for which a defined account exists and for which we will never 
produce traces in which we withdraw more money than available on it. *}

subsection{* Restricting the Test-Space by Test Purposes *}
text{* We introduce a constraint on the input sequence, in order to limit the test-space
       a little and eliminate logically possible, but irrelevant test-sequences for a specific
       test-purpose. In this case, we narrow down on test-sequences concerning a specific
       client @{term c} with a specific bank-account number @{term no}.
       
       We make the (in this case implicit, but as constraint explicitly stated) test hypothesis,
       that the @{term SUT} is correct if it behaves correct for a single client.
       This boils down to the assumption that they are implemented as atomic transactions
       and interleaved processing does not interfere with a single thread. *}

fun test_purpose :: "[client, account_no, in_c list] \<Rightarrow> bool"
where
  "test_purpose c no [balance c' no'] = (c=c' \<and> no=no')" 
| "test_purpose c no ((deposit c' no' m)#R) = (c=c' \<and> no=no' \<and> test_purpose c no R)"
| "test_purpose c no ((withdraw c' no' m)#R) = (c=c' \<and> no=no' \<and> test_purpose c no R)"
| "test_purpose c no _ = False"

lemma [simp] : "test_purpose c no [a] = (a = balance c no)"
by(cases a, auto)

lemma [simp] : "R\<noteq>[] \<Longrightarrow> test_purpose c no (a#R) = 
                          (((\<exists>m. a = (deposit c no m)) \<or> (\<exists>m. a = (withdraw c no m))) 
                                 \<and> test_purpose c no R) "
apply(simp add: List.neq_Nil_conv, elim exE,simp)
by(cases a, auto)


subsection{* The TestGen Setup*}
text{* The default configuration of \verb$gen_test_cases$ does \emph{not} descend into 
       sub-type expressions of type constructors (since this is not always desirable, the choice 
       for the default had been for "non-descent"). This case is relevant here since 
       @{typ "Bank.in_c list"} has just this structure but we need ways to explore the input sequence
       type further. Thus, we need configure, for all test cases, and derivation descendants of
       the relusting clauses during splitting, again splitting for all parameters of 
       input type @{typ "Bank.in_c"}: *}

(* Apparently no effectv under 2016 ... 
set_pre_safe_tac{*
  (fn ctxt => TestGen.ALLCASES(
                  TestGen.CLOSURE (
                      TestGen.case_tac_typ ctxt ["Bank.in_c"]))) 
*}
*)

subsection{* Preparation: Miscellaneous *}
 
text{* We construct test-sequences for a concrete client (implicitely assuming 
that interleaving actions with other clients will not influence the system behaviour.
In order to prevent \testgen to perform case-splits over names, \ie, list of 
characters---we define it as constant.
*}
(* fixing the init-space a little *)
definition c\<^sub>0 :: "string" where "c\<^sub>0 = ''meyer''"
(* PUT must be a constant for coding conventions ... *)
consts PUT :: "(in_c \<Rightarrow>(out_c, '\<sigma>)MON\<^sub>S\<^sub>E)"

lemma HH : "(A \<and> (A \<longrightarrow> B)) = (A \<and>  B)" by auto


section{* Small, rewriting based Scenarios including standard code-generation *}

text{* Exists in two formats : General Fail-Safe Tests (which allows for scenarios 
with normal \emph{and} exceptional behaviour; and Fail-Stop Tests, which generates Tests 
only for normal behaviour and correspond to inclusion test refinement. *}

text{* In the following, we discuss a test-scenario with failsave error semantics; \ie{} in each
test-case, a sequence may be chosen (by the test data selection) where the client has  several
accounts. In other words, tests were generated for both \emph{standard} \bf{and} 
\emph{exceptional behaviour}. The splitting technique is general exploration of the type
@{typ "in_c list"}. *}
(*
test_spec test_balance:
assumes account_def   : "(c\<^sub>0,no) \<in> dom \<sigma>\<^sub>0" 
and     accounts_pos  : "init \<sigma>\<^sub>0" 
and     test_purpose  : "test_purpose c\<^sub>0 no S"
and     sym_exec_spec :
       " \<sigma>\<^sub>0 \<Turnstile> (s \<leftarrow> mbind\<^sub>F\<^sub>a\<^sub>i\<^sub>l\<^sub>S\<^sub>a\<^sub>v\<^sub>e S SYS; return (s = x))"
shows  " \<sigma>\<^sub>0 \<Turnstile> (s \<leftarrow> mbind\<^sub>F\<^sub>a\<^sub>i\<^sub>l\<^sub>S\<^sub>a\<^sub>v\<^sub>e S PUT; return (s = x))"
*)
test_spec test_balance:
 "(c\<^sub>0,no) \<in> dom \<sigma>\<^sub>0 \<Longrightarrow>
  init \<sigma>\<^sub>0 \<Longrightarrow>
  test_purpose c\<^sub>0 no S \<Longrightarrow> 
  \<sigma>\<^sub>0 \<Turnstile> (s \<leftarrow> mbind\<^sub>F\<^sub>a\<^sub>i\<^sub>l\<^sub>S\<^sub>a\<^sub>v\<^sub>e S SYS; return (s = x)) \<Longrightarrow>

   \<sigma>\<^sub>0 \<Turnstile> (s \<leftarrow> mbind\<^sub>F\<^sub>a\<^sub>i\<^sub>l\<^sub>S\<^sub>a\<^sub>v\<^sub>e S PUT; return (s = x))"

txt{* Prelude: Massage of the test-theorem --- representing the assumptions of the test explicitely
      in HOL and blocking @{term x} from beeing case-splitted (which complicates the process).*}
(*
apply(rule rev_mp[OF sym_exec_spec])
apply(rule rev_mp[OF account_def])
apply(rule rev_mp[OF accounts_pos])
apply(rule rev_mp[OF test_purpose])
*)
apply(erule rev_mp)+
apply(rule_tac x=x in spec[OF allI])
txt{*  Starting the test generation process.*}
(* Variant I :
using[[no_uniformity]]
apply(gen_test_cases 3 1 "PUT" simp:  HH split: HOL.if_split_asm)
txt{* So lets go for a more non-destructive approach: *}
*)
(* Variant II : *)
apply(gen_test_cases 5 1 "PUT") (* rev 12197: around 180 s *)
(* and symbolic execution separately *)
apply(simp_all add: init_def  HH split: HOL.if_split_asm)

mk_test_suite "bank_simpleSNXB"  (* SNX: Standard and Exceptional Behaviour *)
thm bank_simpleSNXB.test_thm  



text{* And now the Fail-Stop scenario --- this corresponds exactly to inclusion tests
       for normal-behaviour tests: any transition in the model is only possible iff
       the pre-conditions of the transitions in the model were respected. *}
declare Monads.mbind'_bind [simp del]
(*
test_spec test_balance2: 
assumes account_def   : "(c\<^sub>0,no) \<in> dom \<sigma>\<^sub>0" 
and     accounts_pos  : "init \<sigma>\<^sub>0" 
and     test_purpose  : "test_purpose c\<^sub>0 no S"
and     sym_exec_spec :
       " \<sigma>\<^sub>0 \<Turnstile> (s \<leftarrow> mbind\<^sub>F\<^sub>a\<^sub>i\<^sub>l\<^sub>S\<^sub>t\<^sub>o\<^sub>p S SYS; return (s = x))"
shows  " \<sigma>\<^sub>0 \<Turnstile> (s \<leftarrow> mbind\<^sub>F\<^sub>a\<^sub>i\<^sub>l\<^sub>S\<^sub>t\<^sub>o\<^sub>p S PUT; return (s = x))"
txt{* Prelude: Massage of the test-theorem --- representing the assumptions of the test explicitely
in HOL and blocking @{term x} from beeing case-splitted (which complicates the process).*}
apply(rule rev_mp[OF sym_exec_spec])
apply(rule rev_mp[OF account_def])
apply(rule rev_mp[OF accounts_pos])
apply(rule rev_mp[OF test_purpose])
apply(rule_tac x=x in spec[OF allI])
*)
(* workaround *)
test_spec test_balance2: 
"(c\<^sub>0,no) \<in> dom \<sigma>\<^sub>0 \<Longrightarrow> 
 init \<sigma>\<^sub>0 \<Longrightarrow> 
 test_purpose c\<^sub>0 no S \<Longrightarrow>  
 \<sigma>\<^sub>0 \<Turnstile> (s \<leftarrow> mbind\<^sub>F\<^sub>a\<^sub>i\<^sub>l\<^sub>S\<^sub>t\<^sub>o\<^sub>p S SYS; return (s = x)) \<Longrightarrow> 
 \<sigma>\<^sub>0 \<Turnstile> (s \<leftarrow> mbind\<^sub>F\<^sub>a\<^sub>i\<^sub>l\<^sub>S\<^sub>t\<^sub>o\<^sub>p S PUT; return (s = x))"
txt{* Prelude: Massage of the test-theorem --- representing the assumptions of the test explicitely
in HOL and blocking @{term x} from beeing case-splitted (which complicates the process).*}
apply(erule rev_mp)+
apply(rule_tac x=x in spec[OF allI])
(* workaround end *)

txt{*  Starting the test generation process - variant without uniformity generation.*}
using[[no_uniformity]]  
apply(gen_test_cases 4 1 "PUT")
txt{* So lets go for a more non-destructive approach: *}
using[[goals_limit=20]]
apply(simp_all add: init_def  HH split: HOL.if_split_asm)
(* variant with post-hoc generation of uniformities ... *)
using[[no_uniformity=false]]    
apply(tactic "TestGen.ALLCASES(TestGen.uniformityI_tac @{context} [\"PUT\"])") 
mk_test_suite "bank_simpleNB"
thm bank_simpleNB.test_thm

section{*  Test-Data Generation *}

text{* Configuration *}
declare [[testgen_iterations=0]] (* switch off random-solver *)

declare [[testgen_SMT]]          (* switch on Z3 -- for old version, don't forget to set shell variables *)


(* We give Z3 access to the definitions that are used by the test theorem *)
declare c\<^sub>0_def            [testgen_smt_facts] (* Not really needed *)
declare mem_Collect_eq    [testgen_smt_facts]
declare Collect_mem_eq    [testgen_smt_facts]
declare dom_def           [testgen_smt_facts]
declare Option.option.sel [testgen_smt_facts]

text{* Test Data Selection for the Normal and Exceptional Behaviour Test Scenario *}

gen_test_data "bank_simpleSNXB"
thm bank_simpleSNXB.test_thm
thm bank_simpleSNXB.test_thm_inst
print_conc_tests bank_simpleSNXB


text{* Test Data Selection for the Normal Behaviour Test Scenario *}

declare [[testgen_iterations=0]] 
declare [[testgen_SMT]]
gen_test_data "bank_simpleNB"

print_conc_tests bank_simpleNB
thm bank_simpleNB.test_thm_inst


section {* Generating the Test-Driver for an SML and C implementation *}

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
generate_test_script "bank_simpleSNXB"
thm                   bank_simpleSNXB.test_script

generate_test_script "bank_simpleNB"
thm                   bank_simpleNB.test_script

text{* In the following, we describe the interface of the SML-program under test, which is 
in our scenario an \emph{adapter} to the C code under test. This is the heart of the
model-to-SML translation.
The the SML-level stubs for the program under test are declared as follows: *}


consts     balance_stub :: "string \<Rightarrow> int \<Rightarrow> (int, '\<sigma>)MON\<^sub>S\<^sub>E"
code_printing
    constant balance_stub => (SML) "(fn n => fn i => fn s => (case (BankAdapter.balance n (integer'_of'_int i) s) of (SOME(i',s')) => SOME(Int'_of'_integer i',s')))"

consts     deposit_stub :: "string \<Rightarrow> int \<Rightarrow> int \<Rightarrow> (unit, '\<sigma>)MON\<^sub>S\<^sub>E"
code_printing
    constant deposit_stub => (SML) "(fn s => fn i => fn j => BankAdapter.deposit s (integer'_of'_int i) (integer'_of'_int j))"

consts     withdraw_stub:: "string \<Rightarrow> int \<Rightarrow> int \<Rightarrow> (unit, '\<sigma>)MON\<^sub>S\<^sub>E"
code_printing
    constant withdraw_stub => (SML) "(fn s => fn i => fn j => BankAdapter.withdraw s (integer'_of'_int i) (integer'_of'_int j))"

text{*Note that this translation step prepares already the data-adaption; the type \verb+nat+
is seen as an predicative constraint on integer (which is actually not tested).
On the model-to-model level, we provide a global step function that distributes to
individual interface functions via stubs (mapped via the code generation to SML ...).
This translation also represents uniformly nat by int's.
*}


fun   stepAdapter :: "(in_c \<Rightarrow>(out_c, '\<sigma>)MON\<^sub>S\<^sub>E)" 
where
     "stepAdapter(balance name no) = 
                 (x \<leftarrow> balance_stub name no; return(balanceO (Int.nat x)))"
   | "stepAdapter(deposit name no amount) = 
                 (_ \<leftarrow> deposit_stub name no (int amount); return(depositO))"
   | "stepAdapter(withdraw name no amount)= 
                 (_ \<leftarrow> withdraw_stub name no (int amount); return(withdrawO))"

text{* The @{term stepAdapter} function links the HOL-world and establishes the logical link
       to HOL stubs which were mapped by the code-generator to adapter functions in SML (which call 
       internally to C-code inside \verb+bank_adapter.sml+ via a foreign language interface) 

       ... We configure the code-generator to identify the \verb+PUT+ with the generated SML code 
       implicitely defined by the above @{term stepAdapter} definition. *}
 
code_printing
    constant PUT  => (SML) "stepAdapter"


text{* And there we go and generate the \verb+bank_simple_test_script.sml+: *}
export_code                   stepAdapter bank_simpleSNXB.test_script in SML    
module_name TestScript file  "impl/c/bank_simpleSNXB_test_script.sml"

export_code                   stepAdapter bank_simpleNB.test_script in SML    
module_name TestScript file  "impl/c/bank_simpleNB_test_script.sml"




section{* More advanced Test-Case Generation Scenarios *}

text{* Exploring a bit the limits ... *}

text{* Rewriting based approach of symbolic execution ... FailSave Scenario *}
test_spec test_balance:
assumes account_def   : "(c\<^sub>0,no) \<in> dom \<sigma>\<^sub>0" 
and     accounts_pos  : "init \<sigma>\<^sub>0" 
and     test_purpose  : "test_purpose c\<^sub>0 no S"
and     sym_exec_spec :
       " \<sigma>\<^sub>0 \<Turnstile> (s \<leftarrow> mbind\<^sub>F\<^sub>a\<^sub>i\<^sub>l\<^sub>S\<^sub>a\<^sub>v\<^sub>e S SYS; return (s = x))"
shows  " \<sigma>\<^sub>0  \<Turnstile> (s \<leftarrow> mbind\<^sub>F\<^sub>a\<^sub>i\<^sub>l\<^sub>S\<^sub>a\<^sub>v\<^sub>e S PUT; return (s = x))"
txt{* Prelude: Massage of the test-theorem --- representing the assumptions of the test explicitely
in HOL and blocking @{term x} from beeing case-splitted (which complicates the process).*}
apply(insert (* accounts_pos *)  account_def test_purpose sym_exec_spec)
apply(tactic "TestGen.mp_fy @{context} 1",rule_tac x=x in spec[OF allI])
txt{*  Starting the test generation process.*}
apply(gen_test_cases 5 1 "PUT")
(* Measurements 20.2. Revision 11395
   5 : 1 =>  31 test cases in 7.609 seconds
   6 : 1 =>  63 test cases in 26.977 seconds 
   7 : 1 => 127 test cases in 125.183 seconds
*)
txt{* Symbolic Execution: *}
apply(simp_all add:  HH split: HOL.if_split_asm)
(* test data selection by hand !!! *)
mk_test_suite "bank_large"

gen_test_data "bank_large"
print_conc_tests bank_large


text{* Rewriting based approach of symbolic execution ... FailSave Scenario *}
test_spec test_balance:
assumes account_def   : "(c\<^sub>0,no) \<in> dom \<sigma>\<^sub>0" 
and     accounts_pos  : "init \<sigma>\<^sub>0" 
and     test_purpose  : "test_purpose c\<^sub>0 no S"
and     sym_exec_spec : 
       " \<sigma>\<^sub>0 \<Turnstile> (s \<leftarrow> mbind\<^sub>F\<^sub>a\<^sub>i\<^sub>l\<^sub>S\<^sub>t\<^sub>o\<^sub>p S SYS; return (s = x))"
shows  " \<sigma>\<^sub>0 \<Turnstile> (s \<leftarrow> mbind\<^sub>F\<^sub>a\<^sub>i\<^sub>l\<^sub>S\<^sub>t\<^sub>o\<^sub>p S PUT; return (s = x))"
txt{* Prelude: Massage of the test-theorem --- representing the assumptions of the test explicitely
in HOL and blocking @{term x} from beeing case-splitted (which complicates the process).*}
apply(insert (* accounts_pos *)  account_def test_purpose sym_exec_spec)
apply(tactic "TestGen.mp_fy @{context} 1",rule_tac x=x in spec[OF allI])
txt{*  Starting the test generation process.*}
apply(gen_test_cases 3 1 "PUT")
(* Measurements 20.2. Revision 11395
   5 : 1 => 31 test cases in 3.704 seconds
   6 : 1 => 63 test cases in 5.726 seconds
   7 : 1 => 127 test cases in 25.700 seconds
   8 : 1 => 255 test cases in 119.720 seconds
   9 : 1 => 511 test cases in 755.510 seconds
  10 : 1 => 1023 test cases in 6505.396 seconds
*)
txt{* Symbolic Execution: *}
apply(simp_all add:  HH split: HOL.if_split_asm)
(* test data selection by hand !!! *)
mk_test_suite "bank_large'"

gen_test_data "bank_large'"
print_conc_tests bank_large'


text{* And now, to compare, elimination based procedures ... *}

declare deposit.exec_mbindFSave_If[simp del]
declare balance.exec_mbindFSave_If[simp del]
declare withdraw.exec_mbindFSave_If[simp del]
declare deposit.exec_mbindFStop [simp del]
declare balance.exec_mbindFStop[simp del]
declare withdraw.exec_mbindFStop[simp del]

thm deposit.exec_mbindFSave_E withdraw.exec_mbindFSave_E balance.exec_mbindFSave_E
(*
declare exec_mbindFSave_depositE[elim!]
declare exec_mbindFSave_withdrawE[elim!]
declare exec_mbindFSave_balanceE[elim!]
*)


test_spec test_balance:
assumes account_defined: "(c\<^sub>0,no) \<in> dom \<sigma>\<^sub>0" 
and     accounts_pos  : "init \<sigma>\<^sub>0" 
and     test_purpose   : "test_purpose c\<^sub>0 no S"
and     sym_exec_spec :
       " \<sigma>\<^sub>0 \<Turnstile> (s \<leftarrow> mbind\<^sub>F\<^sub>a\<^sub>i\<^sub>l\<^sub>S\<^sub>t\<^sub>o\<^sub>p S SYS; return (s = x))"
shows  " \<sigma>\<^sub>0 \<Turnstile> (s \<leftarrow> mbind\<^sub>F\<^sub>a\<^sub>i\<^sub>l\<^sub>S\<^sub>t\<^sub>o\<^sub>p S PUT; return (s = x))"  
apply(insert (* accounts_pos *)  account_defined test_purpose sym_exec_spec)
apply(tactic "TestGen.mp_fy @{context} 1",rule_tac x=x in spec[OF allI])
using [[no_uniformity]]
apply(gen_test_cases 
3 1 "PUT" )
(* Measurements 20.2. Revision 11395
   5 : 1 =>   31 test cases in 0.423 seconds
   6 : 1 =>   63 test cases in 1.319 seconds
   7 : 1 =>  127 test cases in 4.626 seconds
   8 : 1 =>  255 test cases in 17.063 seconds
   9 : 1 =>  511 test cases in 86.938 seconds
  10 : 1 =>  1023 test cases in 409.183 seconds
*)
apply(tactic "ALLGOALS(TestGen.REPEAT'(ematch_tac @{context} [@{thm balance.exec_mbindFStop_E},
                                                              @{thm withdraw.exec_mbindFStop_E},
                                                              @{thm deposit.exec_mbindFStop_E},
                                                              @{thm valid_mbind'_mt}
                          ]))")
apply(simp_all)
using[[no_uniformity=false]]    
apply(tactic "TestGen.ALLCASES(TestGen.uniformityI_tac @{context} [\"PUT\"])") 
mk_test_suite "bank_large_very" 


text{* Yet another technique: "deep" symbolic execution rules involving knowledge from the
       model domain. Here: input alphabet must be case-split over deposit, withdraw and
       balance. This avoids that \verb$gen_test_cases$ has to do deep splitting. 
*}

theorem hulk : 
assumes redex    : "\<sigma> \<Turnstile> (s \<leftarrow> (mbind\<^sub>F\<^sub>a\<^sub>i\<^sub>l\<^sub>S\<^sub>t\<^sub>o\<^sub>p (a # S) SYS); return (P s))"
and case_deposit : " \<And>c no m. a = deposit c no m \<Longrightarrow> (c, no) \<in> dom \<sigma> \<Longrightarrow> 
                               \<sigma>((c, no) \<mapsto> the (\<sigma> (c, no)) + int m) \<Turnstile>
                                      ( s \<leftarrow> mbind\<^sub>F\<^sub>a\<^sub>i\<^sub>l\<^sub>S\<^sub>t\<^sub>o\<^sub>p S SYS; return P (depositO # s)) \<Longrightarrow>
                               Q"
and case_withdraw : "\<And>c no m.  a = withdraw c no m \<Longrightarrow> (c, no) \<in> dom \<sigma> \<Longrightarrow>
                               int m \<le> the (\<sigma> (c, no)) \<Longrightarrow>
                               \<sigma>((c,no) \<mapsto> the(\<sigma>(c,no))- int m) \<Turnstile>
                                              (s \<leftarrow> mbind\<^sub>F\<^sub>a\<^sub>i\<^sub>l\<^sub>S\<^sub>t\<^sub>o\<^sub>p S SYS; return P (withdrawO#s)) \<Longrightarrow>
                               Q"
and case_balance  : "\<And>c no.    (c, no) \<in> dom \<sigma> \<Longrightarrow> 
                                 \<sigma> \<Turnstile>(s \<leftarrow> mbind\<^sub>F\<^sub>a\<^sub>i\<^sub>l\<^sub>S\<^sub>t\<^sub>o\<^sub>p S SYS; 
                                     return P (balanceO (nat (the (\<sigma> (c, no)))) # s)) \<Longrightarrow>
                                Q"
shows "Q"
proof(cases "a") print_cases
     case (deposit c no m) assume hyp : "a = deposit c no m" show "Q"
        using hyp redex
        apply(simp only: deposit.exec_mbindFStop) 
        apply(rule case_deposit, auto)
        done

next 
     case (withdraw c no m) assume hyp : "a = withdraw c no m" show "Q"
        using hyp redex
        apply(simp only: withdraw.exec_mbindFStop) 
        apply(rule case_withdraw, auto)
        done
next 
     case (balance c no) assume hyp : "a = balance c no " show "Q"
        using hyp redex
        apply(simp only: balance.exec_mbindFStop) 
        apply(rule case_balance, auto)
        done
qed

section{* Experimental Space *}
declare[[testgen_trace]] 
ML{* prune_params_tac; Drule.triv_forall_equality*}

(*
lemma "PO (\<not>(( \<not> A \<or> ( B \<and> F)) \<and>
             (   A \<or> (E \<and> F))))"
apply(subst HOL.imp_conv_disj[symmetric])
apply(subst (2) HOL.not_not[symmetric,of "A"]) 
apply(subst HOL.imp_conv_disj[symmetric])
apply(subst HOL.if_bool_eq_conj[symmetric])


lemma "PO ( (( \<not> A \<or>  ( B \<and> F)) \<and>
            (   A \<or>   (E \<and> F))))"
MCDC ::::

T : A -> True   B -> True    F-> True   E -> False
F : A -> False  B -> True    F-> True   E -> False

F : A -> True   B -> False   F-> True   E -> False
F : A -> True   B -> True    F-> False  E -> False
T : A -> False  B -> True    F-> True   E -> True


*)
end
