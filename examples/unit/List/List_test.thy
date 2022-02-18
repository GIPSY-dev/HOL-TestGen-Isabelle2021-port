(*****************************************************************************
 * HOL-TestGen --- theorem-prover based test case generation
 *                 http://www.brucker.ch/projects/hol-testgen/
 *                                                                            
 * List_test.thy --- testing infinite data structures (lists)
 * This file is part of HOL-TestGen.
 *
 * Copyright (c) 2005-2007 ETH Zurich, Switzerland
 *               2007-2015 Achim D. Brucker, Germany
 *               2008-2016 University Paris-Sud, France
 *               2016      University of Sheffield, UK
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
(* $Id: List_test.thy 13154 2017-08-18 20:11:41Z brucker $ *)

chapter\<open> Testing List Properties \<close> 

text\<open>This is a reference show-case for \testgen providing three test-scenarios that were
treated from A to Z. This includes: 
\<^enum> The modeling phase ("building the test-theory") comprising definitions and theorems
         representing the "background theory" of a particular model to test.
\<^enum> The test-specification, the formal statement from which the tests were derived.
\<^enum> The abstract test generation phase which basically cuts the input-output relation
         of the program under test into partitions represented by constraint systems.
         (since the constraint systems can be unsatisfiable, abstract test cases can be
         vacuous).
\<^enum> The test selection phase that attempts to find concrete test-cases, \ie{} ground
         instances of abstract test cases. 
\<^enum> The test driver generation  phase converts the concrete test-cases into a program 
         that executes these tests; it is linked to a test-harness allowing to track the
         test evaluation and the program or system under test.
\<^enum> The test execution phase (which is currently done outside \testgen{} via makefiles.          
\<close>

text\<open>In this example we present the current main application of \testgen{}: generating test data 
for black box testing of functional programs within a specification based unit test. We use a 
simple scenario, developing the test theory for testing sorting algorithms over lists, develop 
test specifications (elsewhere called test targets or test goals), and explore the different 
possibilities.\<close>



theory   List_test 
imports 
  List
   "~~/src/HOL/Library/Code_Target_Numeral"
   Code_Integer_Fsharp
   Testing
begin

text\<open>A Test-theory as a whole starts with the import of its main components, among them 
     the \testgen environment grouped together in the @{theory "Testing"}. The theories
     @{theory "Code_Target_Numeral"} and @{theory "Code_Integer_Fsharp"} are required
     to support the test driver generation  process.
\<close>


section {* A First Model and a Quick Walk Through *} 
text {* In the following we give a first impression of how the testing process using \testgen{} 
looks like. For brevity we stick to default parameters and explain possible decision points and 
parameters where the testing can be improved in the next section.  *}

subsubsection {* Modeling: Writing the Test Specification *}
text {* We start by specifying a primitive recursive predicate describing sorted lists: *}

(* primrec is_sorted:: "('a::linorder) list \<Rightarrow> bool" *)
primrec  is_sorted:: "int list \<Rightarrow> bool" 
  where "is_sorted  []      = True" |
        "is_sorted  (x#xs)  = (case xs of 
                                  []   \<Rightarrow> True 
                                | y#ys \<Rightarrow> x \<le> y \<and> is_sorted xs)"



text {* We will use this HOL predicate for describing our test specification, i.e. the properties 
our implementation should fulfill and which we ultimately will test. *} 

test_spec     "is_sorted(PUT l)"
oops


text {* where @{text PUT} is a ``placeholder'' for our program under test. For the sake of the
presentation, we drop the test attempt here.*}


text{* However, for the code-generation necessary to generate a test-driver and actually 
@{emph \<open>run\<close>} the test of an external program, the @{emph \<open>program under test\<close>} or @{verbatim \<open>PUT\<close>} for short, it is sensible to represent the latter as an 
@{bold \<open>uninterpreted constant\<close>};  the code-generation will later on configured such that the 
place-holder in the test-driver code is actually linked to the real, external program which is a 
black box from the point of view of this model (the testing procedure needs actually only 
executable code). *}


consts PUT :: "'a list \<Rightarrow> 'a list" 

text{* Note that the choice of the name is arbitrary. *}

subsubsection \<open>Generating Abstract Test-cases\<close> 

text {* Now we can automatically generate @{emph \<open>test cases\<close>}. Using the default
        setup, we just apply our @{method gen_test_cases}: *}




test_spec "is_sorted(PUT (l))"
  apply(gen_test_cases 3 1 "PUT")
  txt {*  which leads to the test partitioning one would expect: @{subgoals[display,goals_limit=50]}.
          Now we bind the test theorem to a particular named @{emph \<open>test suite\<close>}, a kind of 
          container into which all relevant data is stored and under which a group of tests can be 
          referred to during test execution. *}
mk_test_suite "is_sorted_result"


text {* The current test theorem contains holes, that correspond to the concrete data of the test
        that have not been generated yet *}
thm is_sorted_result.test_thm



subsubsection \<open>Generating Concrete Test-cases \<close>
text {* Now we want to generate concrete test data, i.e. all variables in the 
test cases must be instantiated with concrete values. This involves a 
random solver which tries to solve the constraints by randomly 
choosing values.  *}


thm is_sorted_result.test_thm
gen_test_data "is_sorted_result" 
thm is_sorted_result.test_thm_inst  


(*
ML{* 
fun pretty_cterm_style_generic f ctxt (style, (name,pos:Position.T)) =
     let val termS =  case (Symtab.lookup (f (TestEnv.get_testenv ctxt)) name) of
                           SOME k => map (style o Thm.term_of) k  (* (nth(k,0)) *)
                         | NONE => error "No such test suite"
     in Pretty.big_list "\\\\" (map (Thy_Output.pretty_term ctxt) ( termS)) end

val  pretty_thyp_style     = pretty_cterm_style_generic TestEnv.get_test_thyps_tab
val  pretty_conctest_style = pretty_cterm_style_generic TestEnv.get_test_data_tab
val  pretty_uPO_style      = pretty_cterm_style_generic TestEnv.get_unsolved_PO_tab

(* code copy from Thy_Output (2016) since this is not exported there ... *)

fun basic_entities name scan pretty =
  Thy_Output.antiquotation name scan (fn {source, context = ctxt, ...} =>
    Thy_Output.output ctxt o Thy_Output.maybe_pretty_source pretty ctxt source);

fun basic_entity name scan = basic_entities name (scan >> single);

(* end copy *)

val _ = Theory.setup
( (basic_entity @{binding thyps} (Term_Style.parse -- (Scan.lift (Parse.position Args.name))) 
   pretty_thyp_style) #>
  (basic_entity @{binding uPOs} (Term_Style.parse -- (Scan.lift (Parse.position Args.name))) 
   pretty_uPO_style) #>
  (basic_entity @{binding conctests} (Term_Style.parse -- (Scan.lift (Parse.position Args.name))) 
   pretty_conctest_style)) 
  ;
*} *)

text{* Which leads to the following test data: @{conctests "is_sorted_result"} *}
text{* Note that the underlying test hypothesis remain: @{thyps "is_sorted_result"} *}


text {* Note that by the following statements, the test data, the test
        hypotheses and the test theorem can be inspected interactively. *}


print_conc_tests "is_sorted_result"
print_abs_tests  "is_sorted_result"
print_thyps      "is_sorted_result"
print_upos       "is_sorted_result"    (* TODO Chantal : upos must be defined, even if empty *)



text {* The generated test data can be exported to an external file:*}
export_test_data "impl/data/test_data.data" is_sorted_result    

subsubsection\<open>Test Execution and Result Verification \<close>
text {* In principle, any SML-system should be able to run the provided test-harness and generated 
test-script. Using their specific facilities for calling foreign code, testing of non-SML programs is
possible. For example, one could test implementations written:

\<^item> for the.Net platform, e.g., written in C\# using sml.net~\cite{sml.net},
\<^item> in C using, e.g.  the foreign language interface of sml/NJ~\cite{smlnj} or MLton~\cite{mlton},
\<^item> in Java using MLj~\cite{mlj}.

Depending on the SML-system, the test execution can be done within an interpreter or using a 
compiled test executable.  Testing implementations written in SML is straight-forward, based 
on automatically generated test scripts. This generation is based on the internal code generator of
Isabelle and must be set up accordingly.

The the following, we show the general generation of test-scripts (part of the finally generated 
test-driver) in different languages; finally, we will concentrate on the test-generation scenario 
for C.
*}


code_printing 
    constant PUT  => (Fsharp)  "((List.map (fun x -> Int'_of'_integer x)) (myList.sort (List.map (fun x -> integer'_of'_int x) ((_)) )))"
                 and (SML)    "((map (fn x => Int'_of'_integer x)) o myList.sort o  (map (fn x => integer'_of'_int x)))"
                 and (Scala)  "((myList.sort ((_).map {x => integer'_of'_int(x)})).map {x => int'_of'_integer(x)})"

generate_test_script "is_sorted_result"
thm                   is_sorted_result.test_script

text {* Testing an SML implementation: *}
export_code                  is_sorted_result.test_script in SML    
module_name TestScript file "impl/sml/is_sorted_test_script.sml" 

text {* We use the SML test script also for testing an implementation written in C: *}
export_code                  is_sorted_result.test_script in SML    
module_name TestScript file "impl/c/is_sorted_test_script.sml"

text {* Testing an F\# implementation: *}
export_code                  is_sorted_result.test_script in Fsharp 
module_name TestScript file "impl/fsharp/is_sorted_test_script.fs"

text {* We use the F\# test script also for testing an implementation written in C\#: *}
export_code                  is_sorted_result.test_script in Fsharp 
module_name TestScript file "impl/csharp/is_sorted_test_script.fs"

text {* Testing a Scala implementation: *}
export_code                  is_sorted_result.test_script in Scala 
module_name TestScript file "impl/scala/is_sorted_test_script.scala"

text {* We use the Scala script also for testing an implementation written in Java: *}
export_code                  is_sorted_result.test_script in Scala 
module_name TestScript file "impl/java/is_sorted_test_script.scala"

text {* Finally, we export the raw test data in an XML-like format: *}
export_test_data "impl/data/is_sorted_test_data.dat" is_sorted_result

text {* which generates the following test harness: 
  *}


text {* In the following, we assume an ANSI C implementation of our 
sorting method for sorting C arrays that we want to test.
(In our example setup, it is contained in the file @{file "impl/c/sort.c"}.)
Using the foreign language interface provided by the SML
compiler MLton we first have to import the sort method written in C
using the @{verbatim "_import"} keyword of MLton and further, we provide
a ``wrapper'' doing some data-type conversion, e.g.\ converting lists
to arrays and vice versa:
\begin{verbatim}
structure myList = struct

val csort = _import "sort": int array * int -> int array;
fun ArrayToList a = Array.foldl (op ::) [] a;
fun sort_list list = ArrayToList (csort(Array.fromList(list),(length list)));


fun sort list = map IntInf.fromInt (sort_list (map IntInf.toInt list))

end
\end{verbatim}
That's all, now we can build the test executable using MLton and end up with a test executable 
which can be called directly. In @{dir "impl/c"}, the process of:
\<^enum> compiling the generated @{file "impl/c/is_sorted_test_script.sml"}, the test harness
  (\verb+harness.sml+), a main routine @{file "impl/c/List.sml"}) and containing a wrapper into 
  an SML structure @{verbatim "myList"} as well as the SML-to-C code-stub @{verbatim "sort"},
\<^enum> compiling the C test-driver and linking it to the program under test @{file "impl/c/sort.c"}, and
\<^enum> executing the test
is captured in a @{file "impl/c/Makefile"}. So:
\begin{table}
  \centering
{\small
\begin{verbatim}
>make
mlton -default-ann 'allowFFI true' is_sorted_test.mlb sort.c
./is_sorted_test


Test Results:
=============
Test 0 -     SUCCESS
Test 1 -     SUCCESS
Test 2 -     SUCCESS
Test 3 -     SUCCESS
Test 4 -     SUCCESS
Test 5 -     SUCCESS
Test 6 -     SUCCESS


Summary:
--------
Number successful tests cases: 7 of 7 (ca. 100%)
Number of warnings:             0 of 7 (ca. 0%)
Number of errors:               0 of 7 (ca. 0%)
Number of failures:             0 of 7 (ca. 0%)
Number of fatal errors:         0 of 7 (ca. 0%)

Overall result: success
===============
\end{verbatim}
}
  \caption{A Sample Test Trace: The ascending property tested.}
  \label{tab:test-trace}
\end{table}
executes the test and displays a test-statistic as shown in
Table~\vref{tab:test-trace}. 
*}

section \<open> A Refined Model and Improved Test-Results \<close>
text {*
Obviously, in reality one would not be satisfied with the test cases generated in 
the previous section: for testing sorting algorithms one would expect that the test data
somehow represents the set of permutations of the list elements. We have already 
seen that the test specification used in the last section ``only'' enumerates
lists up to a specific length without any ordering constraints on their
elements. What is missing, is a test that input and output sequence are in fact
@{emph \<open>permutations\<close>} of each other. We could state for example : *} 

fun    del_member :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list option" 
where "del_member x [] = None"
     |"del_member x (y # S) = (if x = y then Some S 
                               else case del_member x S of
                                      None \<Rightarrow> None
                                    | Some S' \<Rightarrow> Some(y # S'))"

fun    is_permutation :: "'a list \<Rightarrow> 'a list \<Rightarrow> bool"
where "is_permutation [] [] = True"
     |"is_permutation (a#S)(a'#S') =(if a = a' then is_permutation S S'
                                     else case del_member a S' of
                                            None \<Rightarrow> False
                                          | Some S'' \<Rightarrow> is_permutation S (a'#S''))"
     |"is_permutation _ _ = False"

fun is_perm :: " 'a list \<Rightarrow> 'a list \<Rightarrow> bool"
where "is_perm [] [] = True"
     |"is_perm [] T  = False" 
     |"is_perm (a#S) T = (if length T = length S + 1 
                           then is_perm S (remove1 a T)
                           else False)"

value "is_perm [1,2,3::int] [3,1,2] "

text{* A test for permutation, that not is hopelessly non-constructive like
        "the existence of a bijection on the indexes [0 .. n-1], that is pairwise 
       mapped to the list" or the like, is obviously quite complex; the apparent 
       "mathematical specification" is not always the easiest. We convince ourselves 
       that the predicate @{term is_permutation} indeed captures our intuition by
       animations of the definition: *}
       
value "is_permutation [1,2,3] [3,2,1::nat]"
value "\<not> is_permutation [1,2,3] [3,1::nat]"
value "\<not> is_permutation [2,3] [3,2,1::nat]"
value "\<not> is_permutation [1,2,1,3] [3,2,1::nat]"
value "is_permutation [2,1,3] [1::nat,3,2]"

value "is_perm [1,2,3] [3,2,1::nat]"
value "\<not> is_perm [1,2,3] [3,1::nat]"
value "\<not> is_perm [2,3] [3,2,1::nat]"
value "\<not> is_perm [1,2,1,3] [3,2,1::nat]"
value "is_perm [2,1,3] [1::nat,3,2]"



text{* ... which are all executable and thus were compiled and all evaluated to true. *}

text{* Based on these concepts, a test-specification is straight-forward and easy: *}
declare [[goals_limit=5]]

(*<*)
test_spec "is_sorted(PUT l) \<and> is_perm (PUT l) l"
(*>*)
apply(gen_test_cases 5 1 "PUT")
mk_test_suite "ascending_permutation_test"

text{* A quick inspection of the test theorem reveals that there are in fact no
       relevant constraints to solve, so test-data selection is easy: *} 
declare [[testgen_iterations=100]]
gen_test_data       "ascending_permutation_test"


print_conc_tests    "ascending_permutation_test"
print_conc_tests (6)"ascending_permutation_test"
print_thyps         "ascending_permutation_test"
print_thyps      (0)"ascending_permutation_test"


text{* Again, we convert this into test-scripts that can be compiled to a test-driver. *}
generate_test_script ascending_permutation_test
thm                  ascending_permutation_test.test_script

text {* We use the SML implementation also for testing an implementation written in C: *}
export_code          ascending_permutation_test.test_script in SML    
module_name TestScript file "impl/c/ascending_permutation_test_script.sml"

text{* Try @{verbatim "make run_ascending_permutation"} in directory @{dir "impl/c"} to compile
and execute the generated test-driver.*}

section {* A Test-Specification based on a Comparison with a Reference Implementation *}

text{* We might opt for an alternative modeling approach:
Thus we decide to try a more `'descriptive'' test specification that
is based on the behavior of an insertion sort algorithm: *}

fun    ins :: "('a::linorder) \<Rightarrow> 'a list \<Rightarrow> 'a list"
where "ins x [] = [x]"
     |"ins x (y#ys) = (if (x < y) then x#y#ys else (y#(ins x ys)))"
fun    sort:: "('a::linorder) list \<Rightarrow> 'a list"
where "sort [] = []"
     |"sort (x#xs) = ins x (sort xs)"

text {*
Now we state our test specification by requiring that the behavior of the program under test 
@{text PUT} is identical to the behavior of our specified sorting algorithm @{text sort}: *}

text {*
Based on this specification @{method "gen_test_cases"} produces test cases representing all 
permutations of lists up to a fixed length @{value "n"}. Normally, we also want to configure up 
to which length lists should be generated (we call this the @{emph \<open>depth\<close>} of the test case), 
e.g.~we decide to generate lists up to length @{value "3"}. Our standard setup: *}

declare [[goals_limit=100]]
test_spec "sort l = PUT  l"
  apply(gen_test_cases "PUT")
mk_test_suite "is_sorting_algorithm0"

text {*
generates @{value "9"} test cases describing all permutations of lists of length
@{value "1"},@{value "2"} and @{value "3"}. "Permutation" means here that not only test cases 
(i.e. I/O-partitions) are generated for lists of length  @{value "0"}, @{value "1"},@{value "2"} 
and @{value "3"}; the partitioning is actually finer: for two-elementary lists, for example, 
the case of a list with the first element larger or equal and the dual case are distinguished. 
The entire test-theorem looks as follows:

@{thm "is_sorting_algorithm0.test_thm"} *}


text{*A more ambitious setting is:*}

test_spec "sort l = PUT  l"

  apply(gen_test_cases 5 1 "PUT") (* 7 !!! *)

 (* 154 test cases in 120.726 seconds *)

  txt {* which leads after 2 seconds to the following test partitioning (excerpt):
         @{subgoals [display, goals_limit=10]}
       *}
  (* apply smt *)     
mk_test_suite "permutation_test"

thm permutation_test.test_thm

text {* In this scenario, 39 test cases are generated describing all
permutations of lists of length $1,2,3$ and $4$. "Permutation" means
here that not only test cases (i.e.  I/O-partitions) are generated for
lists of length 0, 1, 2, 3, 4; the partitioning is actually finer: for
two-elementary lists, take one case for the lists with the first
element larger or equal.  *}

text{* The case for all lists of depth 5 is feasible, however, it will
already take 8 minutes. The resulting constraints for the test cases are
complex and require more intensive effort in resolving.*}

text{* There are several options for the test-data selection. On can either use the
(very old) random solver or the more modern smt interface. (One day, we would also
have a nitpick-interface to constsraint solving via bitblasting sub-models of the constraints
to SAT.) The random solver, however, finds only 67 instances out of 150 abstract test cases,
while smt instantiates all of them:
\begin{verbatim}
Test theorem (gen_test_data) 'permutation_test': 67 test cases in 2.951 seconds 
\end{verbatim}
 *}
(* Either random-solver : *)
(* declare [[testgen_iterations=100]] *)
(* Or activate smt-solver. (More efficient). *)
declare [[testgen_iterations=0]]
declare [[testgen_SMT]]          (* switch on Z3 *)
gen_test_data       "permutation_test"

print_conc_tests    "permutation_test"
print_thyps         "permutation_test"


 
generate_test_script permutation_test
thm                  permutation_test.test_script 

text {* We use the SML implementation also for testing an implementation written in C: *}
export_code          permutation_test.test_script in SML    
module_name TestScript file "impl/c/permutation_test_script.sml"

text{* We obtain test cases like:  @{conctests "permutation_test"}. *}

text {* If we scale down to only 10 iterations, 
this is not sufficient to solve all conditions, i.e. we 
obtain many test cases with unresolved constraints 
where @{term RSF} marks unsolved cases. In these
cases, it is unclear if the test partition is empty. Analyzing the generated
test data reveals that all cases for lists with length up to (and including) 
3 could be solved. From the 24 cases for lists of length 4 only
9 could be solved by the random solver 
(thus, overall 19 of the 34 cases 
were solved). To achieve better results, we could 
interactively increase the number of iterations which reveals that we
need to set iterations to 100 to find all solutions reliably.
\begin{center}
 \begin{tabular}{l||r|r|r|r|r|r|r|r|r}
 iterations&  5 & 10 & 20 & 25 & 30 & 40 & 50 & 75 & 100 \\
 \hline
 solved goals (of 34) & 13 & 19 & 23 & 24 & 25 & 29 & 33 & 33 &  34      
 \end{tabular}
\end{center}
Instead of increasing the number of iterations one could 
also add  other techniques such as 

        \begin{enumerate}
        \item deriving new rules that allow for 
              the generation of a simplified test theorem,
        \item introducing abstract test cases or 
        \item supporting the solving process by derived rules.
        \end{enumerate}
*}

text{* Running the test (in the current setup: \verb+make run_permutation_test+ )against our
sample C-program under \verb+impl/c+ yields the following result:
\begin{table}
  \centering
{\small
\begin{verbatim}
> make run_permutation_test
mlton -default-ann 'allowFFI true' permutation_test.mlb sort.c
./permutation_test


Test Results:
=============
Test 0 -     SUCCESS
Test 1 -     SUCCESS
Test 2 - *** FAILURE: post-condition false
Test 3 - *** FAILURE: post-condition false
Test 4 - *** FAILURE: post-condition false
Test 5 - *** FAILURE: post-condition false
Test 6 - *** FAILURE: post-condition false
Test 7 - *** FAILURE: post-condition false
Test 8 - *** FAILURE: post-condition false
Test 9 - *** FAILURE: post-condition false
Test 10 - *** FAILURE: post-condition false
Test 11 - *** FAILURE: post-condition false
Test 12 - *** FAILURE: post-condition false
Test 13 - *** FAILURE: post-condition false
Test 14 - *** FAILURE: post-condition false
Test 15 - *** FAILURE: post-condition false
Test 16 - *** FAILURE: post-condition false
Test 17 - *** FAILURE: post-condition false
Test 18 - *** FAILURE: post-condition false
Test 19 - *** FAILURE: post-condition false
Test 20 - *** FAILURE: post-condition false
Test 21 - *** FAILURE: post-condition false
Test 22 -     SUCCESS
Test 23 -     SUCCESS
Test 24 - *** FAILURE: post-condition false
Test 25 - *** FAILURE: post-condition false
Test 26 - *** FAILURE: post-condition false
Test 27 - *** FAILURE: post-condition false
Test 28 - *** FAILURE: post-condition false
Test 29 - *** FAILURE: post-condition false
Test 30 - *** FAILURE: post-condition false
Test 31 - *** FAILURE: post-condition false
Test 32 - *** FAILURE: post-condition false


Summary:
--------
Number successful tests cases: 4 of 33 (ca. 12%)
Number of warnings:             0 of 33 (ca. 0%)
Number of errors:               0 of 33 (ca. 0%)
Number of failures:             29 of 33 (ca. 87%)
Number of fatal errors:         0 of 33 (ca. 0%)

Overall result: failed 
===============
\end{verbatim}
}
\caption{A Sample Test Trace for the Permutation Test Scenario}
\label{tab:test-trace2}
\end{table}
*}

subsection{*Summary*}
text{* A comparison of the three scenarios reveals that albeit a reasonable degree
of automation in the test generation process, the essence of model-based test case
generation remains an \emph{interactive process} that is worth to be documented in a formal
test-plan with respect to various aspects: the concrete modeling that is chosen,
the precise formulation of the test-specifications (or: test-goals), the configuration
and instrumentation of the test-data selection process, the test-driver synthesis and
execution. This process can be complemented by proofs establishing equivalences 
allowing to convert initial test-specifications into more executable ones, or more 
'symbolically evaluatable' ones, or that help to reduce the complexity of the constraint-
resolution in the test-data selection process. *}

text{* But the most important aspect remains: what is a good testing model ? Besides
the possibility that the test specification simply does not test what the tester had
in mind, the test theory and test-specification have a crucial importance on the 
quality of the generated test data that seems to be impossible to capture automatically.*}

section {* Non-Inherent Higher-order Testing *}
text{*  HOL-TestGen can use test specifications that contain
higher-order operators --- although we would not claim that the test case 
generation is actually higher-order (there are no enumeration schemes
for the function space, so function variables are untreated by the
test case generation procedure so far). *}

text{* Just for fun, we reformulate the problem of finding the
maximal number in a list as a higher-order problem: *}

test_spec "foldr max l (0::int) = PUT2 l"
apply(gen_test_cases "PUT2" simp:max_def)
mk_test_suite "maximal_number"

declare [[testgen_iterations = 200]]
gen_test_data "maximal_number"

print_conc_tests (0) "maximal_number"



end
