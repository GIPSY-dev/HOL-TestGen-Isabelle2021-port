(*****************************************************************************
 * HOL-TestGen --- theorem-prover based test case generation
 *                 http://www.brucker.ch/projects/hol-testgen/
 *                                                                            
 * Triangle_test.thy --- testing the classical triangle example
 * This file is part of HOL-TestGen.
 *
 * Copyright (c) 2003-2007 ETH Zurich, Switzerland
 *               2009-2015 Achim D. Brucker, Germany
 *               2009-2010 Univ. Paris-Sud, France
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
(* $Id: Triangle_test.thy 12977 2017-01-05 21:10:51Z brucker $ *)


chapter {* Testing the Triangle Example *}

theory 
  Triangle_test
imports
  Triangle
   "~~/src/HOL/Library/Code_Target_Numeral"
   Code_Integer_Fsharp
begin

declare [[testgen_profiling]]

text{* The test theory \texttt{Triangle\_test} is used to demonstrate 
       the pragmatics  of \testgen{} in the standard triangle example;
       The demonstration elaborates three test plans: standard test 
       generation (including test driver generation), abstract test data
       based test generation, and abstract test data based
       test generation reusing partially synthesized abstract
       test data. *}


section {* The Standard Workflow *}

    text {* We start with stating a test specification for
       a program under test: it must behave as specified in the definition 
       of @{text classify_triangle}.

       Note that the variable @{term program} is used to label an
       arbitrary implementation of the current \index{program under
       test}program under test that should fulfill the test
       specification: *}

consts program :: "int * int * int => triangle"

test_spec "program(x,y,z) = triangle_classifier_spec x y z"

    txt {* By applying @{term gen_test_cases} we bring the proof state into 
           testing normal form (TNF). *}

    apply(gen_test_cases  "program" simp add: is_triangle_def
                                              triangle_classifier_spec_def)

    (* 35 Goals: 17 THYP / 18 test cases *)
    txt {* In this example, we decided to generate symbolic test cases
           and to unfold the triangle predicate by its definition before 
           the process. This leads to a formula with, among others, the following clauses: 
           @{subgoals [display, goals_limit=5]} *}
    (*\
    Exercise: compare  these with the  results of Dick and 
    Faivre~\cite{dick.ea:testing:1993}.
    *)
    txt {* Note that the computed \TNF is not minimal, i.e. further simplification and
           rewriting steps are needed to compute the \emph{minimal set of
           symbolic test cases}. The following post-generation simplification
           improves the generated result before ``frozen'' into a \emph{test theorem}: *}

    apply(simp_all) 

    txt {* Now, ``freezing'' a test theorem\index{test theorem} technically means 
           storing it into a specific data structure provided by \testgen, namely a \emph{test
           environment}\index{test environment} called @{term triangle_test} that captures all 
           data relevant to a test. The test-environment is the basis for the future steps,
           that is, the test data generation and the generation of the test-drivers for
           the external (black-box) programs under test. *}

    mk_test_suite "triangle_test"


text {* For example, @{term triangle_test} contains the test-theorem which can be projected
        and displayed by the usual Isar command \verb+thm+. *}
 
thm "triangle_test.test_thm"

text{*  We compute the concrete \emph{test statements} by instantiating
        variables by constant terms in the symbolic test cases for
        ``@{term program}'' via a random test procedure: *}

gen_test_data "triangle_test"

(* TODO: Attribute 
text {* which stores its results inside @{term triangle_test} 
        to  @{thm[display] triangle_test.concrete_tests } *}
*)

print_thyps "triangle_test" 
print_conc_tests "triangle_test"

text{*  Now we use the generated test data statement lists to automatically
        generate a test driver, which is controlled by the test harness.
        The first argument is the external SML-file name into which the 
        test driver is generated, the second argument the name of the
        test data statement set and the third the name of the (external)
        program under test.

        For demonstration purposes, we generate test drivers to several 
        different programming languages, which will each be linked to
        a different (black-box) implementation in their respective programming language. 
     *}


code_printing
  constant program => (Fsharp) "myTriangle.testTriangle"
           and        (SML)    "((fn (a,(b,c)) => myTriangle.testTriangle ((integer'_of'_int ((a))), ((integer'_of'_int ((b))), (integer'_of'_int ((c)))))))" 
           and        (Scala)  "myTriangle.testTriangle" 

code_printing
  type_constructor triangle => (SML) "myTriangle.triangle"

code_printing 
  constant  "equilateral" => (SML) "myTriangle.Equilateral"
code_printing 
  constant  "scalene"     => (SML) "myTriangle.Scalene"
code_printing 
  constant  "isosceles"   => (SML) "myTriangle.Isosceles"
code_printing 
  constant  "error"       => (SML) "myTriangle.Error"

generate_test_script "triangle_test"
thm triangle_test.test_script

text {* Testing an SML implementation: *}
export_code triangle_test.test_script in SML    module_name TestScript file "impl/sml/triangle_test_script.sml"

text {* We use the SML implementation also for testing an implementation written in C: *}
export_code triangle_test.test_script in SML    module_name TestScript file "impl/c/triangle_test_script.sml"

text {* Testing an F\# implementation: *}
export_code triangle_test.test_script in Fsharp module_name TestScript file "impl/fsharp/triangle_test_script.fs"

text {* Testing a Scala implementation: *}
export_code triangle_test.test_script in Scala module_name TestScript file "impl/scala/triangle_test_script.scala"

text {* Finally, we export the raw test data in an XML-like format: *}
export_test_data "impl/data/triangle_data.dat" triangle_test


section {* The Modified Workflow: Using Abstract Test Data *}

text {* 
  There is a viable alternative to the standard development process above: 
  instead of unfolding triangle and trying to generate ground substitutions
  satisfying the constraints, one may keep triangle in the test theorem, treating
  it as a building block for new constraints. 
  Such building blocks will also be called 
  \index{abstract test case}\emph{abstract test cases}.

  In the following, we will set up a new version of the
  test specification, called @{term triangle2}, and prove the
  relevant abstract test cases individually before test case 
  generation. These proofs are highly automatic, but the choice 
  of the abstract test data in itself is ingenious,
  of course. 
*}
(*
  Nevertheless, the computation for establishing if
  a certain triple is encapsulated in these proofs, deliberating the 
  main test case generation of @{term triangle2} from them. 
  In fact, these contain 5 arithmetic constraints which represent 
  already a sensible load if given to the random solver. 
*)
text {*
  The abstract test data will be assigned to the subsequent
  test generation for the test specification @{term triangle2}.
  Then the test data generation phase is started for @{term triangle2}
  implicitly using the abstract test cases. The association 
  established by this assignment is also stored in the test
  environment.

  The point of having abstract test data is that it can be generated 
  ``once and for all'' and inserted before the test data selection 
  phase producing a ``partial'' grounding. It will turn out that the 
  main state explosion is shifted from the test case generation to the 
  test data selection phase. 
  *}


subsection{* Using explicit (derived) test-instances *}

text{* There is an Isar-attribute \verb+test_inst+ that allows for declaring theorems as 
       test instances, \ie{} concrete instantiations of a test-class. Technically, this 
       works by unifying the lemma against the proof obligations (which instantiates the
       schema variables and erases the obligation).
*}
lemma triangle_abscase1 [test_inst "triangle2"]: "is_triangle 1 1 1"
  by(auto simp: is_triangle_def)

lemma triangle_abscase2 [test_inst"triangle2"]:"is_triangle 1 2 2"
  by(auto simp: is_triangle_def)

lemma triangle_abscase3 [test_inst"triangle2"]:"is_triangle 2 1 2"
  by(auto simp: is_triangle_def)

lemma triangle_abscase4 [test_inst"triangle2"]:"is_triangle 2 2 1"
  by(auto simp: is_triangle_def)

lemma triangle_abscase5 [test_inst"triangle2"]:"is_triangle 3 4 5"
  by(auto simp: is_triangle_def)

lemma triangle_abscase6 [test_inst"triangle2"]:"\<not> is_triangle (-1) 1 2"
  by(auto simp: is_triangle_def)

lemma triangle_abscase7 [test_inst"triangle2"]:"\<not> is_triangle 1 (-1) 2"
  by(auto simp: is_triangle_def)

lemma triangle_abscase8 [test_inst"triangle2"]:"\<not> is_triangle 1 2 (-1)"
  by(auto simp: is_triangle_def)

lemma triangle_abscase9 [test_inst "triangle2"]: "\<not> is_triangle (-1) (-1) (-1)"
  by(auto simp: is_triangle_def)

lemma triangle_abscase10 [test_inst "triangle2"]: "\<not> is_triangle (-1) 1 (-1)"
  by(auto simp: is_triangle_def)

lemma triangle_abscase11 [test_inst "triangle2"]: "\<not> is_triangle 1 (-1) (-1)"
  by(auto simp: is_triangle_def)

lemma triangle_abscase12 [test_inst "triangle2"]: "\<not> is_triangle (-1) (-1) 1"
  by(auto simp: is_triangle_def)

text{* A means to inspect the test environment is given by:*}   
print_testenv "triangle2"
text{* ... or without filter: *}
print_testenv ""

text{* Just for demonstration purposes, we apply the abstract test data solver
directly in the proof: *}

test_spec "prog(x,y,z) = triangle_classifier_spec x y z"
  apply(gen_test_cases "prog" simp add: triangle_classifier_spec_def)
  apply(discharge_POs "triangle2")
  (* or alternatively more low-level: 
  apply(tactic "TestGen.discharge_POs \"triangle2\" @{context}")
  *)
oops 

text{* The previous version discharges and eliminates PO's from the test theorem.
Alternatively, one can leave them inside and discharge them later during the test data selection 
phase. *}
 
test_spec "prog(x,y,z) = triangle_classifier_spec x y z"
  apply(gen_test_cases "prog" simp add: triangle_classifier_spec_def)
  mk_test_suite "triangle2"
thm "triangle2.test_thm"


gen_test_data "triangle2"
print_conc_tests triangle2

(* TODO Attribute
text{* The test data generation is started and implicitly uses 
       the abstract test data assigned to the test theorem 
       \emph{triangle2}. Again, we inspect the results:
@{thm[display] triangle2.concrete_tests} *}
*)
 
print_thyps "triangle2" 
print_conc_tests "triangle2"

subsection{* Alternative: Synthesizing Abstract Test Data *}

text {* In fact, part of the ingenious work of generating abstract
        test data can be synthesized by using the test case generator
        itself. This usage scenario proceeds as follows:
        \begin{enumerate}
        \item we set up a decomposition of @{term triangle}
              in an equality to itself; this identity is disguised
              by introducing a variable @{term prog} which is stated 
              equivalent to @{term triangle} in an assumption,  
        \item the introduction of this assumption is delayed; i.e.
              the test case generation is performed in a state
              where this assumption is not visible,
        \item after executing test case generation, we fold back 
              @{term prog} against @{term triangle}.
        \end{enumerate}
  *}

test_spec abs_triangle : 
assumes 1: "prog = triangle" 
shows      "is_triangle x y z = prog x y z"
  apply(gen_test_cases "prog" simp add: is_triangle_def)
  apply(simp_all add: 1)
mk_test_suite "abs_triangle"


text {* which results in  @{thm[display] abs_triangle.test_thm} Thus, we
        constructed  test cases for being triangle or not in 
        terms of arithmetic constraints. These are amenable to
        test data generation by increased random solving, which
        is controlled by the test environment variable \verb+iterations+:*}

declare [[testgen_iterations=100]]
gen_test_data "abs_triangle"
(* TODO Attribute
text {* resulting in: @{thm[display] abs_triangle.concrete_tests} *}
*)

text {* Thus, we achieve solved ground instances for abstract test data. 
        Now, we assign these synthesized test data to the new future
        test data generation. Additionally to the synthesized abstract
        test data, we assign the data for isosceles and equilateral
        triangles; these can not be revealed from our synthesis since
        it is based on a subset of the constraints available in the
        global test case generation. *}

(* TODO 
declare abs_triangle.concrete_tests[test_inst"triangle3"]
*)
declare triangle_abscase1[test_inst"triangle3"]
declare triangle_abscase2[test_inst"triangle3"]
declare triangle_abscase3[test_inst"triangle3"]


text {* The setup of the testspec is identical as for triangle2; it is 
        essentially a renaming. *}
     
test_spec "program(x,y,z) = triangle_classifier_spec x y z"
  apply(simp add: triangle_classifier_spec_def)
  apply(gen_test_cases  "program" simp add: triangle_classifier_spec_def)
  mk_test_suite "triangle3"


text{* The test data generation is started again on the
       basis on synthesized and selected hand-proven abstract 
       data. *}

declare [[testgen_iterations=10]]
gen_test_data "triangle3"

print_thyps "triangle3" 
print_conc_tests "triangle3"
(* TODO Attribute
text {* resulting in: @{thm[display] triangle3.concrete_tests}. *}
 *)
end
