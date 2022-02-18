(*****************************************************************************
 * HOL-TestGen --- theorem-prover based test case generation
 *                 http://www.brucker.ch/projects/hol-testgen/
 *                                                                            
 * max_test.thy --- the "Max" example
 * This file is part of HOL-TestGen.
 *
 * Copyright (c) 2005-2007 ETH Zurich, Switzerland
 *               2013-2015 Achim D. Brucker, Germany
 *               2016      The University of Sheffield
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
(* $Id: Max_test.thy 12977 2017-01-05 21:10:51Z brucker $ *)

chapter {* Introduction *}

theory 
  Max_test
imports   
  "~~/src/HOL/Library/Code_Target_Numeral"
  Code_Integer_Fsharp
  Testing
begin

text{* This introductory example explains the standard 
       \testgen{} method resulting in a formalized test 
       plan that is documented in a machine-checked 
       text like this theory document.

       We declare the context of this document---which must be the
       theory ``Testing'' at least in order to include the \testgen{}
       system libraries---and the type of the program under test.  *}


consts prog :: "int \<Rightarrow> int \<Rightarrow> int"

text{* Assume we want to test a simple program computing the 
       maximum value of two integers. We start by writing our 
       test specification:
     *}

test_spec "(prog a b) = (max a b)"

  txt {*
      By applying @{term gen_test_cases} we bring the proof
      state into testing normal form (\TNF)
      (see~\cite{brucker.ea:symbolic:2005} for details). 
      *}

  apply(gen_test_cases  "prog" simp: max_def)

  txt {* 
      which leads to the test partitioning one would expect:
      @{subgoals [display, goals_limit=50]}.

      Now we bind the test theorem to a particular name
      in the test environment:
      *}

  mk_test_suite "max_test"



text {* This concludes the test case generation phase.
      Now we turn to the test data generation, which
      is---based on standard configurations in the
      test environment to be discussed in later 
      examples---just the top-level command:
      *}

  gen_test_data "max_test" 

text {* The Isabelle command \texttt{thm} allows for
      interactive inspections of the result: *}

  print_conc_tests max_test


(* TODO : define print attribute :
text {* which is:

        @{thm [display] max_test.concrete_tests} 

        in this case. *}
*)

text {* Analogously, we can also inspect the test hypotheses 
        and the test theorem: *}

  print_thyps max_test

(* TODO : define print attribute :
text {* which yields: 
 
        @{thm [display] max_test.test_hyps} 

        and
      *}
*)

  thm max_test.test_thm

text {* resulting in:

        @{thm [display] max_test.test_thm} *}




text {* We turn now to the automatic generation of a test harness.
        This is performed by the top-level command: *}
code_printing 
  constant prog => (Fsharp) "myMax.max"
           and     (SML)    "(Int'_of'_integer (myMax.max (integer'_of'_int ((_))) (integer'_of'_int ((_)))))"
           and     (Scala)  "(int'_of'_integer (myMax.max ((integer'_of'_int ((_))), (integer'_of'_int ((_))))))"
  
generate_test_script "max_test"
thm max_test.test_script

text {* Testing an SML implementation: *}
export_code max_test.test_script in SML    module_name TestScript file "impl/sml/max_test_script.sml"

text {* We use the SML implementation also for testing an implementation written in C: *}
export_code max_test.test_script in SML    module_name TestScript file "impl/c/max_test_script.sml"

text {* Testing an F\# implementation: *}
export_code max_test.test_script in Fsharp module_name TestScript file "impl/fsharp/max_test_script.fs"

text {* Testing a Scala implementation: *}
export_code max_test.test_script in Scala module_name TestScript file "impl/scala/max_test_script.scala"

text {* Finally, we export the raw test data in an XML-like format: *}
export_test_data "impl/data/max_data.dat" max_test


text {* which generates:
\lstinputlisting[style=sml]{../max_script.sml}
*}
(*<*)
end
(*>*)
