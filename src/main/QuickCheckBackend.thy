(*****************************************************************************
 * HOL-TestGen --- theorem-prover based test case generation
 *                 http://www.brucker.ch/projects/hol-testgen/
 *                                                                            
 * TestGen.thy --- the core of the HOL-TestGen System.
 * This file is part of HOL-TestGen.
 *
 * Copyright (c) 2005-2010 ETH Zurich, Switzerland
 *               2008-2013 Achim D. Brucker, Germany
 *               2009-2013 Universite Paris-Sud, France
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

chapter {* The QuickCheck backend *}

theory QuickCheckBackend
imports 
  HOL.HOL
  HOL.Int
  HOL.List
  TestEnv
  BackendUtils

begin


ML{* 

structure QuickCheckBackend =
struct

fun list_abs_var t [] = t
  | list_abs_var t ((x as Var(_, T))::vars) = Abs(Name.internal Name.uu, T, abstract_over(x, list_abs_var t vars))

fun iterate f 0 = NONE
  | iterate f k = case f () handle Match => NONE
                   of NONE => iterate f (k - 1) | SOME q => SOME q;

fun quickcheck_tac' ctxt iters n thm =
  let
      val size = 15
      val thy = Proof_Context.theory_of ctxt
      val vars = BackendUtils.premvars n thm
      val prem = Logic.nth_prem(n, Thm.prop_of thm)
      val neg =  @{term Not} $ (HOLogic.dest_Trueprop prem)
      val neg' = list_abs_var neg vars

	  (*	TODO: use new code generation
	  
	  val tester = Codegen.test_term ctxt n 
	  
	  *)
	  fun tester x = NONE
      fun with_tester k = iterate (fn () => tester k) iters
      fun with_size k = if k > size then NONE
                        else
                            (case with_tester k
                              of NONE => with_size (k + 1)
                               | SOME q => SOME q);
  in case with_size 1 of
         SOME insts => let
             val instantiated = Drule.instantiate_normalize
                                      ([], BackendUtils.certify_pairs ctxt (vars ~~ insts)) thm
         in
             full_simp_tac ctxt n instantiated
         end
       | NONE => Seq.empty
  end

fun quickcheck_tac ctxt iters n thm = let
    val tac = Object_Logic.full_atomize_tac ctxt THEN' (quickcheck_tac' ctxt iters)
in 
    (case (Seq.pull (tac n thm)) of 
         SOME (x, xq) => Seq.single x
       | NONE => Seq.empty)
    handle ERROR _ => Seq.empty (* Catch "unable to generate code" exceptions *) 
end

end

*}

end
