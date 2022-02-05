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

chapter {* Utilities for the various backends *}

theory BackendUtils
imports TestEnv

begin

ML{* 

structure BackendUtils =
struct

fun certify_pairs ctxt l = map (fn (Var(x,t),y) => ((x,  t), Thm.cterm_of ctxt y)) l
fun uncertify_pairs l = map (fn (x,(a,t)) => (Thm.term_of x, Var (a,t))) l

fun solve_by_simp_tac ctxt = SOLVED' (full_simp_tac ctxt)
fun solve_by_simp_or_auto_tac ctxt = 
  let
    val pon = Config.get ctxt TestEnv.pon
    val solved' = if (pon = 0) then SOLVED' else (fn x => x)
    val full_simp = full_simp_tac ctxt
    val clarsimp = clarsimp_tac ctxt
    (* val metis = Metis_Tactic.metis_tac [] ATP_Proof_Reconstruct.metis_default_lam_trans ctxt (TestEnv.get_smt_facts ctxt) *)
    (* We can use SMT from the standard library, no need for the patch here *)
    val smt =  SMT_Solver.smt_tac ctxt (TestEnv.get_smt_facts ctxt)
    (* val use_metis = Config.get ctxt TestEnv.use_metis *)
    val use_smt = Config.get ctxt TestEnv.use_smt
    val tactic = if use_smt then (
                   fn y => (SOLVE (full_simp y))
                    ORELSE (SOLVE (clarsimp y))
                    ORELSE (smt y)
                  ) else (
                   fn y => (SOLVE (full_simp y))
                    ORELSE (SOLVE (clarsimp y))
                    ORELSE (auto_tac ctxt)
                  )
  in solved' tactic
  end

fun premvars n thm = let
    val prem = Logic.nth_prem(n, Thm.prop_of thm)
in
    map Var (Term.add_vars prem [])
end

end

*}

end
