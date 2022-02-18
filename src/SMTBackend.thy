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

chapter {* The SMT backend *}

theory SMTBackend
imports 
  clocks
  BackendUtils
  "smt_patch/Old_SMT_patch"
  "new_smt_patch/SMT_patch"

begin


ML{* 

signature SMTBACKEND = sig
  (* The main tactic to call the SMT backend on a PO *)
  val testgen_smt_tac : Proof.context -> int -> tactic
end

*}

(* Common part between the two interfaces *)

lemma add_bound: "\<lbrakk> P \<and> (size x) <= k \<rbrakk> \<Longrightarrow> P" by(auto)

ML{*

(* Backported from Isabelle 13-2 *)
fun matches_subterm thy (pat, obj) =
  let
    fun msub bounds obj = Pattern.matches thy (pat, obj) orelse
      (case obj of
        Abs (x, T, t) => msub (bounds + 1) (snd (Term.dest_abs (Name.bound bounds, T, t)))
      | t $ u => msub bounds t orelse msub bounds u
      | _ => false)
  in msub 0 obj end;

*}


(* Old interface (deprecated, will be removed in next versions) *)

declare [[old_smt_solver = z3]]
declare [[old_z3_options = "AUTO_CONFIG=false MBQI=false"]]
declare [[old_smt_oracle = true]]
declare [[old_z3_with_extensions = true]]
declare [[old_smt_datatypes = true]]

(* abbreviation "trigger == Old_SMT_patch.trigger"
abbreviation "pat == Old_SMT_patch.pat" *)

lemma old_trigger_intr: "(x = y) \<Longrightarrow> Old_SMT_patch.trigger [[Old_SMT_patch.pat (x)]] (x = y)" 
by(simp add: Old_SMT_patch.trigger_def)


ML{*

structure OldSMTBackend : SMTBACKEND = struct

fun trig_thm thy thm = 
    let  val is_trig = matches_subterm thy (@{const Old_SMT_patch.trigger}, Thm.prop_of thm)
                       orelse not (exists_subterm is_Var (Thm.prop_of thm))
    in
         if is_trig then thm else thm RS @{thm "old_trigger_intr"} handle THM _ => thm
    end

fun pretty_insts ctxt msg insts = let
    fun mkeq (x,y) = Const(@{const_name HOL.eq}, dummyT) $ x $ y
    val pretty_insts = map (fn inst => (Syntax.pretty_term ctxt (mkeq inst))) insts
in
    Pretty.string_of (Pretty.big_list (msg^":") pretty_insts)
end

fun scan_def (Const (@{const_name HOL.eq}, _) $ t $ u) = (t,u)
  | scan_def _ = error ("Unexpected SMT counterexample format")

fun mkinsts thy vars ce tr = let
    val defs = map scan_def ce
    val _ = if tr then tracing (pretty_insts @{context} "Raw SMT counterexample" defs) else ()
    val defs' = defs @ (map swap defs)

    (* The defs that are directly usable *)
    fun is_Free_or_Var t = (is_Free t) orelse (is_Var t)
    val real_defs = filter (fn (x,_) => is_Free_or_Var x) defs'
    val _ = if tr then tracing (pretty_insts @{context} "SMT counterexample after filtering real defs" real_defs) else ()
    
    (* The defs of functions that we have to infer from their partial definition via equalities
       (might want to change this by looking directly at ce) *)
    fun insert (t1, t2, u) acc = case acc of
        [] => [(t1, [t2], [u])]
      | (t1', t2s, us)::acc => if t1' = t1 then (t1', t2::t2s, u::us)::acc else (t1', t2s, us)::(insert (t1, t2, u) acc)
    fun aggregate_fun_defs acc l = case l of
        [] => acc
      | (t1 $ t2, u)::l => if is_Free_or_Var t1 then aggregate_fun_defs (insert (t1, t2, u) acc) l else (aggregate_fun_defs acc l)
      | _::l => aggregate_fun_defs acc l
    val aggregates = aggregate_fun_defs [] defs'
    fun mk_body x Tx Tu t2s us = case t2s of
        [t2] => (case us of [u] => u)
      | t2::t2s => (case us of u::us => (Const (@{const_name HOL.If}, HOLogic.boolT --> Tu --> Tu --> Tu)) $ ((Const (@{const_name HOL.eq}, Tx --> Tx --> HOLogic.boolT)) $ x $ t2) $ u $ (mk_body x Tx Tu t2s us)) (* if x = t2 then u else mk_body x t2s us *)
    fun mk_fun_defs l = case l of
        [] => []
      | (t1, t2::t2s, u::us)::l => let
        val Tx = fastype_of t2
        val name = "xMkFun"
        val x = (name, Tx)
        val Tu = fastype_of u
      in (t1, absfree x (mk_body (Free x) Tx Tu (t2::t2s) (u::us)))::(mk_fun_defs l) end
    val fun_defs = mk_fun_defs aggregates
    val _ = if tr then tracing (pretty_insts @{context} "SMT counterexample with partial defs of functions" fun_defs) else ()
    
    (* Generation of the instantiation *)
    val all_defs = real_defs @ fun_defs
    val var_insts = map (fn x => (x, subst_atomic all_defs x)) vars
    val _ = if tr then tracing (pretty_insts @{context} "Generated instantiation from SMT counterexample" var_insts) else ()
in
    BackendUtils.certify_pairs thy var_insts
end

val (profiling, profiling_setup) = Attrib.config_bool @{binding testgen_profiling} (K false);

(* a wrapper around smt_tac' that fixes the provided counterexamples *)
fun smt_ce_tac ctxt rules = 
Subgoal.FOCUS(fn {context, prems, schematics, ...} => (fn thm => 
let
    val prof_name = "SMT"
    val start_tac = (if Config.get ctxt profiling   
                     then Clocks.start_clock_tac prof_name 
                     else all_tac)
    val stop_tac =  (if Config.get ctxt profiling 
                     then Clocks.stop_clock_tac prof_name 
                     else all_tac)
in
    (start_tac 
     THEN (Old_SMT_patch_Solver.smt_tac' context (rules @ prems) 1) 
     THEN stop_tac) thm
    |> Seq.hd 
    |> Seq.single
                                                                                                      
    handle Old_SMT_patch_Failure.SMT (Old_SMT_patch_Failure.Counterexample {is_real_cex = is_real_cex', 
                                                        free_constraints, 
                                                        const_defs}) => 
           let
               val _ = if Config.get ctxt profiling then Clocks.stop_clock prof_name else ()
               val inv_insts = map swap (snd schematics)
               val term_insts = BackendUtils.uncertify_pairs inv_insts
               val free_constraints' = map (subst_atomic term_insts) free_constraints
               val const_defs' = map (subst_atomic term_insts) const_defs
           in
               raise Old_SMT_patch_Failure.SMT 
                         (Old_SMT_patch_Failure.Counterexample {is_real_cex = is_real_cex', 
                                                      free_constraints = free_constraints', 
                                                      const_defs = const_defs'})
           end

         | exc => let  val _ = if Config.get ctxt profiling 
                               then Clocks.stop_clock prof_name 
                               else ()
           in
               raise exc
           end

end)) ctxt


fun try_inst_tac ctxt insts n thm = let
    val thm' = Drule.instantiate_normalize ([], insts) thm
in
    BackendUtils.solve_by_simp_or_auto_tac ctxt n thm'
end
    
fun smt_inst_tac ctxt rules n thm = let
    val prem = Logic.nth_prem(n, Thm.prop_of thm)
    val neg = @{const Pure.imp}
                    $ prem
                    $ (@{const "Trueprop"} $ @{const "False"})
    val goal = Goal.init (Thm.cterm_of ctxt neg) 
in
    (Seq.hd (smt_ce_tac ctxt rules 1 goal); Seq.empty) 
    handle Old_SMT_patch_Failure.SMT (Old_SMT_patch_Failure.Counterexample {free_constraints, const_defs, ...}) 
           => try_inst_tac ctxt (mkinsts ctxt (BackendUtils.premvars n thm) (free_constraints @ const_defs) (Config.get ctxt TestEnv.smt_model)) n thm
         | Old_SMT_patch_Failure.SMT _ => Seq.empty
end

(* fun add_bound_tac ctxt bound t =
    Subgoal.FOCUS_PARAMS(fn {context, schematics, ...} => let
                                val thy = Proof_Context.theory_of context
                                val ct = Thm.instantiate_cterm schematics (cterm_of thy t)
                                val bound_term = cterm_of thy (HOLogic.mk_nat bound)
                                val xtype = ctyp_of thy (TVar (("'a",0), @{sort "Nat.size"}))
                                val tinst = (xtype, ctyp_of_term ct)
                                val k = cterm_of thy (Var (("k",0), @{typ "nat"}))
                                val x = cterm_of thy (Var (("x",0), type_of t))
                                val inst1 = (k, bound_term)
                                val inst2 = (x, ct)
                            in
                                TacticPatch.res_terminst_tac [tinst] [inst1, inst2] @{thm add_bound} 1
                            end) ctxt

fun add_bounds_tac ctxt bound ts = let
    fun next (t, tac) = tac THEN' (add_bound_tac ctxt bound t)
in
    List.foldl next (K all_tac) ts
end

fun bounded_smt_tac ctxt bound rules =
    Subgoal.FOCUS_PARAMS(fn {context, ...} => 
                            (fn thm => let
                                    val thy = Proof_Context.theory_of context
                                    val datatype_vars = filter (fn x => isDataType thy (type_of x)) 
                                                               (premvars 1 thm)
                                in
                                    EVERY[add_bounds_tac context bound datatype_vars 1,
                                          smt_inst_tac context rules 1,
                                          ALLGOALS (full_simp_tac context)] thm
                                end)) ctxt *)

fun unbounded_smt_tac ctxt rules =
    Subgoal.FOCUS_PARAMS(fn {context, ...} => 
                            (fn thm =>
                                    EVERY[smt_inst_tac context rules 1,
                                          ALLGOALS (full_simp_tac context)] thm
                                )) ctxt
  
fun testgen_smt_tac ctxt =
  let
    val thy = Proof_Context.theory_of ctxt
    val smt_facts = map (trig_thm thy) (TestEnv.get_smt_facts ctxt)
  in
    unbounded_smt_tac ctxt smt_facts
    (* bounded_smt_tac ctxt (Config.get ctxt TestEnv.depth) smt_facts *)
  end

end

*}


(* New interface *)

declare [[smt_solver = z3]]
declare [[z3_options = "AUTO_CONFIG=false smt.mbqi=false"]]
declare [[smt_oracle = true]]
declare [[z3_extensions = true]]

lemma trigger_intr: "(x = y) \<Longrightarrow> SMT_patch.trigger (SMT_patch.Symb_Cons (SMT_patch.Symb_Cons (SMT_patch.pat (x)) SMT_patch.Symb_Nil) SMT_patch.Symb_Nil) (x = y)" 
by(simp add: SMT_patch.trigger_def)


ML{*

structure NewSMTBackend : SMTBACKEND = struct

fun trig_thm thy thm = 
    let  val is_trig = matches_subterm thy (@{const SMT_patch.trigger}, Thm.prop_of thm)
                       orelse not (exists_subterm is_Var (Thm.prop_of thm))
    in
         if is_trig then thm else thm RS @{thm "trigger_intr"} handle THM _ => thm
    end

fun pretty_insts ctxt msg insts = let
    fun mkeq (x,y) = Const(@{const_name HOL.eq}, dummyT) $ x $ y
    val pretty_insts = map (fn inst => (Syntax.pretty_term ctxt (mkeq inst))) insts
in
    Pretty.string_of (Pretty.big_list (msg^":") pretty_insts)
end

fun mkinsts thy vars defs tr = let
    val _ = if tr then tracing (pretty_insts @{context} "Raw SMT counterexample" defs) else ()
    val defs' = defs @ (map swap defs)

    (* The defs that are directly usable *)
    fun is_Free_or_Var t = (is_Free t) orelse (is_Var t)
    val real_defs = filter (fn (x,_) => is_Free_or_Var x) defs'
    val _ = if tr then tracing (pretty_insts @{context} "SMT counterexample after filtering real defs" real_defs) else ()
    
    (* The defs of functions that we have to infer from their partial definition via equalities
       (might want to change this by looking directly at ce) *)
    fun insert (t1, t2, u) acc = case acc of
        [] => [(t1, [t2], [u])]
      | (t1', t2s, us)::acc => if t1' = t1 then (t1', t2::t2s, u::us)::acc else (t1', t2s, us)::(insert (t1, t2, u) acc)
    fun aggregate_fun_defs acc l = case l of
        [] => acc
      | (t1 $ t2, u)::l => if is_Free_or_Var t1 then aggregate_fun_defs (insert (t1, t2, u) acc) l else (aggregate_fun_defs acc l)
      | _::l => aggregate_fun_defs acc l
    val aggregates = aggregate_fun_defs [] defs'
    fun mk_body x Tx Tu t2s us = case t2s of
        [t2] => (case us of [u] => u)
      | t2::t2s => (case us of u::us => (Const (@{const_name HOL.If}, HOLogic.boolT --> Tu --> Tu --> Tu)) $ ((Const (@{const_name HOL.eq}, Tx --> Tx --> HOLogic.boolT)) $ x $ t2) $ u $ (mk_body x Tx Tu t2s us)) (* if x = t2 then u else mk_body x t2s us *)
    fun mk_fun_defs l = case l of
        [] => []
      | (t1, t2::t2s, u::us)::l => let
        val Tx = fastype_of t2
        val name = "xMkFun"
        val x = (name, Tx)
        val Tu = fastype_of u
      in (t1, absfree x (mk_body (Free x) Tx Tu (t2::t2s) (u::us)))::(mk_fun_defs l) end
    val fun_defs = mk_fun_defs aggregates
    val _ = if tr then tracing (pretty_insts @{context} "SMT counterexample with partial defs of functions" fun_defs) else ()
    
    (* Generation of the instantiation *)
    val all_defs = real_defs @ fun_defs
    val var_insts = map (fn x => (x, subst_atomic all_defs x)) vars
    val _ = if tr then tracing (pretty_insts @{context} "Generated instantiation from SMT counterexample" var_insts) else ()
in
    BackendUtils.certify_pairs thy var_insts
end

val (profiling, profiling_setup) = Attrib.config_bool @{binding testgen_profiling} (K false);

(* a wrapper around smt_tac' that fixes the provided counterexamples *)
fun smt_ce_tac ctxt rules = 
Subgoal.FOCUS(fn {context, prems, schematics, ...} => (fn thm => 
let
    val prof_name = "SMT"
    val start_tac = (if Config.get ctxt profiling   
                     then Clocks.start_clock_tac prof_name 
                     else all_tac)
    val stop_tac =  (if Config.get ctxt profiling 
                     then Clocks.stop_clock_tac prof_name 
                     else all_tac)
in
    (start_tac 
     THEN (SMT_patch_Solver.smt_get_model_tac context (rules @ prems) 1) 
     THEN stop_tac) thm
    |> Seq.hd 
    |> Seq.single
                                                                                                      
    handle SMT_patch_Solver.SMT_Model {const_defs} => 
           let
               val _ = if Config.get ctxt profiling then Clocks.stop_clock prof_name else ()
               val inv_insts = map swap (snd schematics)
               val term_insts = BackendUtils.uncertify_pairs inv_insts
               (* val free_constraints' = map (subst_atomic term_insts) free_constraints *)
               val const_defs' = map (apply2 (subst_atomic term_insts)) const_defs
           in
               raise SMT_patch_Solver.SMT_Model {const_defs = const_defs'}
           end

         | exc => let  val _ = if Config.get ctxt profiling 
                               then Clocks.stop_clock prof_name 
                               else ()
           in
               raise exc
           end

end)) ctxt


fun try_inst_tac ctxt insts n thm = let
    val thm' = Drule.instantiate_normalize ([], insts) thm
in
    BackendUtils.solve_by_simp_or_auto_tac ctxt n thm'
end
    
fun smt_inst_tac ctxt rules n thm = let
    val prem = Logic.nth_prem(n, Thm.prop_of thm)
    val neg = @{const Pure.imp}
                    $ prem
                    $ (@{const "Trueprop"} $ @{const "False"})
    val goal = Goal.init (Thm.cterm_of ctxt neg) 
in
    (Seq.hd (smt_ce_tac ctxt rules 1 goal); Seq.empty) 
    handle SMT_patch_Solver.SMT_Model {const_defs} 
           => try_inst_tac ctxt (mkinsts ctxt (BackendUtils.premvars n thm) ((* free_constraints @ *) const_defs) (Config.get ctxt TestEnv.smt_model)) n thm
end

fun unbounded_smt_tac ctxt rules =
    Subgoal.FOCUS_PARAMS(fn {context, ...} => 
                            (fn thm =>
                                    EVERY[smt_inst_tac context rules 1,
                                          ALLGOALS (full_simp_tac context)] thm
                                )) ctxt
  
fun testgen_smt_tac ctxt =
  let
    val thy = Proof_Context.theory_of ctxt
    val smt_facts = map (trig_thm thy) (TestEnv.get_smt_facts ctxt)
  in
    unbounded_smt_tac ctxt smt_facts
  end

end

*}


(* Choice of the interface *)

ML{*

structure SMTBackend : SMTBACKEND = struct

  fun testgen_smt_tac ctxt =
      if Config.get ctxt TestEnv.SMT then
        OldSMTBackend.testgen_smt_tac ctxt
      else if Config.get ctxt TestEnv.SMT2 then
        NewSMTBackend.testgen_smt_tac ctxt
      else
        K no_tac

end

*}



end
