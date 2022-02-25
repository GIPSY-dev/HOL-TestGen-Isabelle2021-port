(*****************************************************************************
 * HOL-TestGen --- theorem-prover based test case generation
 *                 http://www.brucker.ch/projects/hol-testgen/
 *                                                                            
 * TestGen.thy --- the core of the HOL-TestGen System.
 * This file is part of HOL-TestGen.
 *
 * Copyright (c) 2005-2010 ETH Zurich, Switzerland
 *               2008-2015 Achim D. Brucker, Germany
 *               2009-2017 Universite Paris-Sud, France
 *               2015-2017 The University of Sheffield, UK
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

chapter {* The TestGen Core*}

theory TestGen 
imports 
	Complex_Main 
	Term_Tactics (*ML*)	
  clocks  (*ML*) 	
  log (* ML *)  
  TestEnv (* ML *)
  BackendUtils
  RandomBackend
  QuickCheckBackend
  (*SMTBackend*)
  

keywords  "mk_test_suite"              :: "qed_global" 
     and  "test_spec"                  :: "thy_goal" 
     and  "gen_test_data"              :: "thy_decl_block" (*"thy_script"*) (* really ? *)
     and  "print_testenv"              :: diag
     and  "print_conc_tests"           :: diag
     and  "print_abs_tests"            :: diag
     and  "print_thyps"                :: diag
     and  "print_upos"                 :: diag
     and  "set_pre_safe_tac"           :: diag
     and  "set_pre_normalize_TNF_tac"  :: diag
     and  "set_pre_minimize_TNF_tac"   :: diag
begin 


section{*General Framework for Unit-Test*}


definition PO :: "bool \<Rightarrow> bool"
  where   "PO x = x"

lemma PO_norm1  [simp]: "PO(PO A) = PO A"      by(simp add: PO_def)
lemma PO_norm2  [simp]: "(\<not> PO A) = (PO(\<not> A))" by(simp add: PO_def)
lemma PO_norm3  [simp]: "(A \<and> PO B) = (PO(A \<and> B))" by(simp add: PO_def)
lemma PO_norm4  [simp]: "(PO A \<and>  B) = (PO(A \<and> B))" by(simp add: PO_def)
lemma PO_norm5  [simp]: "(A \<or>  PO B) = (PO(A \<or> B))" by(simp add: PO_def)
lemma PO_norm6  [simp]: "(PO A \<or>  B) = (PO(A \<or> B))" by(simp add: PO_def)
lemma PO_norm7  [simp]: "(A \<longrightarrow> (PO B)) = (PO(A \<longrightarrow> B))" by(simp add: PO_def)
lemma PO_norm8  [simp]: "((PO A) \<longrightarrow>  B) = (PO(A \<longrightarrow> B))" by(simp add: PO_def)
lemma PO_norm9  [simp]: "(A = (PO B)) = (PO(A = B))" by(simp add: PO_def)
lemma PO_norm10 [simp]: "((PO A) =  B) = (PO(A = B))" by(simp add: PO_def)
lemma PO_norm11 [simp]: "(\<forall>x. (PO (A x))) = (PO(\<forall>x. A x))" by(simp add: PO_def)
lemma PO_norm12 [simp]: "(\<exists>x. (PO (A x))) = (PO(\<exists>x. A x))" by(simp add: PO_def)

lemma PO_I : "(PO P) \<and> Q \<Longrightarrow> P \<and> Q" by(simp add: PO_def)  (* internal use only *)
lemma PO_rev[elim!]: "\<not> PO False \<Longrightarrow> PO False \<Longrightarrow>  False" by auto
lemma PO_grow : "PO(P \<and> Q) \<and> R \<Longrightarrow> (PO P) \<and> (Q \<and> R)" by(simp add: PO_def) (* internal use only *) 


definition THYP :: "bool \<Rightarrow> bool"
  where   "THYP x = x"

lemma  THYP_triv [simp]: "THYP True = True" by(simp add: THYP_def)

lemma  THYP_I    : "A \<Longrightarrow> THYP A" by(simp add: THYP_def)

lemma  THYP_D    : "THYP A \<Longrightarrow> A" by(simp add: THYP_def) 

lemma  THYP_E    : "\<lbrakk> THYP A; (A \<Longrightarrow> R) \<rbrakk> \<Longrightarrow> R" by(simp add: THYP_def)

lemma  THYP_spec : "THYP(\<forall>x. P x) \<Longrightarrow> THYP(P x)" by(simp add: THYP_def)

lemma  THYP_app1 : "\<lbrakk> THYP(A \<longrightarrow> B); A \<rbrakk> \<Longrightarrow> B" by(simp add: THYP_def) 
       (* to be used with etac in order to apply uniformity hyp *)

lemma  THYP_app1_rev : "\<lbrakk> A; THYP(A \<longrightarrow> B) \<rbrakk> \<Longrightarrow> B" by(simp add: THYP_def) 
       (* to be used with etac in order to apply uniformity hyp *)

lemma  THYP_app2 : "\<lbrakk> THYP(A); A \<Longrightarrow> B \<rbrakk> \<Longrightarrow> B" by(simp add: THYP_def) 
       (* to be used with RS in order to apply regularity hyp *)


lemma  THYP_E_reg :  "\<lbrakk> size x \<le> k \<Longrightarrow> B; THYP((k < size x) \<longrightarrow> B)\<rbrakk> \<Longrightarrow> B" 
       by(simp add: THYP_def, auto)
       (* to be used with rtac  in order to introduce regularity hyp *)


definition RSF :: "bool"
  where   "RSF = True" -- {* just to denote random solver failures *}

lemma  RSF_E : "\<lbrakk> RSF \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
       by(auto simp: RSF_def) 


section {* Tool Setup *}


ML{*
infix 1 |$>

infix 6 DOWNTO

infix 0 COLLECT_SS

signature TESTGEN =
sig
   val  mt_testenv        : TestEnv.testenv

   val get_test_thm       : theory -> Symtab.key -> thm list

   val trace              : bool Config.T
   (* switches on debug information *)

   val no_uniformity      : bool Config.T
   (* switches off uniformity generation *)

   val profiling          : bool Config.T
   (* switches on timer profiler *)

   val no_finalize        : bool Config.T
   (* don't generate constraints (POs) *)

   val is_neither_thyp_nor_PO : term -> bool

   val |$>                : thm * tactic -> thm
   val TRY'               : (int -> tactic) -> int -> tactic
   val COND'              : (int -> thm -> bool) -> (int -> tactic) -> (int -> tactic) -> int -> tactic
   val DOWNTO             : int * int -> (int -> tactic) -> tactic
   val DEPTH_SPLIT        : (int -> tactic) -> int -> tactic
   val REPEAT'            : ('a -> tactic) -> 'a -> tactic                   
   val ALLCASES           : (int -> tactic) -> tactic
   val to_TNF             : Proof.context -> string list -> int -> thm -> thm Seq.seq
   val uniformityI_tac    : Proof.context -> string list -> int -> tactic
   val CLOSURE            : (int -> tactic) -> int -> thm -> thm Seq.seq
   val case_tac_typ       : Proof.context -> string list -> int -> thm -> thm Seq.seq

   val ONLY_POS           : (int -> tactic) -> int -> tactic
                         
   val finalize_tac       : Proof.context -> string list -> tactic
                         
   val abs_data_tac       : Proof.context -> thm list -> int -> tactic
                         
   val mp_fy              : Proof.context -> int -> tactic
   val all_ify            : Proof.context -> string list -> int -> tactic
   val thyp_ify           : Proof.context -> int -> tactic
                         
   val var_hyp_subst_tac  : Proof.context -> int -> tactic

   val gen_test_case_tac  : Proof.context -> string list -> tactic
   (* "gen_test_case_tac ctxt prognames" is a
      tactic that converts all subgoals of current proof state into
      test-normal form - i.e. a conjunctive normal form
      (instead of DNF), where the conclusions have the
      form "P(progname x1 .. xn)", where progname does
      not occur in the premisses (the "constraints")
      of the test. As a prerequisite, a data-separation
      theorem of depth k is resolved for up to >steps< number
      of free variables in the current proof-state.

      NOTE: At present, the generation of data-separation
      lemmas is limited to "real" free variables and will
      not work for parameters of a test specification. Further,
      the proof-state is assumed to have only one goal.
    *)

   (* Included for complete backward compatibility *)
   val gen_test_case_old_tac : Proof.context -> string list  -> tactic

   val gen_test_data      :  string -> Context.generic -> Context.generic
   (* "gen_test_data name context" constructs ground type instances of
      test theorems associated to "name". In a further step,
      "abstract" or local test data were resolved into the resulting test
      theorems (if available in the testenv under "name"), remaining
      meta variables were instantiated by a "random_solver"
      that attempts to generate an instance and tries to solve
      the constraints of a goal up to "iterations" times.

      The resulting simplified and "solved" test data theorems
      were stored again in the test environment.
    *)

    (* TODO: remove these three functions *)
   val get_test_data      : theory -> string  -> thm list
   (* get_test_data thy name extracts the test judgements
      (i.e. the premisses of test data statement, that are not
      test hypothesis or proof obligation.). *)

   val get_test_hyps      : theory -> string -> thm list
   (* get_test_hyps thy name extracts the test hypothesis
      of a !!test data statement!!, not a test theorem. *)

   val get_pos      : theory -> string -> thm list
   (* extract remaining constraints (proof obligations) *)

   val animate            : theory -> string  -> unit
   (* ground test data statements may be animated, if "P(progname x1 .. xn)"
      is executable. "animate" presents test data statements by
      unfolding "progname x1 .. xn" and simplifying on a stepwise
      basis. (* for the moment, it's just asm_simp_tac with the
      standard evaluation trace, in the future its more or less
      the same except with slightly improved output *)
    *)
   val discharge_POs  :  string -> Proof.context -> tactic
  
   val setup: theory -> theory
end
*}                                                
           

ML{* 

structure TestGen  : TESTGEN  =
struct

open Thm;
open HOLogic;
open BNF_LFP_Compat ;
open Old_Datatype_Aux
(* open TestEnv; *)
(* open Clocks; *)
(* open BNF_LFP_Compat *) 
open Int; 
open List;
open Ctr_Sugar_Util ; (* rtac dtac etc. *)
open Rule_Insts;      (* res_inst_tac etc *)



val (trace, trace_setup) = Attrib.config_bool @{binding testgen_trace} (K false);
val (no_uniformity, no_uniformity_setup) = Attrib.config_bool @{binding no_uniformity} (K false);
val (profiling, profiling_setup) = Attrib.config_bool @{binding testgen_profiling} (K false);
val (no_finalize, no_finalize_setup) = Attrib.config_bool @{binding testgen_no_finalize} (K false);


(* ************************************************************************* *)
(* access to datatype package ...                                            *)
(* ************************************************************************* *)

fun isDataType thy (Type(tn,_)) = is_some (BNF_LFP_Compat.get_info thy [] tn)  (* CHECK ME: empty preference list ok ? *)
   |isDataType _ _ = false;


fun get_case_split_of_dt thy type_name = #exhaust (BNF_LFP_Compat.the_info thy [] type_name);

fun get_nchotomy_of thy type_name = #nchotomy (BNF_LFP_Compat.the_info thy [] type_name);


(* ************************************************************************* *)
(* access to record package ...                                              *)
(* ************************************************************************* *)

fun isRecordType thy (Type(tn,_)) = is_some (Record.get_info thy tn)
   |isRecordType _ _ = false;
   
fun get_case_split_of_record thy type_name = #cases(the (Record.get_info thy type_name));


(* ************************************************************************* *)
(* term computations ...                                                     *)
(* ************************************************************************* *)

fun max_depth (Free h) = (0,[h])
   |max_depth (Const h)= (0,[])
   |max_depth (Abs(s,tt,t)) = max_depth t
   |max_depth (s $ t) = let val (k,S) = max_depth (s)
                            val (k',S') = max_depth (t)
                        in  if k > k'+1 then (k,S)
                            else if k = k'+1 then (k, S @ S')
                                 else (k'+1, S')
                        end
   |max_depth (_) = (0,[]);

(* relies on definitions in Testing.thy ... *)
val is_thyp = exists_Const (fn (@{const_name THYP},_) => true | _ => false)

fun is_po (Const (@{const_name Trueprop},_) $ (Const (@{const_name PO},_) $ _)) = true
   |is_po _   = false;

fun is_neither_thyp_nor_PO t = (not (is_thyp t)) andalso (not (is_po t))

fun is_test_data t = (is_neither_thyp_nor_PO t) andalso not (exists_subterm is_Var t)

fun dest_TruepropAll (Const ("all", _) $ Abs(s,ty, t)) =  
                          (Const (@{const_name "HOL.All"}, (ty --> HOLogic.boolT) --> HOLogic.boolT) 
                           $ Abs(s,ty , dest_TruepropAll t))
    |dest_TruepropAll t =  HOLogic.dest_Trueprop t;


fun exists_prog prog = Term.exists_subterm
                           (fn Free (x, _) => member (op =) prog x
                             | Const (c, _) => member (op =) prog (Long_Name.base_name c) (* FIXME proper internal name!? *)
                             | _ => false);

(* complex type instantiations ... *)

fun groundT_thm context bound candTs thm =
    let val ctxt  = Context.proof_of context
        val thy   = Proof_Context.theory_of ctxt
        val thm   = Thm.varifyT_global thm
        val tvars = Term.add_tvars (list_comb(Thm.concl_of thm,Thm.prems_of thm)) []
        fun ctyp_of_sort x so t = if Sign.of_sort thy (t,so)
                                  then (SOME((x,so), Thm.ctyp_of ctxt t)
                                       handle _ => NONE)  (* FIXME avoid handle _ *)
                                  else NONE 
        fun prodS [] _ = []
           |prodS (a::R) B =  (map(fn x => a::x) B) @ (prodS R B)

        fun compute_instsT [] = [[]]
           |compute_instsT ((x,so)::R) = prodS (List.mapPartial (ctyp_of_sort x so) candTs)
                                               (compute_instsT R)
    in
        map (fn x => Drule.instantiate_normalize (x,[]) thm)
            (Library.take bound (compute_instsT tvars))
    end;

(* test

 val thm' = groundT_thm thy
                        (#type_range_bound(rep_testenv te))
                        (#type_candicates(rep_testenv te))
                        thm

 *)



(* *********************************************************************** *)
(*                                                                         *)
(* SOME more universal tacticals -> tctical.ML                             *)
(*                                                                         *)
(* *********************************************************************** *)

fun thm |$> tac =
    case Seq.pull (tac thm) of
         SOME (m,_) => m
        |_ => error"|$> : TACTIC FAILED"

fun TRY' tac n = TRY(tac n) (* standard combinator,
                               not implemented so far in Isabelle *)

fun REPEAT' tac n = REPEAT (tac n)

fun COND' testfun thenf elsef x prf =
      if testfun x prf then thenf x prf else elsef x prf;


fun (k DOWNTO (n:int)) = fn tac => (fn st =>
  let fun doall x = if x < n
                    then all_tac
                    else ((tac x) THEN doall(x-1))
      val m = Thm.nprems_of st
  in  if k <= 0 orelse k > m
      then all_tac st
      else doall k st
  end)


fun DEPTH_SPLIT tac n st =
(* PRE tac should only exhausting - i.e. increase
       the number of subgoals finitely many times
   POST if tac never fails, DEPTH_SPLIT tac will not fail.
 *)
    let val m   = Thm.nprems_of st
        val res = st |$> (tac n)
        val m'  = Thm.nprems_of res
    in  if m' > m
        then ((n + m' - m) DOWNTO n)(DEPTH_SPLIT tac) (res)
        else all_tac res
    end

fun SOLVE_ASMS ctxt tac n state =
    let val goal = Logic.get_goal (Thm.prop_of state) n
        val params = Logic.strip_params goal
        val prems =  map HOLogic.dest_Trueprop (rev(Logic.strip_imp_prems goal))
        val eqTrueI2 = @{lemma "[|P;P |] ==> True" by auto}
        fun decomp thm n = let val mm = (thm RS conjunct1)
                           in  (dtac ctxt (mm RS eqTrueI2) n) THEN
                               (etac ctxt @{thm TrueE} n) THEN
                               (decomp (thm RS conjunct2) n) end
                           handle THM _ => (dtac ctxt (thm RS eqTrueI2) n) THEN
                                           (etac ctxt @{thm TrueE} n)

    in  case prems of
        [] => all_tac state
       |a::r => let val prem = List.foldl HOLogic.mk_conj a r
                   val prem'= (Term.subst_bounds ((rev(map Free params)),prem))
                   val thm  = Goal.prove ctxt [] [] (HOLogic.mk_Trueprop prem') tac
                in (decomp thm n) state end
                handle _ => no_tac state (* could not solve asms ... *)  (* FIXME avoid handle _ *)
    end


fun auto_solver thms {prems: thm list, context: Proof.context} state =
    let val thm'  = state |$> (TRY(safe_tac (context delrules [notI])))
        val goals = Thm.nprems_of thm'
        fun solve_thm thm = FIRSTGOAL (fn n => (rtac context thm n) THEN
                                       (IF_UNSOLVED (SOLVE(auto_tac context))))
        fun solve_thms [] = no_tac
           |solve_thms (a::R) = solve_thm a ORELSE solve_thms R
    in  if goals > 0 then (solve_thms thms) thm' else all_tac thm'
    end


(* *********************************************************************** *)
(*                                                                         *)
(* SOME Testing specific tacticals                                         *)
(*                                                                         *)
(* *********************************************************************** *)

(* PRE n>0 and n <= nprems_of thm *)
fun is_THYP n thm = is_thyp(Logic.nth_prem(n, Thm.prop_of thm))

fun is_PO n thm = is_po(Logic.nth_prem(n, Thm.prop_of thm))

fun is_TEST n thm = is_neither_thyp_nor_PO(Logic.nth_prem(n, Thm.prop_of thm))

fun ONLY_CASES tac = COND' is_TEST tac (K all_tac)

fun ALLCASES_before k tac = (k DOWNTO 1) (ONLY_CASES tac)

fun ALLCASES tac thm = (ALLCASES_before (Thm.nprems_of thm) tac thm)

fun ONLY_POS tac = COND' is_PO tac (K all_tac)


fun unfold ctxt rules = asm_full_simp_tac (put_simpset HOL_basic_ss ctxt addsimps rules)

(* Optimization potential: safe_tac against something more
   specialized should do ... *)
fun if_splitter ctxt cs  = asm_full_simp_tac (fold Splitter.add_split @{thms if_splits} (put_simpset HOL_basic_ss ctxt))
                   THEN' TRY' (fn n => SELECT_GOAL (safe_tac cs) n)

(* *********************************************************************** *)
(*                                                                         *)
(* basic tactics ...                                                       *)
(*                                                                         *)
(* *********************************************************************** *)

fun strip_tac ctxt i = REPEAT (resolve_tac ctxt [impI, allI] i); (* declared Legacy in 2013-2*)

(* Pre : A1 ==> .. ==> An ==> An+1 
   Post: A1 --> .. --> An --> An+1 *) 
fun mp_fy ctxt n = (REPEAT(etac ctxt rev_mp n)); (* Version replaced by more efficient one *) 
fun mp_fy ctxt n = (REPEAT(ematch_tac ctxt [rev_mp] n));

fun all_ify ctxt excpt n state =
    let val subgoal   = Logic.nth_prem(n, Thm.prop_of state)
        val params    = Logic.strip_params subgoal
        val frees     = Term.add_frees subgoal []
        fun sbs(n,t)  = res_inst_tac ctxt [((("x",0), Position.none), n)] [] spec
        val vars      = filter_out (member (op =) excpt o fst) (params @ frees)
    in  (if null vars 
         then all_tac
         else (List.foldr(fn(x,ta) => (sbs x n) THEN ta) (prune_params_tac ctxt) vars)
               (* NEW PATCH rev 12197*)
               THEN
               all_ify ctxt excpt n  (* sbs can fail to eliminate *all* variables
                                        due to alpha-renaming of parameters in
                                        res_inst_tac. This recursive call makes
                                        all_ify exhaustive.*)
               (* END NEW PATCH rev 12197*)
              )
              (state)
    end


(*FIXME Free's are actually local consts, and cannot be closed in general
  without disrupting Isar locality*)
fun allify_frees_tac ctxt excpt = SUBGOAL (fn (subgoal, i) =>
    let val thy = Proof_Context.theory_of ctxt
        val a = (("'a", 0), @{sort type})
        fun spec_tac (x, T) =
            rtac ctxt (Thm.instantiate ([(a, Thm.ctyp_of ctxt T)], [((("x", 0), T), Thm.cterm_of ctxt (Free (x, T)))])
                    (Thm.transfer thy @{thm spec})) i
        val vars = filter_out (member (op =) excpt o fst) (Term.add_frees subgoal [])
    in
        if null vars then all_tac
        else EVERY (map spec_tac vars)
    end)

fun thyp_ify ctxt n =
    EVERY[mp_fy ctxt n, all_ify ctxt [] n, rtac ctxt (@{thm THYP_def} RS @{thm iffD1}) n]

fun vars_to_frees t = let
    val termvars = Term.add_vars t []
    val freenames = Term.add_free_names t []
    val varnames = map (fn ((s, a),_) => s^(Int.toString a)) termvars
    val newfreenames = Name.variant_list freenames varnames
    val insts = map (fn (x as (_, T), freename) => (Var x, Free (freename, T))) (termvars ~~ newfreenames)
in
    Term.subst_atomic insts t
end

fun convert_goals_to_metahyps (test:(term -> bool)) thm =
    let val thy = Thm.theory_of_thm thm
    in  map ((fn prop => Thm.forall_elim_vars 0 (Thm.assume (Thm.global_cterm_of thy prop))) o vars_to_frees)
            (filter test (Thm.prems_of thm))
    end;


fun instantiate_tac ctxt insts n thm =
    let val goal = Thm.global_cterm_of (Thm.theory_of_thm thm) (Logic.nth_prem(n, Thm.prop_of thm))
    in  (rtac ctxt (Drule.instantiate_normalize ([],insts)(Thm.trivial goal)) n
) thm end

fun var_hyp_subst_tac ctxt no state =
    let val prms = Logic.strip_imp_prems(Logic.nth_prem(no, Thm.prop_of state));
        fun is_eq (Const (@{const_name HOL.eq}, _) $ (Var _) $ _) = true
           |is_eq (Const (@{const_name HOL.eq}, _) $ _ $ (Var _)) = true
           |is_eq _ = false
        val i = Library.find_index(fn (Const(@{const_name Trueprop},_)$X) => is_eq X)
                                  (prms)
        fun mks thm = if i >= 0
                      then ((rotate_tac i no) THEN etac ctxt @{thm thin_refl} no) thm
                      else no_tac thm
    in ((REPEAT mks)
        THEN
        (full_simp_tac ctxt no)) state
    end;


(* Code seems to be superseeded by Goals.PARALLEL_GOALS in Isabelle2013-2 ...  *)
(* parallel tactic application, without any sanity checks *)

local exception FAILED of unit in

fun PARALLEL tac st =
  let
    fun try_tac g = 
      (case SINGLE tac g of
        NONE => raise FAILED ()
      | SOME g' => g');
    val goals = Drule.strip_imp_prems (Thm.cprop_of st);
    val results = Par_List.map (try_tac o Goal.init) goals;
  in all_tac st (*  ALLGOALS (fn i => retrofit i 1 (nth results (i - 1))) st *)
   end
  handle FAILED () => Seq.empty;

end;



(* A specialized map-reduce pattern for constraint-solving in TestGen. The
   PO's were extracted, attempts to their solution parallized, and the retrofit
   of the results into the test-theorem is again sequential, since it instantiates
   the meta-variables. *)
fun PARALLEL_TRYSOLVE_POs ctxt test_solve_tac st =
  let
    val pon = Config.get ctxt TestEnv.pon
    fun filter_pos filter S =
        let fun  h _ _ [] = []
               | h f n (a::S) = if f a then (n,a)::(h f (n+1) S) else (h f (n+1) S)
            fun  h_pon _ _ _ [] = []
               | h_pon f n k (a::S) = if f a then (if k = pon then (n,a):: nil 
                                                              else (h_pon f (n+1) (k+1) S)) 
                                             else (h_pon f (n+1) k S)
        in if pon = 0 then h filter 1 S else h_pon filter 1 1 S end;
    fun try_solve ct = ((Option.map (Goal.finish ctxt)) o
                         (SINGLE (test_solve_tac ctxt))) 
                        (Goal.init ct);
    val goals = Drule.strip_imp_prems (Thm.cprop_of st);
    val po_trms = (filter_pos (is_po o Thm.term_of) goals);
    val jdmts =  Par_List.map (fn(n,ct) => (n, try_solve ct)) po_trms
    
  in Seq.succeed(foldr (fn ((k, SOME a),thm) => (a RSN (k, thm))
                          |((_, NONE),thm) => thm) st jdmts)
  end

 (* val PARALLEL = PARALLEL_GOALS *) (* Experiment. See above. bu *)


(* applies exhaustively tactic tac ctxt i on subgoal i and all its descendants.
   tac can solve current goal i.
   PRE: tac must eventually terminate, also in all descendants ( otherwise CLOSURE loops).
   PRE: current goal i must be in {1 .. nprems_of st}.
   PRE: ctxt must be the ProofContext of st.
*)
fun CLOSURE tac i st = 
    let fun closure i k st = if i > k then  all_tac st
                             else let val m = Thm.nprems_of st 
                                  in  case SINGLE (tac i) st of 
                                        NONE => closure (i+1) k st
                                      | SOME st' => let val m' = Thm.nprems_of st'
                                                    in  if m' = m-1 (* tac eliminated subgoal *)
                                                        then closure i (k-1) st'
                                                        else closure i (k+(m'-m)) st' 
                                                        (* superfluous case distinct *)
                                                    end 
                                  end
    in  closure i i st end



(* *********************************************************************** *)
(*                                                                         *)
(*  special tactics for TestGen                                            *)
(*                                                                         *)
(* *********************************************************************** *)

fun cpat ctxt str = Thm.cterm_of ctxt (Proof_Context.read_term_pattern ctxt str);

(*PRE : Must not be THYP or PO *)
(* Known Bug: does not work for arbirary mixtures between HOL and Pure Quantifications *)
fun uniformityI_tac ctxt prog = 
    (if Config.get ctxt no_uniformity 
    then (fn _ => all_tac)
    else SELECT_GOAL
    let
        val cert = Thm.cterm_of ctxt;

        val core_tac =
          SUBGOAL (fn (term, i) =>
            let fun conv_All  (Const (@{const_name All}, ty) $ Abs(n, ty', tt)) =
                      (Const (@{const_name Ex}, ty) $ Abs (n, ty', conv_All tt))
                  |conv_All  (Const (@{const_name HOL.implies}, _) $ P $ Q) =
                      (Const (@{const_name HOL.conj}, [boolT,boolT]--->boolT) $ P $ conv_All Q)
                  | conv_All tt = tt;
             (*   val tt = dest_TruepropAll term; *)
                val tt = dest_Trueprop term;
                val thyp = mk_Trueprop (@{const THYP} $ (@{const HOL.implies} $ conv_All tt $ tt));
            in rtac ctxt (Thm.instantiate ([], [((("psi",0),propT), cert thyp)]) cut_rl) i end);

        val x = cpat ctxt "?x::?'a";
        val T = Thm.typ_of_cterm x;
        val count = Unsynchronized.ref 0;
        fun new_var () = cert (Var (("?X" ^ Int.toString (Unsynchronized.inc count) ^ "X", 0), T));
        fun exI_tac i st = rtac ctxt (Thm.instantiate ([], [((("x",0),T), new_var ())]) @{thm exI}) i st;
        fun check_tac' (t,i) = case t of
                                   @{term Trueprop} $ t' => check_tac' (t',i)
                                 | @{term HOL.conj} $ u $ _ => if exists_prog prog u then 
                                                                 no_tac 
                                                             else all_tac

        val check_tac = SUBGOAL check_tac'
        val intro_PO = (rtac ctxt @{thm PO_I} 1) 
                       THEN (check_tac 1) 
                       THEN REPEAT_DETERM ((rtac ctxt @{thm PO_grow} 1) 
                       THEN (check_tac 1))

        val finish_tac = (intro_PO THEN (rtac ctxt @{thm "conjI"} 1) THEN (strip_tac ctxt 2)) ORELSE (strip_tac ctxt 1)
    in
        EVERY [mp_fy ctxt 1, all_ify ctxt prog 1,
               core_tac 1, etac ctxt @{thm THYP_app1} 1,
               (REPEAT_DETERM o exI_tac) 1,
               finish_tac]
    end)


(* ************************************************************************* *)
(* data separation lemma generation ...                                      *)
(* ************************************************************************* *)


fun refine_data_separation_lemma changed ctxt bal prem_no cands thm =
(* - bal controls of the refinement is in balancing mode
     (only parameters whose occurrence in the term is
      has strictly less than maximum height)
     or not.
   - prem_no indicates the number of the premise
   - cands is the global list of candidates.
     In balancing mode, parameters in maximal depth
     position were eliminated.
   - PRE maxidx is 0 for all mvars
   - POST maxidx is 0 for all mvars

 *)
let
    val thy    = Proof_Context.theory_of ctxt
    val prem   = Logic.nth_prem(prem_no, Thm.prop_of thm)
    val params = Logic.strip_params(prem)
    val cands' = if bal then
                    let val term   = HOLogic.dest_Trueprop(hd
                                            (Logic.strip_assums_hyp prem))
                        val (k,mp) = max_depth(Term.subst_bounds
                                            ((rev(map Free params)),term))
                    in filter(fn p => forall(fn p'=> not(p=p')) (mp)) cands end
                 else cands;

    val var_no = find_index (fn(s,t)=> exists(fn (name,ty)=>
                                             s = name andalso t = ty) cands')
                             params
    val (name,ty)  = if var_no > ~1 then List.nth(params,var_no)
                     else raise (ERROR("no param found"))
    val Type(tn,_) = ty;
    val m          = get_case_split_of_dt thy tn;
    val n          = m RSN (prem_no, thm);
    (* pre: all occurrences of ?indname t1 ... tn have the same
            arguments and types  and occur in a critical pattern :
             ?indname t1 ... tn = C x1 ... xn
        ...
       The Thm.adjust_maxidx_thm reflects the fact, that only one
       MVar y should have been left - the others are erased due to
       hypsubst internally
    *)
    fun find_mvar_pat indname goal_no thm =
        let val goal = Logic.get_goal thm goal_no
            val params = Logic.strip_params goal
            fun  cc(Const(@{const_name Pure.imp}, _)
                    $ (Const(@{const_name Trueprop}, _)
                       $ (Const(@{const_name HOL.eq},t) $ A $ B))
                    $ C) = (case strip_comb(subst_bounds(
                                     rev(map Free params), A)) of
                             (Var(s,_),S) =>(if s = indname
                                             then (map dest_Free S, head_of B)
                                             else cc(C))
                            | (_, _)  => cc C)
               | cc _ = error("find_mvar_pat: No pattern found")
        in cc (strip_all_body goal) end
    fun lifter name S =
        let fun ll k [] = if 0 <=k then Bound(k)
                          else error"find_mvar:impossible lifter"
               |ll k ((s,t)::R) =
                      if s = name then Abs(s,t, ll 0 R)
                      else Abs(s,t, ll (k+1) R)
        in ll (~(length S)) S end
    fun typ_of_lifter (name:string) S =
        let fun tll S [] = error"find_mvar:impossible type for lifter"
               |tll S ((s,t)::R) =
                       if name = s
                       then ((rev S)@(t::(map snd R)), t)
                       else tll (t::S) R
        in  (op --->)(tll [] S) end
    val (lifter_params, constr) = find_mvar_pat ("y",1) prem_no (Thm.prop_of n)
    (* ("y",1) is a fact from the invariant maxidx=0 (see below) *)
    val subst0 = lifter name lifter_params
    val ty_lift = fastype_of subst0
    val ty_constr = fastype_of constr
    val subst = Thm.cterm_of ctxt subst0
    val ty_lift_body = body_type ty_lift
    val ty_lift_constr = body_type ty_constr
    val tyenv = Sign.typ_match thy (ty_lift_constr,ty_lift_body) Vartab.empty
                handle Type.TYPE_MATCH => Vartab.empty
    (* Hack that works for cases, where non-recursive positions in a type
       were GROUND types (like color in RBT_tree). *)
    fun tysubs2ctyps(x,(s,t)) = ((x,s),Thm.ctyp_of ctxt t) (*(Thm.ctyp_of ctxt (TVar(x,s)),Thm.ctyp_of ctxt t) *)
    val tsubst = map tysubs2ctyps (Vartab.dest tyenv)
    val ()    = (changed:=true)
    val var = (("y",1),ty_lift)
    val result = (Drule.instantiate_normalize (tsubst, [(var,subst)]) n)
                 |$> (ALLGOALS(fn n => TRY(hyp_subst_tac_thin true ctxt n)))
                 |$> prune_params_tac ctxt
in  Thm.adjust_maxidx_thm 0 result
    (* establishes POST and makes this fact therefore invariant. *)
    (* More safe, but also more expensive variant: standard result. *)
end

(* This is the core procedure of the data_separation_lemma generation, and,
   in a way, the core of the test case generator itself.

   It proceeds as follows: in a given theorem thm (usually an exhaustion lemma
   itself), the premisses (having the form !!x1..xn. A x1 .. xn ==> B in
   general) were selected and "refined" in a "sweep". This means that in a
   sweep, for each premisse an xi is selected (which must have a data-type,
   say ti) and the exhaustion theorem of ti is forward resolved into this
   premisse; cleaning it up (by prems_hyp_subst_tac) also erases xi as
   parameter of this premisse.
   In a next sweep, another xj may be selected and so forth, up to the moment
   were no parameters remained in the premisse that existed before the initial
   sweep (this the list parameters is the "cand" (candidates) x1 .. xj for
   all premisses which precomputed.)

   Then, the candidate list may be recomputed and the process repeated up to
   n times. Since any group of sweeps erases one generation of parameters,
   the parameter n corresponds to "depth+1" of the data term occuring in the
   premisse increases, i.e. from:

   [| ?y = Leaf ==> ?P;
      !!a tree1 tree2. ?y = Node a tree1 tree2 ==> ?P |]
   ==> ?P

   we get:

   [| ?y = Leaf ==> ?P; !!a. ?y = Node a Leaf Leaf ==> ?P;
      !!a aa tree1 tree2a. ?y = Node a Leaf (Node aa tree1 tree2a) ==> ?P;
      !!a aa tree1a tree2a. ?y = Node a (Node aa tree1a tree2a) Leaf ==> ?P;
      !!a aa tree1a tree2a ab tree1 tree2b.
            ?y = Node a (Node aa tree1a tree2a) (Node ab tree1 tree2b) ==> ?P
   |] ==> ?P

   This picture is slightly complicated by the fact that Isabelle does not
   change the parameters, but may reintroduce parameter erased by a previous
   sweep during the forward resolution step. Thus, the procedure may loop.

   Instead of not erasing the parameters during lemma-refinement (this
   leads to very large liftings of the meta-variables over these
   parameter lists and is thus expensive), we chose to use
   a particular test for "maximal" parameters in order to avoid this problem.

 *)
fun nrefine_data_separation_lemma changed ctxt 0 thm = thm
  | nrefine_data_separation_lemma changed ctxt n thm =
    let
      val thy = Proof_Context.theory_of ctxt
      val isaDataType   = fn(_,ty)=> isDataType thy ty
      val thm_params    = maps Logic.strip_params (Thm.prems_of thm)
      val cands         = distinct (op=) (filter isaDataType thm_params)
      fun rds b(prno,t) = refine_data_separation_lemma changed ctxt b prno cands t
                          handle _ => t  (* FIXME avoid handle _ *)
      val ()            = (changed:=false)
      fun sweep b th    = List.foldr (rds b) th (1 upto (length(Thm.prems_of th)))
      val thm1          = sweep false thm       (* debalancing phase *)
      fun repeat_till_stable thm = let val ()   = (changed:=false)
                                     val thm' = sweep true thm
                                   in  if !changed
                                       then repeat_till_stable thm'
                                       else thm'
                                   end
    in  nrefine_data_separation_lemma changed ctxt
          (n-1)
           (if  !changed
            then thm1                     (* debalancing phase had no effect *)
            else repeat_till_stable thm1) (* balancing phase *)
    end;

(* NOTE: Currently, this core routine is restricted to
   "real free" variables; parameters will not be
   considered as a simple means to avoid looping ... *)
fun data_separation_tac ctxt var no state =
    let
        val thy    = Proof_Context.theory_of ctxt
        val depth  = Config.get ctxt TestEnv.depth
      	val (na,Type(tn,_)) = var
        fun ds_thm tn = nrefine_data_separation_lemma (Unsynchronized.ref false) 
						                                          ctxt  depth 
						                                          (get_case_split_of_dt thy tn)
 
       	val data_sep_thm = Drule.export_without_context (ds_thm tn)
        val brchs = length(Thm.prems_of data_sep_thm)
    in  ((res_inst_tac ctxt [((("y",0),Position.none),na)] [] data_sep_thm no)
         THEN 
         (res_inst_tac ctxt [((("x",0),Position.none),na), 
                                        ((("k",0),Position.none),Int.toString depth)] 
                                       []
                                       @{thm THYP_E_reg} 
										                   (no + brchs - 1))
         THEN (thin_tac ctxt (na^"= _") [] (no+brchs))) state
    end;

(* Copied from Isabelle2011 old_term.ML sources, for providing old variable order *)
(*Accumulates the Frees in the term, suppressing duplicates.*)
fun add_term_frees (t, frees: term list) = case t of
    Free   _ => Ord_List.insert Term_Ord.term_ord t frees
  | Abs (_,_,body) => add_term_frees(body,frees)
  | f$t =>  add_term_frees (f, add_term_frees(t, frees))
  | _ => frees;

fun term_frees t = add_term_frees(t,[]);

(* Included for complete backward compatibility *)
fun data_separation_old_tac ctxt depth no state =
     let
        val thy    = Proof_Context.theory_of ctxt
        val prem   = Logic.nth_prem(no, Thm.prop_of state)
        val params = Logic.strip_params(prem)
        val term   = HOLogic.dest_Trueprop(Logic.strip_assums_concl prem)
        val frees  = map dest_Free (term_frees term)
(*      val cands  = filter (fn (_,ty) => isDataType thy ty) (params@frees) *)
        val cands  = filter (fn (_,ty) => isDataType thy ty) (frees)
        fun ds_thm tn =
          nrefine_data_separation_lemma (Unsynchronized.ref false) ctxt depth (get_case_split_of_dt thy tn)
    in (case cands of
          [] => no_tac
        | (na,Type(tn,_))::_ =>
                    let val data_sep_thm = Drule.export_without_context (ds_thm tn)
                        val brchs = length(Thm.prems_of data_sep_thm)
                    in       (res_inst_tac ctxt [((("y",0),Position.none),na)] [] data_sep_thm no)
                        THEN (res_inst_tac ctxt [((("x",0),Position.none),na),
                                                   ((("k",0),Position.none),Int.toString depth)] []
                                                  @{thm THYP_E_reg}
                                                  (no + brchs - 1))
                        THEN (thin_tac ctxt (na^"= _") [] (no+brchs))
                    end)
       (state)
end


(* "Small", non-recursive Version of gen_test_cases:
   (TODO for future releases: Integration into the testgen-Kernel).
   searches parameter in goal no with typename tname and performs case-split on this
        parameter. Note that the type-name must be the full name. 
        PRE: current goal i must be in {1 .. nprems_of st}.
        PRE: ctxt must be the ProofContext of st. *)
 (* op member : ('a * 'b -> bool) -> 'b list -> 'a -> bool *)

   fun case_tac_typ ctxt tnames no thm =
     let  
          val prem   = Logic.nth_prem(no, Thm.prop_of thm)
          val params = Logic.strip_params(prem)
          val max    = Thm.nprems_of thm 
          val params = params (* @ free variables TODO !!! *) 
          fun ty_search (_,Type(s,_)) = member (op =) (tnames) (s) 
             |ty_search (_,_) = false
          fun REP tac st = let val max' =  Thm.nprems_of st 
                           in  (max'-max+no DOWNTO no) tac st end
     in case List.find ty_search params of
               SOME (X,_) => EVERY[Induct_Tacs.case_tac ctxt X [] NONE no ,
                                   REP (hyp_subst_tac_thin true ctxt), 
                                   unfold_tac ctxt [@{thm triv_forall_equality}] ] thm
                                   (* probably not the most efficient - try simp only *)
             | NONE       => no_tac thm
   end;



(* ************************************************************************* *)
(* normal form computation ...                                               *)
(* *************************** ********************************************** *)

fun to_TNF ctxt prog no state =
    let
        val thy     = Proof_Context.theory_of ctxt;
        val term    = Thm.prop_of state
        val prems   = Logic.prems_of_goal term no
        val concl   = Logic.concl_of_goal term no
        fun term_string_of_goal_no () = (Pretty.unformatted_string_of o (Syntax.pretty_term ctxt)) 
                                            (Logic.list_implies(prems,concl))
        val prems'  = filter (exists_prog prog) prems;
        val concl'  = filter (exists_prog prog) [concl];
        fun subst t = (Thm.cterm_of ctxt (Var(("P",0),HOLogic.boolT)),
                       Thm.cterm_of ctxt t);
        (*  swap_tac : tactic * term -> tactic; takes one term containing
            "prog" and swap it into the conclusion as disjoint *)
        val swap_accumulate =  @{lemma "[| P ; ~P | Q |] ==> Q" by auto}
        fun swap_tac (tm,tc) = tc THEN
                               (Term_Tactics.eres_terminst_tac 
                                  ctxt
                                  []
                                  [subst (HOLogic.dest_Trueprop tm)]
                                   swap_accumulate
                                  no)
        (* rev_tac swaps term "a" into conclusion *)
        fun rev_tac thy a = Term_Tactics.eres_terminst_tac
                                  ctxt
                                  []
                                  [subst (HOLogic.dest_Trueprop a)]
                                  @{thm rev_notE}
                                  no
    in ((case (prems',concl') of
          ([],[])   => error ("Subgoal " ^Int.toString(no)
                             ^" can not be converted into TNF: \n \n" ^ 
                              term_string_of_goal_no())
          (* case that conclusion does not contain "prog", but several
             assumptions do: pick one of them, revert first *)
         |(a::R,[]) =>(rev_tac thy a
                       THEN
                       (List.foldl swap_tac all_tac R))
         |(R,_)     => (List.foldl swap_tac all_tac R)
        )
        THEN
         (simp_tac (put_simpset HOL_ss ctxt) no)) state 
    end;



fun normalize_TNF ctxt prog top =
      List.foldl (fn (arg,t) => t THEN to_TNF ctxt prog arg)
                 all_tac
                 ((length (prems_of top)) downto 1)
                 top
    


(* TODO: adb *)
fun minimize_TNF ctxt = distinct_subgoals_tac
(* This should do:
   - sorting assumptions in all subgoals
   - sorting parameters of subgoals
   - sortieren der clauses -
     weniger asms zuerst (defer_tac)
   - eliminieren von assumptions subsumed in other clauses
     [| P;R |] ==> A;
     [| P;Q;R  |] ==> A
     ------------------
     [| P;R |] ==> A;
     [| P;R  |] ==> A
     durch thin_tac
   - eliminieren von subsumed or's,
     a particular weakness of our procedure so far.
     [| P;R |] ==> A;
     [| ~P;Q |] ==> B
     [| R; Q|] ==> A|B;
     ------------------
     [| P;R |] ==> A;
     [| ~P;Q |] ==> B
    - finally distinct_subgoals_tac
*)


(* orig version *)
(*
fun gen_test_case_tac thy clasimp depth steps prog  =
    EVERY[ALLGOALS (asm_full_simp_tac (snd clasimp)),
          safe_tac ((global_claset_of thy) addss (global_simpset_of thy)),
          normalize_TNF thy prog,
          minimize_TNF,
          ALLGOALS (fn n => TRY(uniformityI_tac prog n))];
*)



(* ************************************************************************* *)
(* test case generation ...                                                  *)
(* ************************************************************************* *)

fun SORT ctxt rules n thm = let
    val matches = maps (fn rule => rule ctxt n thm) rules
    val sorted = map (fn (i,tac) => tac) 
                     (sort (fn (x,y) => rev_order (int_ord (fst x, fst y))) matches) 
in
    (EVERY sorted) thm
end



fun EXEC ctxt tac str = EVERY[if Config.get ctxt profiling 
                                 then Clocks.start_clock_tac str 
                                 else all_tac,
                              if Config.get ctxt trace 
                                 then print_tac ctxt ("\n:"^str^"\n") 
                                 else all_tac,
                              tac,
	                            if Config.get ctxt profiling 
                                 then Clocks.stop_clock_tac str 
                                 else all_tac]

fun EXEC' ctxt tac str n = EXEC ctxt (tac n) str

fun PRINT_THM ctxt no = 
               (fn state => (if Config.get ctxt trace 
                             then let val prem = Logic.nth_prem(no, prop_of state)
                                      val str  = (Pretty.string_of o (Syntax.pretty_term ctxt)) prem
                                  in  print_tac ctxt ("\n goal "^Int.toString(no)^"::"^str^"\n") end
                             else all_tac) state)

fun finalize_tac ctxt prog = 
    EXEC ctxt (ALLCASES(TRY'(uniformityI_tac ctxt prog))) "main uniformity NF"
			 
fun gen_test_case_tac ctxt prog = let
    val steps = Config.get ctxt TestEnv.steps
    val testenv = TestEnv.get_testenv ctxt
    val rules   = TestEnv.get_test_derivation_rules testenv

    val begin_profiling_tac = if Config.get ctxt profiling 
                              then Clocks.start_clock_tac "unnamed_test_thm" THEN Clocks.start_clock_tac "gen_test_cases"
                              else all_tac
				  
    val end_profiling_tac = if Config.get ctxt profiling 
                            then Clocks.stop_clock_tac "gen_test_cases" THEN Clocks.stop_clock_tac "unnamed_test_thm"
                            else all_tac

    fun pre_normalize_TNF_tac ctxt = TestEnv.get_pre_normalize_TNF_tac (TestEnv.get_testenv ctxt) ctxt

    val sort_tac = SELECT_GOAL (SORT ctxt rules 1)
in  
    EVERY[begin_profiling_tac,
	        EXEC ctxt (ALLCASES((asm_full_simp_tac ctxt)))          "pre-simplification",
	        EXEC ctxt (REPEAT_DETERM_N steps (ALLCASES sort_tac)) "main completed",
          EXEC ctxt (pre_normalize_TNF_tac ctxt)                  "pre_norm",
          EXEC ctxt (normalize_TNF ctxt prog)                     "TNF",
	        if Config.get ctxt no_finalize 
             then all_tac 
             else finalize_tac ctxt prog,
	        end_profiling_tac]
end 

fun data_separation_rule ctxt no state =
let
    val thy    = Proof_Context.theory_of ctxt
    val prem   = Logic.nth_prem(no, prop_of state)
  (*val params = Logic.strip_params(prem) *)
    val term   = HOLogic.dest_Trueprop(Logic.strip_assums_concl prem)
    val frees  = Term.add_frees term []
  (*val cands  = filter (fn (_,ty) => isDataType thy ty) (params@frees) 
        : LOOPS AT PRESENT SINCE gen_test_cases active on frees *)
    val cands  = filter (fn (_,ty) => isDataType thy ty) (frees)
    fun tac cand = TRY (CHANGED_PROP      (ALLCASES (data_separation_tac ctxt cand)) 
                                     THEN (ALLCASES (TRY' (hyp_subst_tac_thin true ctxt))))
                                     THEN (if Config.get ctxt trace 
                                           then print_tac ctxt "After data separation" 
                                           else all_tac)
in
    map (fn cand => (100, tac cand)) cands
end

fun to_HCNF_rule ctxt no state = 
    [(50,      EXEC ctxt (TestEnv.get_pre_safe_tac (TestEnv.get_testenv ctxt) ctxt) "Simp"
	        THEN EXEC ctxt (TRY (safe_tac ctxt)) "HCN")]

fun minimize_rule ctxt no state =      
    [(10,      EXEC ctxt (TestEnv.get_pre_minimize_TNF_tac (TestEnv.get_testenv ctxt) ctxt) "pre_minimize"
	        THEN EXEC ctxt (minimize_TNF ctxt) "MinimTNF"
          THEN (ALLCASES(asm_full_simp_tac ctxt))
          THEN (TRY (safe_tac ctxt)))] 

(* Included for complete backward compatibility *)
fun gen_test_case_old_tac ctxt prog  =
    let val testenv = TestEnv.get_testenv ctxt
        val depth = Config.get ctxt TestEnv.depth
        val steps = Config.get ctxt TestEnv.steps

        val prep_HCNF = TestEnv.get_pre_safe_tac testenv
        val to_HCNF = TRY (safe_tac ctxt)
        val pre_normalize_TNF_tac = TestEnv.get_pre_normalize_TNF_tac testenv
        val pre_minimize_TNF_tac = TestEnv.get_pre_minimize_TNF_tac testenv
        fun trace_tac b str = (if Config.get ctxt trace 
                               then print_tac ctxt ( "\n"^b^":"^str^"\n")
                               else all_tac)
        fun exec phase b str = EVERY[if Config.get ctxt profiling 
                                     then Clocks.start_clock_tac str 
                                     else all_tac,
                                     phase, trace_tac b str,
                                     if Config.get ctxt profiling 
                                     then Clocks.stop_clock_tac str 
                                     else all_tac]

        fun standard k b =
            EVERY[if Config.get ctxt trace then print_tac ctxt "Enter" else all_tac,
                  exec (prep_HCNF ctxt) b "Simp",
                  exec (to_HCNF) b "HCN",
                  exec (pre_normalize_TNF_tac ctxt) b "pre_norm",
                  exec (normalize_TNF ctxt prog) b "TNF",
                  exec (pre_minimize_TNF_tac ctxt) b "pre_minimize",
                  exec (minimize_TNF ctxt) b "MinimTNF"]
        val dst = data_separation_old_tac ctxt depth

        fun pairself f (x, y) = (f x, f y);

        (*True if the two theorems have the same prop field, ignoring hyps, der, etc.*)
        val eq_thm_prop = op aconv o pairself Thm.full_prop_of;

        fun main k st =(if k < steps (* not yet all frees per goal
                                          less steps exhausted*)
                        then   (ALLCASES(fn n => TRY(dst n) )) THEN
                               (* try exhaustion per goal *)
                               (COND(fn st' => not (eq_thm_prop(st, st')))
                                        (* something 's changed *)
                                        (     (ALLCASES (fn n => TRY((hyp_subst_tac_thin true ctxt) n) ) ) (* REALLY ? *)
                                         THEN (standard k "1")
                                         THEN (main (k+1))
                                        )
                                        (standard k "2"))
                        else standard  k "0" (* run out of steps *)) (st)
        val begin_profiling_tac = if Config.get ctxt profiling then
                                      Clocks.start_clock_tac "unnamed_test_thm" THEN Clocks.start_clock_tac "gen_test_cases"
                                  else
                                      all_tac

        val end_profiling_tac = if Config.get ctxt profiling then
                                      Clocks.stop_clock_tac "gen_test_cases" THEN Clocks.stop_clock_tac "unnamed_test_thm"
                                  else
                                      all_tac
    in  EVERY[begin_profiling_tac,
              exec (ALLCASES((asm_full_simp_tac ctxt))) "" "pre-simplification",
              exec (main 0) "" "main completed",
              exec (ALLCASES(TRY'(uniformityI_tac ctxt prog))) "" "main uniformity NF",
              end_profiling_tac]
    end;


(* ************************************************************************* *)
(*                                                                           *)
(* testdata generation        ...                                            *)
(*                                                                           *)
(* ************************************************************************* *)


fun abs_data_tac ctxt atdata = 
    let fun single_abs_data_tac thm = 
            Subgoal.FOCUS_PARAMS(fn {context, ...} => 
            SOLVE (Method.insert_tac context [thm] 1 THEN auto_tac context)) ctxt
    in
       FIRST' (map single_abs_data_tac atdata)
    end


fun test_solve_tac ctxt atdata = 
    let val thy = Proof_Context.theory_of ctxt
        val remove_po = EqSubst.eqsubst_tac ctxt [0] [@{thm PO_def}]
        val total_iterations = Config.get ctxt TestEnv.iterations
        val max_simple_iterations = 50
        val simple_iterations  = Int.min(total_iterations, max_simple_iterations)
        val further_iterations = Int.max(total_iterations - max_simple_iterations,0)
    in
              remove_po 
        THEN' PRINT_THM ctxt 
        THEN' (FIRST'[EXEC' ctxt (abs_data_tac ctxt atdata) "abs_data",
                      EXEC' ctxt (RandomBackend.random_inst_tac ctxt simple_iterations) "random_inst",
                      EXEC' ctxt (QuickCheckBackend.quickcheck_tac ctxt further_iterations) "quickcheck",
                      EXEC' ctxt (SMTBackend.testgen_smt_tac ctxt) "smt"])
    end



fun is_solved n thm = 
    let  fun is_unsolved_po i =  not (null (inter (op =) (BackendUtils.premvars n thm) (BackendUtils.premvars i thm))) 
                                 andalso i <> n
    in    not (exists is_unsolved_po (1 upto (nprems_of thm)))
    end

(* Instantiate the remaining variables in test cases
with random terms *)

fun finalize_test_tac ctxt n thm = let
in
    (COND (is_solved n) (RandomBackend.single_rand_inst_tac ctxt (BackendUtils.premvars n thm)) all_tac) thm
end



fun solve_all ctxt atdata state =
   let (* adding a let expression.. in order to check if all free vars were instatiated by smt.. 
          if true then error code else solve_all*)
    val PARALLEL_TRYSOLVE = PARALLEL_TRYSOLVE_POs ctxt (fn ctxt => test_solve_tac ctxt atdata 1) state
                             
    val term =  PARALLEL_TRYSOLVE |>  Seq.list_of |> 
               (List.map prop_of) |> HOLogic.mk_list @{typ "term"}
    val use_smt = Config.get ctxt TestEnv.use_smt;
in
   if (use_smt andalso (Term.exists_subterm (Term.is_Var) term))
   then  error("One or more free variables were not instantiated by the solver!")
          
   else  state |$> PARALLEL_TRYSOLVE_POs ctxt (fn ctxt => test_solve_tac ctxt atdata 1)
          |$> ALLCASES (finalize_test_tac ctxt) (* cannot parallelize here *)

end


  (* *********************************************************************** *)
  (* Normalizer                                                              *)
  (* *********************************************************************** *)
  (* motivation: type instantiation may make
     constraints of test-cases unsolvable.
     Unsolvable cases should be removed before random-solving.
     Since constraints with Mvars were not considered
     by simptac and arith_tac, they were substituted
     against arbitrary free vars aforehand.

fun norm_tac ctxt n thm =
   let  val thy   = Proof_Context.theory_of ctxt
        val m     = Thm.nprems_of thm
        val prem  = Logic.nth_prem(n, prop_of thm)
        val k     = length (Logic.strip_imp_prems(prem))
        val goal  = Thm.trivial(cterm_of thy prem)
        val tvars = OldTerm.term_vars prem
        val insts = map(fn(x as Var((s,a),t))=>
                            (cterm_of thy x,
                             cterm_of thy (Free("XXX"^s^(Int.toString a),t))))
                       (tvars)
        val cleanup    = List.foldr (fn (_,tac) => (atac (n)) THEN tac)
                               all_tac (1 upto k)
   in  (
        (rtac (instantiate ([],insts) goal) n)
        THEN
        (full_simp_tac (simpset_of ctxt) n)  (* may erase goal n.
                                 --> test case unsolvable. *)
        THEN
        (fn thm' => if (nprems_of thm' < m+k) (* goal erased *)
                    then cleanup thm'
                    else no_tac thm )(* report failure *)
       )(thm)
   end *)

fun gen_test_data name context =
    let val ctxt = Context.proof_of context
        val te = TestEnv.get_testenv ctxt
        val bound = Config.get ctxt TestEnv.type_range_bound
        val candTs= #type_candicates(TestEnv.rep_testenv te)
        val type_grounds = groundT_thm context bound candTs
        val testthm  = (the(Symtab.lookup(TestEnv.get_test_thm_tab te)name)
                            handle Option.Option => error("No test theorem: "^name^" available!"))
        val atdata = (the(Symtab.lookup(TestEnv.get_absdata_tab te)name)
                      handle Option.Option => [])
        val jdmts = map (solve_all ctxt atdata) (type_grounds testthm)
        val te1 = TestEnv.test_thm_inst_tab_update  (Symtab.update(name,jdmts)(TestEnv.get_test_thm_inst_tab te)) te
        val prems = List.concat (map Thm.prems_of jdmts)
        val data = map (Thm.cterm_of ctxt) (filter is_test_data prems)
        val te2 = TestEnv.set_test_data_tab (name,data) te1
        val hyps = map (Thm.cterm_of ctxt) (filter is_thyp prems)
        val te3 = TestEnv.set_test_thyps_tab (name,hyps) te2
        val pos = map (Thm.cterm_of ctxt) (filter is_po prems)
        val te4 = TestEnv.set_unsolved_PO_tab (name,pos) te3

        val t = LogThy.get_td_delta ()
        val _ = writeln (String.concat ["Test theorem (gen_test_data) '",name,"': ",
					                               Int.toString (List.length data)," test cases in ",
                                         Time.toString t, " seconds"])
         val _ = if not (null pos) 
                 then  writeln (String.concat ["Warning: There were ", Int.toString (List.length pos) , " unsolved POs."])
                 else  ()
         val _ = LogThy.append (String.concat [
                              Context.theory_name (Proof_Context.theory_of ctxt), ", " ,name, ", ",
					                     "test data, " ,Int.toString (List.length data),
                              ", " ,Time.toString t,"\n"])
			   
    in TestEnv.map_data (K te4) context end;

fun select_goals pred thy name = let
    val te = TestEnv.get_testenv_global thy
in
    maps (convert_goals_to_metahyps pred) 
             (the(Symtab.lookup(TestEnv.get_test_thm_inst_tab te)name)
              handle Option.Option => error("No data statement: "^name^" available!"))
end

val get_test_data = select_goals is_test_data

val get_test_hyps = select_goals is_thyp

val get_pos = select_goals is_po

fun get_test_thm thy name = let
    val te = TestEnv.get_testenv_global thy
in
             (the(Symtab.lookup(TestEnv.get_test_thm_inst_tab te)name)
              handle Option.Option => error("No data statement: "^name^" available!"))
end

fun discharge_POs name context =
    let fun use_test_instances_tac name ctxt  =
              let val te = TestEnv.get_testenv ctxt
                  val atdata = (the(Symtab.lookup(TestEnv.get_absdata_tab te)name)
                                handle Option.Option => [])
              in (TRY' (      EqSubst.eqsubst_tac ctxt [0] [@{thm PO_def}] 
                        THEN' abs_data_tac ctxt atdata))
              end
    in ALLGOALS(ONLY_POS (use_test_instances_tac name context)) end

(* *********************************************************************** *)
(*                                                                         *)
(* Initial test environment                                                *)
(*                                                                         *)
(* *********************************************************************** *)

val _ = Context.>> (TestEnv.map_data
  ((TestEnv.pre_safe_tac_update (fn ctxt => ALLCASES (asm_full_simp_tac ctxt)))
   #> (TestEnv.add_test_derivation_rule data_separation_rule)
	 #> (TestEnv.add_test_derivation_rule to_HCNF_rule)
	 #> (TestEnv.add_test_derivation_rule minimize_rule)));

val mt_testenv = TestEnv.get_testenv (Context.the_local_context ());

val _ =
  Outer_Syntax.command @{command_keyword "print_testenv"} "print test environment"
    (Parse.name  >> (fn name => Toplevel.keep ((TestEnv.print_testenv name) o Toplevel.context_of)));

val options =  Scan.optional (Parse.$$$ "(" |-- Parse.!!! (Scan.option Parse.nat--| Parse.$$$ ")")) (NONE);

val _ = let fun print name opts ctxt = writeln (TestEnv.print_test_data ctxt name opts) in
            Outer_Syntax.command @{command_keyword "print_conc_tests"} "print concrete tests"
            (options -- Parse.name  >> (fn (opts, name) => 
                                          Toplevel.keep ((print name opts) o Toplevel.context_of)))
        end;

val _ = let fun print name opts ctxt = writeln (TestEnv.print_test_case ctxt name opts) in
            Outer_Syntax.command @{command_keyword "print_abs_tests"} "print abstract tests"
            (options -- Parse.name  >> (fn (opts, name) => 
                                          Toplevel.keep ((print name opts) o Toplevel.context_of)))
        end;

val _ = let fun print name opts ctxt = writeln (TestEnv.print_test_hyps ctxt name opts) in
            Outer_Syntax.command @{command_keyword "print_thyps"} "print test hypothesis"
            (options -- Parse.name  >> (fn (opts, name) => 
                                          Toplevel.keep ((print name opts) o Toplevel.context_of)))
        end;

val _ = let fun print name opts ctxt = writeln (TestEnv.print_unsolved_pos ctxt name opts) in
            Outer_Syntax.command @{command_keyword "print_upos"} "print unsolved proof obligations"
            (options -- Parse.name  >> (fn (opts, name) => 
                                          Toplevel.keep ((print name opts) o Toplevel.context_of)))
        end;


(* ************************************************************************* *)
(* micellaneous functions ...                                                *)
(* ************************************************************************* *)


fun animate thy name =  (* HACK - very simplistic implementation *)
    let val ctxt = Proof_Context.init_global thy |> Config.put simp_trace true
        fun animate_data_statement thm =
                (Output.writeln ">>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>";
                 Pretty.writeln (Thm.pretty_thm ctxt thm);
                 Output.writeln "============================================";
   (*              asm_full_simplify (global_simpset_of(theory_of_thm(thm))) thm; *)
                 asm_full_simplify ctxt thm;
                 Output.writeln "<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<");
    in
        List.app animate_data_statement (get_test_data thy name)
    end;

(* module setup *)

val setup =
  trace_setup #>
  no_uniformity_setup #>
  profiling_setup #>
  no_finalize_setup;

end (*struct *);

*}

setup {* TestEnv.setup #> TestGen.setup *}
text{* A key concept of HOL/TestGen are \emph{test suites}. These can be seen as a kind of 
container data-structure that relate to a test-specification a number of data, namely the
test theorem (the TNF), abstract and concrete test data, and specific configuration data. 
Test-suites were created at the end of a test-specification statement and initial test-refinement.
Later on they were enriched and finally used to generate test drivers and test executions.

So, a test suite with name "X" will be finally run at a test-execution executed outside HOL/TestGen
started by the shell-command "run_X".
*}

ML{*

fun mk_test_suite name = Toplevel.end_proof (fn _ => fn state =>
  let
    val ctxt = Proof.context_of state;
    val _ = if Config.get ctxt TestGen.profiling 
            then (Clocks.start_clock  "unnamed_test_thm";
                  Clocks.rename_clock "unnamed_test_thm" name;
                  Clocks.stop_clock name)
            else ()

    val _ = Proof.assert_backward state;
    val {context = goal_ctxt, goal, ...} = Proof.goal state
    fun up_thy thy =
        let
          fun add_to_dm name thm thy =
              let
                val thy = TestEnv.map_data_global (TestEnv.add_test_case (name,thm)) thy
                val t = LogThy.get_tc_delta ()
                val num_of_tc = List.length
                                (List.filter (fn tc => TestGen.is_neither_thyp_nor_PO tc) (Thm.prems_of thm))
                val _ = writeln (String.concat ["Test theorem (gen_test_cases) '",
                                                name,"': ", Int.toString num_of_tc,
						                                    " test cases in ",Time.toString t, 
                                                " seconds"])

                val _ = LogThy.append (String.concat 
                                       [Context.theory_name thy, ", ",
						                            name, ", " ,"test case, " ,Int.toString num_of_tc,
                                        ", ", Time.toString t,"\n"])
              in
                thy
              end
        in
          thy |> Sign.add_path (space_implode "_" [name])
              |> (Global_Theory.add_thms [((@{binding test_thm}, goal), [])])
              |> snd 
              |> Sign.parent_path
              |> add_to_dm (space_implode "_" [name]) goal
              |> Clocks.flush_clocks
        end

  in goal_ctxt |> Local_Theory.background_theory up_thy  end);


val _ = Outer_Syntax.command  
              @{command_keyword mk_test_suite}
              "store test state (theorem)"
              (Parse.name >> mk_test_suite);



(**********************)
fun gen_test_dataT name thy =
    let  val _  = LogThy.start_td_timer ()
         val _ = if Config.get_global thy TestGen.profiling 
                 then (Clocks.init_clocks thy;Clocks.start_clock name;Clocks.start_clock "gen_test_data")
                 else ()

         val thy = Context.theory_map (TestGen.gen_test_data name) thy (* call of the core-routine*)

	       val t = LogThy.get_td_delta ()
         val thy = if Config.get_global thy TestGen.profiling 
                   then (Clocks.stop_clock "gen_test_data"; Clocks.stop_clock name; Clocks.flush_clocks thy)
                   else thy                                 
         
         val thy  = Sign.add_path (space_implode "_" [name]) thy;
         val thm  = TestGen.get_test_thm thy name
         val thy  = snd(Global_Theory.add_thmss [((@{binding test_thm_inst},thm),[])] (thy))

         val thy = Sign.parent_path thy;
     in
         thy
     end
   
val _ =  Outer_Syntax.command 
              (*@{command_spec "gen_test_data"}*)
              @{command_keyword gen_test_data} 
              "generate test data"
              (Parse.name  >> (Toplevel.theory o gen_test_dataT));

(**********************)

val general_statement =
  Parse_Spec.statement >> (fn x => ([], Element.Shows x)) ||
  Parse_Spec.long_statement;

val _ = Outer_Syntax.local_theory_to_proof
            @{command_keyword test_spec} 
            "define test specification"   
            (Scan.optional (Parse_Spec.opt_thm_name ":" --|
               Scan.ahead (Parse_Spec.includes >> K "" || Parse_Spec.long_statement_keyword)) 
               Binding.empty_atts --
               Scan.optional Parse_Spec.includes [] --
               general_statement >> 
                  (fn ((a, includes), (elems, concl)) => fn lthy =>
                     let val _ = if Config.get lthy TestGen.profiling 
                                 then Clocks.init_clocks (Proof_Context.theory_of lthy) 
                                 else ()
                     in
                        Specification.schematic_theorem_cmd true
                        "test_spec" NONE (K I) a includes elems concl false lthy
                     end));

*}
ML{* 
fun set_wrapper str H src = 
         let val txt = Input.text_of src
             val range = Input.range_of src
             val txt' = str ^ "(" ^ txt ^ ")"
         in  H (Input.source true txt' range) end;

(* BU : TO BE REVISED BY BU TO 2016. WAS SORT OF A HACK ANYWAY.
   Chantal: did revise it; please double check*)
val _ = Outer_Syntax.command 
             (*@{command_spec "set_pre_safe_tac"}*)
             @{command_keyword set_pre_safe_tac}  
             "configure gen_test_gen: set pre_safe_tac"
             (Parse.ML_source >> (Toplevel.theory o 
                                      (set_wrapper 
                                         "(TestEnv.map_data_global o TestEnv.pre_safe_tac_update)" 
                                         Isar_Cmd.setup)));


val _ = Outer_Syntax.command 
             (*@{command_spec "set_pre_normalize_TNF_tac"}*)
              @{command_keyword set_pre_normalize_TNF_tac}  
             "configure gen_test_gen: pre_normalize_TNF_tac"
              (Parse.ML_source >> (Toplevel.theory o 
                                       (set_wrapper 
                                        "(TestEnv.map_data_global o TestEnv.pre_normalize_TNF_tac_update)" 
                                        Isar_Cmd.setup)))

val _ = Outer_Syntax.command 
             (*@{command_spec "set_pre_minimize_TNF_tac"}*) 
              @{command_keyword set_pre_minimize_TNF_tac}
             "configure gen_test_gen: set pre_minimize_TNF_tac"
              (Parse.ML_source >>  (Toplevel.theory o 
                                       (set_wrapper 
                                          "(TestEnv.map_data_global o TestEnv.pre_minimize_TNF_tac_update)" 
                                          Isar_Cmd.setup)))


fun pretty_cterm_style_generic f ctxt (style, (name,pos:Position.T)) =
     let val termS =  case (Symtab.lookup (f (TestEnv.get_testenv ctxt)) name) of
                           SOME k => List.map (style o Thm.term_of) k  (* (nth(k,0)) *)
                         | NONE => error "No such test suite"
     in Pretty.big_list "\\\\" (List.map (Thy_Output.pretty_term ctxt) ( termS)) end

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
*}


attribute_setup test_inst = 
                {*  Scan.lift Args.name >> (fn name =>
                         Thm.declaration_attribute (fn thm =>
                             TestEnv.map_data (TestEnv.add_abstest_data (name, thm)))) *} 
                "declare theorems for test case generation"

attribute_setup testgen_type_candidates = 
                {* Scan.repeat1 Args.typ >> 
                   (fn Ts =>
                      Thm.declaration_attribute (fn _ =>
                          TestEnv.map_data (TestEnv.type_candidates_update Ts))) *} 
                "declare testgen type candidates"

                                    
method_setup discharge_POs = 
             {* Scan.lift (Scan.option(Parse.string) >> 
                (fn params => fn ctxt => 
                   let  val _ = LogThy.start ();
                        val name = (case params of
                                      NONE => ""
                                    | SOME (s) => s);
                   in    Method.SIMPLE_METHOD (CHANGED_PROP 
                               (TestGen.discharge_POs name ctxt))
                   end)) *} 
             "eliminate POs by test instances"
                
method_setup gen_test_cases = 
             {* Scan.lift (Scan.option (Parse.nat -- Parse.nat) 
                -- Scan.repeat1 (Scan.unless (Scan.first clasimp_modifiers) Args.name)) 
                --| Method.sections clasimp_modifiers >>
                (fn (params, prog) => fn ctxt =>
                    let  val _ = LogThy.start ();
                         val ctxt' = (case params of
                                       NONE => ctxt
                                     | SOME (depth, steps) => ctxt
                                                                |> Config.put TestEnv.depth depth
                                                                |> Config.put TestEnv.steps steps);
                    in Method.SIMPLE_METHOD (CHANGED_PROP 
                                               (TestGen.gen_test_case_tac ctxt' prog))
                end) *} 
             "generate symbolic test cases"

method_setup gen_test_cases_old = 
             {* Scan.lift (Scan.option (Parse.nat -- Parse.nat) -- 
                 Scan.repeat1 (Scan.unless (Scan.first clasimp_modifiers) Args.name)) --|
                   Method.sections clasimp_modifiers >>
                (fn (params, prog) => fn ctxt =>
                    let val _ = LogThy.start ();
                        val ctxt' = (case params of
                                      NONE => ctxt
                                    | SOME (depth, steps) => ctxt
                                                               |> Config.put TestEnv.depth depth
                                                               |> Config.put TestEnv.steps steps);
                    in Method.SIMPLE_METHOD (CHANGED_PROP 
                            (TestGen.gen_test_case_old_tac ctxt' prog))
                   end)
             *} 
             "old variant of gen_test_cases"

ML{* fn ctxt =>  HEADGOAL o (K(TestGen.thyp_ify ctxt ))*}
ML{* fn ctxt =>  METHOD (HEADGOAL o (K(TestGen.thyp_ify ctxt )))*}



ML{*
val _ =
  Theory.setup
   (Method.setup @{binding thyp_ify}
      (Attrib.thms >> (fn _ => fn ctxt => METHOD (HEADGOAL o (K(TestGen.thyp_ify ctxt ))))) 
      "making testhyps explicit" #>
    Method.setup @{binding mp_ify}
      (Attrib.thms >> (fn _ => fn ctxt => METHOD (HEADGOAL o (K(TestGen.mp_fy ctxt )) ))) 
       "fast destruction matching" #>
    Method.setup @{binding all_ify}
      (Attrib.thms >> (fn _ => fn ctxt => METHOD (HEADGOAL o (K(TestGen.all_ify ctxt [])) )))
       "replace all free variables by quantifiers")
*}

end
