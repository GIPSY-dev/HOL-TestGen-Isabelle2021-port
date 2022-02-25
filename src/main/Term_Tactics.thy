
(*****************************************************************************
 * HOL-OCL --- an interactive theorem-prover for for UML/OCL
 *             http://www.brucker.ch/projects/hol-ocl/
 *                                                                            
 * isabelle2009_kernel_patch.ML --- Isabelle kernel extensions
 * This file is part of HOL-OCL.
 *
 * Copyright (c) 2003-2007 ETH Zurich, Switzerland
 *               2008-2009 Achim D. Brucker, Germany
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
(* $Id: isabelle2009_kernel_patch.ML 9289 2012-01-30 18:22:21Z krieger $ *)


theory Term_Tactics
imports Main
begin


(* Code for Isabelle2004/5-Kernel. Should go to Tactic - structure.        *)
(* (up to make_elim_preserve, which is already there ...                 *)
(* >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>> *)

(*
Like lift_inst_rule but takes terms, not strings, where the terms may contain
Free variables referring to parameters of the subgoal (following the
conventions of the string-based version).

insts: [...,(vj,tj),...]

Both vj and tj must be type correct and have the same types as in the
string-based version (i.e. have the types *before lifting* over the
context of subgoal i. In particular, tj may not contain loose bound 
variables. In order to use lift_inst_rule with subterms of the subgoal,
these have to be substituted by free variables before.

NB: the types in insts must be correctly instantiated already,
    i.e. Tinsts is not applied to insts.


An Example in HOL:
==================

We assume st = [| [] @ y = y @ [];
                  !!a list. list @ y = y @ list ==> (a # list) @ y = y @ a # list |]
               ==> (x @ y = y @ x)" : Thm.thm,
i = 2, rule = sym and a standard test-based substitution
sinsts = [("t","(a # list) @ y")]. 

Then standard lift_inst_rule (st, i, sinsts, rule) yields:

  "(!!a list. list @ y = y @ list ==> ?s1 a list = (a # list) @ y)
      ==> (!!a list. list @ y = y @ list ==> (a # list) @ y = ?s1 a list)"

i.e. a lifted version of 'sym'.

Internally, the variables were set to:

     val params = [("a", "'a"), ("list", "'a List.list")];
     val inc = 1;
     val used = ["'a"]:: string list;
     val Tinsts = [(("'a", 0), "'a list")] : (Term.indexname * Thm.ctyp) list;
     val insts = [("?t", "(a # list) @ y")] : (Thm.cterm * Thm.cterm) list;

in this case.

Now we emulate the effect of "lift_inst_rule" by "term_lift_inst_rule",
we simply have to convert the substitutions:
 
   val Tinsts'= map (fn(x,y) => (x,#T(rep_ctyp y))) Tinsts;
   (*val Tinst' = [(("'a", 0), "'a List.list")]:(Term.indexname*Term.typ)list*)
   val insts' = map (fn(x,y)=>(dest_Var(term_of x), term_of y)) insts;
   (*[((("t", 0), "'a List.list"),
        Const ("List.op @", "['a List.list, 'a List.list] => 'a List.list")
       $(Const("List.list.Cons","['a, 'a List.list] => 'a List.list") $
              Free ("a", "'a") $ Free ("list", "'a List.list")) $
              Free ("y", "'a List.list"))]
    :((Term.indexname * Term.typ) * Term.term) list *)

Thus, we get:

    lift_inst_rule (st, i, sinsts, rule)
  = term_lift_inst_rule (st, i, Tinsts', insts', rule)


where (Tinsts', insts') = read_insts_in_state (st, i, sinsts, rule).
This explains the connection between string- and term-based
versions.

Unfortunately, the term_lift_inst_rule exported from the
the structure Tactics (in Isabelle/src/Pure/tactic.ML)
DOES NOT satisfy the desired equality - in subtle special
cases related to paramaters of a subgoal in st, it behaves
different. Therefore, a re-implementation based on
lift_inst_rule-code is done here.

On top of this, the definition of term based substitution
tactic variants for res_inst_tac, eres_inst_tac, dres_inst_tac is
straigt forward.                

COULD BE RealIZED BY MORE GENERAL VERSION OF gen_compose_inst_tac, TOO. 

*)
ML{*
signature TERM_TACTICS =
sig
val params_of_state     : thm -> int -> (string * typ) list
(*
val read_insts_in_state : thm * int * (indexname * string) list * thm
                           -> (ctyp * ctyp) list * (cterm * cterm) list
*)
val term_lift_inst_rule : Proof.context 
                           -> thm * int * (ctyp * ctyp) list * (cterm * cterm) list * thm -> thm
val compose_terminst_tac: Proof.context 
                           -> (ctyp * ctyp) list
                           -> (cterm * cterm) list -> bool * thm * int -> int -> tactic
val res_terminst_tac    : Proof.context 
                           -> (ctyp * ctyp) list
                           -> (cterm * cterm) list -> thm -> int -> tactic
val eres_terminst_tac   : Proof.context 
                           -> (ctyp * ctyp) list
                           -> (cterm * cterm) list -> thm -> int -> tactic
val make_elim_preserve  : Proof.context -> thm -> thm
val cut_terminst_tac    : Proof.context 
                           ->(ctyp * ctyp) list
                           -> (cterm * cterm) list -> thm -> int -> tactic
val forw_terminst_tac   : Proof.context 
                           ->(ctyp * ctyp) list 
                           -> (cterm * cterm) list -> thm -> int -> tactic
val dres_terminst_tac   : Proof.context 
                           -> (ctyp * ctyp) list
                           -> (cterm * cterm) list -> thm -> int -> tactic
(*
val convert_tinsts      : ((indexname * sort) * typ) list -> theory -> (ctyp * ctyp) list
val convert_substs      : ((indexname * typ) * term) list -> theory -> (cterm * cterm) list
*)
val subgoal_terminst_tac: Proof.context 
                           -> (ctyp * ctyp) list 
                           -> term -> int -> tactic
end;

*}


ML{*
structure Term_Tactics  : TERM_TACTICS  =
struct

open Thm;
(* copied code from Isabelle/src/Pure/tactic.ML,
   essentially for debugging purposes ... (version 2005)
   >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>
 *)

(*Determine print names of goal parameters (reversed)*)
fun innermost_params i st = (fn goal =>
    Term.rename_wrt_term goal (Logic.strip_params goal)) (Logic.get_goal (Thm.prop_of st) i);
(*params of subgoal i as they are printed*)
fun params_of_state st i = rev (innermost_params i st);
fun cterm_fun f ct = Thm.global_cterm_of (Thm.theory_of_cterm ct) (f (Thm.term_of ct));
(*********

(*read instantiations with respect to subgoal i of proof state st*)
 fun read_insts_in_state (st, i, sinsts, rule) =
  let val thy = Thm.theory_of_thm st
      and params = params_of_state st i
      and rts = Drule.types_sorts rule and (types,sorts) = Drule.types_sorts st
      fun types'(a, ~1) = (case AList.lookup (op =) params a of NONE => types (a, ~1) | sm => sm)
        | types' ixn = types ixn;
      val used = Drule.add_used rule (Drule.add_used st []);
  in read_insts thy rts (types',sorts) used sinsts end;

*************)



(* copied code from Isabelle/src/Pure/tactic.ML,
   but modified. (deletion of its first line
   and expansion of the parameters) ... (version 2005)
   >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>
 *)

fun term_lift_inst_rule ctxt (st, i, Tinsts, insts, rule) =
let (*val {maxidx,...} = rep_thm st*)
    val maxidx  = Thm.maxidx_of st
    and params = params_of_state st i
    val paramTs = map #2 params
    and inc = maxidx+1
    fun ctyp_fun f cT = Thm.ctyp_of ctxt (f (Thm.typ_of cT));
    fun liftvar (Var ((a,j), T)) = Var((a, j+inc), paramTs---> Logic.incr_tvar inc T)
      | liftvar t = raise TERM("Variable expected", [t]);
    fun liftterm t 
      = fold_rev absfree params (Logic.incr_indexes([],paramTs,inc) t)
    (*Lifts instantiation pair over params*)
    (*fun liftpair (cv,ct) = (cterm_fun liftvar cv, cterm_fun liftterm ct)*)

    val to_var_index   = (fn  Var(s,t) => (s,t)) o Thm.term_of
    val to_tvar_index  = (fn  TVar(s,t) => (s,t)) o Thm.typ_of

    fun liftpair (cv,ct) = ((to_var_index o (cterm_fun liftvar)) cv, 
                            cterm_fun liftterm ct)
    fun lifttvar (c,tt) =  ((to_tvar_index o ctyp_fun (Logic.incr_tvar inc)) c, 
                            ctyp_fun (Logic.incr_tvar inc) tt) 
in  Drule.instantiate_normalize (map lifttvar Tinsts, map liftpair insts)
			                          (Thm.lift_rule (Thm.cprem_of st i) rule)
end;


(* copied code from Isabelle/src/Pure/tactic.ML, (gen_compose_inst_tac)
   but modified. (definition unfolding, exchange of lifting function,
   adoption of parameters) ... (version 2005)
   >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>
 *)

fun compose_terminst_tac ctxt Tinsts insts (bires_flg, rule, nsubgoal) i st =
  if i > nprems_of st then no_tac st
  else st |>
    (compose_tac ctxt 
                 (bires_flg, term_lift_inst_rule ctxt (st, i, Tinsts, insts, rule), nsubgoal) 
                 i
     handle TERM (msg,_)   => (warning msg;  no_tac)
          | THM  (msg,_,_) => (warning msg;  no_tac));
                                                 
                                 
(*"Resolve" version.  Note: res_inst_tac cannot behave sensibly if the
  terms that are substituted contain (term or type) unknowns from the
  goal, because it is unable to instantiate goal unknowns at the same time.
                                                                                  
  The type checker is instructed not to freeze flexible type vars that
  were introduced during type inference and still remain in the term at the
  end.  This increases flexibility but can introduce schematic type vars in
  goals.
*)

(* copied code from Isabelle/src/Pure/tactic.ML, (res_inst_tac etc.)
   but modified. (definition unfolding, exchange of lifting function,
   adoption of parameters) ... (version 2005)
   >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>
 *)

fun res_terminst_tac ctxt Tinsts insts rule i =
    compose_terminst_tac ctxt Tinsts insts (false, rule, nprems_of rule) i;
                                                                                  
(*eresolve elimination version*)
fun eres_terminst_tac ctxt Tinsts insts rule i =
    compose_terminst_tac ctxt Tinsts insts (true, rule, nprems_of rule) i;


(*For forw_inst_tac and dres_inst_tac.  Preserve Var indexes of rl;
  increment revcut_rl instead. *)
(* COPIED FROM TACTIC STRUCTURE. SUPERFLUOUS HERE IF IT WOULD BE EXPORTED !!! *)

fun make_elim_preserve rl = Rule_Insts.make_elim_preserve rl

(*
fun make_elim_preserve rl =
  let val {maxidx,...} = rep_thm rl
      val thy = Thm.theory_of_thm rl
      fun cvar ixn = cterm_of (thy) (Var(ixn,propT));
      val revcut_rl' =
          Drule.instantiate_normalize ([],  [(cvar("V",0), cvar("V",maxidx+1)),
				             (cvar("W",0), cvar("W",maxidx+1))]) revcut_rl
      val arg = (false, rl, nprems_of rl)
      val [th] = Seq.list_of (Thm.bicompose false arg 1 revcut_rl')
  in  th  end
  handle Bind => raise THM("make_elim_preserve", 1, [rl]);
*)

(*instantiate and cut -- for a FACT, anyway...*)
fun cut_terminst_tac ctxt Tinsts insts rule = res_terminst_tac ctxt Tinsts insts (make_elim_preserve ctxt rule);

(*forward tactic applies a RULE to an assumption without deleting it*)
fun forw_terminst_tac ctxt Tinsts insts rule =   cut_terminst_tac ctxt Tinsts insts rule THEN' assume_tac ctxt;

(*dresolve tactic applies a RULE to replace an assumption*)
fun dres_terminst_tac ctxt Tinsts insts rule =  eres_terminst_tac ctxt Tinsts insts (make_elim_preserve ctxt rule);

(* conversions to handle depricated versions of this module : 
   >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>> *)

fun convert_tinsts Tinsts thy = map (fn(x,y) => (Thm.ctyp_of thy (TVar x), Thm.ctyp_of thy y)) Tinsts;
fun convert_substs Subst thy  = map (fn(x,y) => (Thm.cterm_of thy (Var x), Thm.cterm_of thy y)) Subst;

(* Of course, some code duplication can be can be avoided by introducing
   higher-order variants. *)


fun subgoal_terminst_tac ctxt insts sprop goal st =
  (DETERM o (res_terminst_tac ctxt insts)
           (convert_substs [((("psi",0),propT), sprop)] ctxt) cut_rl THEN' 
  SUBGOAL (fn (prop, _) =>
           let val concl' = Logic.strip_assums_concl prop in
           if null (Term.add_tvars concl' []) then ()
           else warning"Type variables in new subgoal: add a type constraint?";
           all_tac
  end)) goal st;
end;

*}



ML{* Term_Tactics.subgoal_terminst_tac *}
end
