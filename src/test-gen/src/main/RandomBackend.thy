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

chapter {* The random solver *}

theory RandomBackend
imports 
  HOL.HOL
  HOL.Int
  HOL.List
  TestEnv
  BackendUtils

begin


ML{* 

structure RandomBackend =
struct

open HOLogic

(* Backported from Isabelle2011-1 module Pure/Library.ML *)
fun frequency xs =
 let
   val sum = Library.foldl op + (0, map fst xs);
   fun pick n ((k: int, x) :: xs) =  if n <= k then x else pick (n - k) xs
 in pick (Random.random_range 1 sum) xs end;


val (trace, trace_setup) = Attrib.config_bool @{binding testgen_trace} (K false);

fun calc_constr_list tgt descr =
let val recTs          = Old_Datatype_Aux.get_rec_types descr;
    val newTs          = Library.take (length descr) recTs;
    val (_,(_,insts,tgt_constrs)) = hd(filter (fn (_,(n,_,_)) => n = tgt) descr)
    val T              = hd(filter (fn (Type(n,_)) => n = tgt) newTs)
    val typ_of_dtyp    = Old_Datatype_Aux.typ_of_dtyp descr
    val constr_decls   = map (fn (cname, cargs) =>
                                 Const(cname, map typ_of_dtyp cargs ---> T))
                             (tgt_constrs)
in  (map Old_Datatype_Aux.dest_DtTFree insts, constr_decls) end;


(* Getting the information associated to an extended record type name *)
fun is_record thy s =
  let
    fun remove_prefix [] = []
      | remove_prefix (c::cs) = if c = #"." then cs else remove_prefix cs
    fun remove_suffix s = String.implode (List.rev (remove_prefix (List.rev (String.explode s))))
    in
    if String.isSuffix "_ext" s then
      Record.get_info thy (remove_suffix s)
    else
      NONE
  end


(* Random value generator for user-defined records
   Note: it does not work for extended records *)
fun random_record w n max ctxt cod_term_tab i =
  let
    (* Generating random values for the fields *)
    val fields = #fields(i)
    val random_fields = List.map (fn (_,ty) => random_term' w (n+1) max ctxt cod_term_tab ty) fields
      
    (* Getting the record maker. Another way would be to generate a Const whose name is the same
       as the name of the type *)
    fun head (a $ _) = head a
      | head t = t
    val (_ $ app_make $ _) = Thm.concl_of (hd (#defs(i)))
    val make = head app_make
    
    (* Building the record *)
    val res = List.foldl (fn (f,h) => h $ f) make random_fields
  in
    res
  end

(* Random value generator for user-defined data-types *)
and random_datatype w n max ctxt cod_term_tab s S i =
  let
    val descr = #descr(i)

    val (insts,constrs) = calc_constr_list s descr

    val weighed_constrs =
      let
        fun ar args = (length (filter (fn t =>
          case t of
              Old_Datatype_Aux.DtRec _ => true
            | _ => false ) args) )
        val constr_arity_list =  map (fn (f,args) => (f,(ar args)))
               (maps (#3 o snd) descr)
      in
      map (fn (f,a) => if a = 0 then (1,f) else (a * w,f))
          constr_arity_list
      end

      val weighed_constrs = if (n >= max)
            then filter (fn (w,_) => w =1) weighed_constrs
            else weighed_constrs
      fun weight_of t = fst(hd ((filter (fn (_,ty) => ty=t)) weighed_constrs))

      fun frequency' xs =
        let
          val max = List.foldl Int.max 0 (map fst xs);
          val xs' = map (fn (x,a) => (max-x+1,a)) xs
        in
          frequency xs' 
        end

        (* the default is a random bias towards constants *)
        val constr = frequency' weighed_constrs
        val Const(h,ty) = hd (filter (fn Const(h,ty) => h = constr) constrs)
        val w          = weight_of h
        val ty_binds   = insts ~~ S
        fun ty_inst s = the (AList.lookup (op =) ty_binds s)
        val instantiated_ty = map_type_tfree ty_inst ty
        val const_head = Const(h,instantiated_ty)
        val arg_ty = binder_types instantiated_ty
      in list_comb(const_head,
           (map(random_term' w (n+1) max ctxt cod_term_tab)(arg_ty)))
      end
                               
(* Random value generator for various types *)
and random_term' w n max ctxt cod_term_tab (Type(s,S)) =
(* w => the weight on the actual level, initial value 1
   n => level counter, inital value 0
   max => maximal allowed number of levels
*)
    let val thy = Proof_Context.theory_of ctxt
    in 
       (case Symtab.lookup cod_term_tab s of
         NONE   => (* default random term generator ...
                      TODO : should do also something for functions ... *)
                   (case Type(s,S) of
                      Type(@{type_name int},_) => mk_number intT (IntInf.fromInt((Random.random_range 0 20) - 10))
                    | Type(@{type_name nat},_) => mk_nat (IntInf.fromInt((Random.random_range 0 40)))
                    | Type(@{type_name set},_) => Const(@{const_name set},dummyT) $
                                       (random_term' w n max ctxt cod_term_tab (Type(@{type_name list},S)))
                    | Type(@{type_name fun},[T, Type(@{type_name bool}, [])]) =>
                      Const(@{const_name set}, Type(@{type_name fun}, [Type(@{type_name list}, [T]), Type(s,S)])) $
                           (random_term' w n max ctxt cod_term_tab (Type(@{type_name list},[T])))
                    | Type(@{type_name fun},[T,U]) => absdummy T (random_term' w n max ctxt cod_term_tab U)
                    | _     =>
                        (case is_record thy s of
                          (* The type is a user-defined record *)
                            SOME i => random_record w n max ctxt cod_term_tab i
                          | NONE =>
                            (case BNF_LFP_Compat.get_info thy [] s of
                               (* The type is a user-defined data-type *)
                                 SOME i => random_datatype w n max ctxt cod_term_tab s S i
                               | NONE => error("Cannot generate random value for type:" ^s^"\nCan only generate random values for int, nat, set, fun, and user-defined records and datatypes")
                            )
                        )
                   )
       | SOME R => R S)
       end
   |random_term' _ _ _ _ _ _ = error "Internal error in random_term: type not ground";
 

fun random_term thy cod_term_tab typ = random_term' 1 0 10000 thy cod_term_tab typ
(* test section:

val ttt = [HOLogic.intT,HOLogic.unitT,HOLogic.boolT,
           HOLogic.mk_setT HOLogic.intT,
           HOLogic.listT HOLogic.intT];
map (random_term Symtab.empty) ttt;

 *)

fun random_insts ctxt cod_tab vars () = 
       map(fn(x as Var(s,t))=>
           (Thm.cterm_of ctxt x,Thm.cterm_of ctxt (random_term ctxt cod_tab t))) vars
    
fun single_rand_inst_tac ctxt vars thm = let
    val te = TestEnv.get_testenv ctxt
    val cod_tab = #cod_term_tab(TestEnv.rep_testenv te)
    val to_var_index   = (fn  Var(s,t) => (s,t)) o Thm.term_of
    val insts = map (fn(x,y)=> (to_var_index x,y)) (random_insts ctxt cod_tab vars ())
in
    Seq.single (Drule.instantiate_normalize ([], insts) thm)
end

fun random_inst_tac ctxt iters n thm = let
    val _    = if iters > 0 andalso Config.get ctxt trace then tracing ("Random solving subgoal "^Int.toString(n)) else () 
    val single_tac = (* print_tac "A" THEN  *)
                     (single_rand_inst_tac ctxt (BackendUtils.premvars n thm)) THEN 
                     (* print_tac "B" THEN *) 
                     (BackendUtils.solve_by_simp_tac ctxt n)
in
    (FIRST (replicate iters single_tac)) thm
end

end

*}



end
