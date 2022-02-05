(*****************************************************************************
 * HOL-TestGen --- theorem-prover based test case generation
 *                 http://www.brucker.ch/projects/hol-testgen/
 *
 * TestEnv.ML  --- environment for configuration parameters
 * This file is part of HOL-TestGen.
 *
 * Copyright (c) 2005-2007 ETH Zurich, Switzerland
 *               2008-2013 Achim D. Brucker, Germany
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

signature TESTENV =
sig
   type test_derivation_rule = Proof.context -> int -> thm -> (int * tactic) list

   (* Core data structure for the test environment.
      Contains tables, parameters, all sorts of "screws"
      to control the test generation process. *)
   type testinfo =
               {test_thm_tab    : thm Symtab.table, (* name to testthm *)

                type_candicates : typ list, (* type grounding list *)

                cod_term_tab    : (typ list -> term) Symtab.table,
                                       (* random generators for terms,
                                          tab assigns to each type constuctor
                                          name a generator that gets the
                                          instances of type constructor as args.*)
                abstest_data_tab: (thm list) Symtab.table,
                                       (* assigns name to list of
                                          abstract (local) test data statements *)
                test_data_tab   : (thm list) Symtab.table,

                pre_safe_tac           :  Proof.context -> tactic,
                pre_normalize_TNF_tac  :  Proof.context -> tactic,
                pre_minimize_TNF_tac   :  Proof.context -> tactic,
		test_derivation_rules  :  test_derivation_rule Unsynchronized.ref list
                };

   val prelude            : bool Config.T
   val wrapper            : bool Config.T
   val toString           : string Config.T
   val setup_code         : string Config.T
   val dataconv_code      : string Config.T

   val depth              : int Config.T  (* data structure depth *)
   val breadth            : int Config.T  (* no of free's in testspec *)

   val bound              : int Config.T  (* global bound for data statements *)
   val case_breadth       : int Config.T  (* no of test data per case,
                                             weakening uniformity *)
   val iterations         : int Config.T  (* number of random attempts to solve a case *)

   val type_range_bound   : int Config.T  (* effectively used elements
                                             type grounding list *)

   val SMT                : bool Config.T
   val get_smt_facts      : Proof.context -> thm list

   type testenv
   val  rep_testenv       : testenv -> testinfo

   val get_data : Proof.context -> testenv
   val map_data : (testenv -> testenv) -> Context.generic -> Context.generic
   val get_data_global : theory -> testenv
   val map_data_global : (testenv -> testenv) -> theory -> theory
   val print_data : Proof.context -> unit


   val  add_test_case     : string * thm -> testenv -> testenv
   (*   add test theorem of "name".
        The test-theorem is assumed to consist of either clauses in TNF or
        of Test Hypotheses. *)

   val  del_test_case     : string -> testenv -> testenv
   val  add_test_data     : string * thm -> testenv -> testenv
   (* used to insert abstract test data registrated under
      "string" into the test environment; abstract test data
      (or "local test theorems") were used in gen_test_data *)
   val  del_test_data     : string -> testenv -> testenv
   (* erase abstract test data from test environment *)

   val thm_tab            : testenv -> thm Symtab.table
   val absdata_tab        : testenv -> thm list Symtab.table
   val jdmt_tab           : testenv -> thm list Symtab.table

   val thm_tab_update     : thm Symtab.table -> testenv -> testenv
   val jdmt_tab_update    : thm list Symtab.table -> testenv -> testenv

   val get_pre_safe_tac   : testenv -> Proof.context -> tactic
   val get_pre_normalize_TNF_tac : testenv -> Proof.context -> tactic
   val get_pre_minimize_TNF_tac  : testenv -> Proof.context -> tactic

   val get_test_derivation_rules : testenv -> test_derivation_rule list
   val add_test_derivation_rule : test_derivation_rule -> testenv -> testenv

   val type_candidates_update   : typ list -> testenv -> testenv
   val pre_safe_tac_update     :  (Proof.context -> tactic) -> testenv -> testenv
   val pre_normalize_TNF_tac_update : (Proof.context -> tactic) -> testenv -> testenv
   val pre_minimize_TNF_tac_update  : (Proof.context -> tactic) -> testenv -> testenv

   val setup: theory -> theory
end

structure TestEnv : TESTENV =
struct

open HOLogic;

type test_derivation_rule = Proof.context -> int -> thm -> (int * tactic) list

type testinfo ={test_thm_tab    : thm Symtab.table, (* name to testthm *)

                type_candicates : typ list, (* type grounding list *)

                cod_term_tab    : (typ list -> term) Symtab.table,
                                    (* random generators for terms,
                                       tab assigns to each type constuctor
                                       name a generator that gets the
                                       instances of type constructor as args.*)
                abstest_data_tab: (thm list) Symtab.table,
                                    (* assigns name to list of
                                       data statements *)
                test_data_tab   : (thm list) Symtab.table,
                pre_safe_tac           :  Proof.context -> tactic,
                pre_normalize_TNF_tac  :  Proof.context -> tactic,
                pre_minimize_TNF_tac   :  Proof.context -> tactic,
		test_derivation_rules  :  test_derivation_rule Unsynchronized.ref list
                };

val (prelude, prelude_setup) = Attrib.config_bool @{binding testgen_prelude} (K true);
val (wrapper, wrapper_setup) = Attrib.config_bool @{binding testgen_wrapper} (K true);
val (toString, toString_setup) = Attrib.config_string @{binding testgen_toString} (K "");
val (setup_code, setup_code_setup) = Attrib.config_string @{binding testgen_setup_code} (K "");
val (dataconv_code, dataconv_code_setup) = Attrib.config_string @{binding testgen_dataconv_code} (K "");
val (depth, depth_setup) = Attrib.config_int @{binding testgen_depth} (K 3);
val (breadth, breadth_setup) = Attrib.config_int @{binding testgen_breadth} (K 1);
val (bound, bound_setup) = Attrib.config_int @{binding testgen_bound} (K 200);
val (case_breadth, case_breadth_setup) = Attrib.config_int @{binding testgen_case_breadth} (K 1);
val (iterations, iterations_setup) = Attrib.config_int @{binding testgen_iterations} (K 25);
val (type_range_bound, type_range_bound_setup) = Attrib.config_int @{binding testgen_type_range_bound} (K 1);
val (SMT, SMT_setup) = Attrib.config_bool @{binding testgen_SMT} (K false);

structure TestGen_SMT
  = Named_Thms (val name = @{binding "testgen_smt_facts"} val description = "Facts for HOL-TestGen SMT solving");

val get_smt_facts = TestGen_SMT.get;

datatype testenv   = Testenv of testinfo

fun rep_testenv (Testenv X) = X;


val initial_testenv     = Testenv
                            {test_thm_tab    = Symtab.empty,

                             type_candicates = [HOLogic.intT,HOLogic.unitT,
                                                HOLogic.boolT,
                                                HOLogic.mk_setT HOLogic.intT,
                                                HOLogic.listT HOLogic.intT],
                             cod_term_tab    = Symtab.empty,
                             abstest_data_tab= Symtab.empty,
                             test_data_tab   = Symtab.empty,
                             pre_safe_tac         = fn ctxt => all_tac,
                             pre_normalize_TNF_tac =  fn ctxt => all_tac,
                             pre_minimize_TNF_tac  =  fn ctxt => all_tac,
			     test_derivation_rules = []
};

fun merge_testenv
   (Testenv{test_thm_tab=tttab,
            type_candicates=tc,
            cod_term_tab=ctt,     abstest_data_tab=tdt,
            test_data_tab=tjt,pre_safe_tac=pst,pre_normalize_TNF_tac=pnt,pre_minimize_TNF_tac=pmt,
	   test_derivation_rules = tdr},
    Testenv{test_thm_tab=tttab',
            type_candicates=tc',
            cod_term_tab=ctt',    abstest_data_tab=tdt',
            test_data_tab=tjt',pre_safe_tac=pst',pre_normalize_TNF_tac=pnt',pre_minimize_TNF_tac=pmt',
	    test_derivation_rules = tdr'}) =

    Testenv{test_thm_tab  = Symtab.merge (Thm.eq_thm) (tttab,tttab'),
            type_candicates       = distinct (op=) (tc@tc'),
            cod_term_tab          = Symtab.empty,
                                    (* don't know what a senseful
                                       definition of override could
                                       be; therefore constraint to the
                                       simplest and most conservative
                                       one *) 
            abstest_data_tab      = Symtab.merge (fn (t1, t2) => List.all Thm.eq_thm (map2 (fn a => fn b => (a, b)) t1 t2)) (tdt,tdt'),
            test_data_tab         = Symtab.merge (fn (t1, t2) => List.all Thm.eq_thm (map2 (fn a => fn b => (a, b)) t1 t2)) (tjt,tjt'),
            pre_safe_tac          = pst,
            pre_normalize_TNF_tac  = pnt,
            pre_minimize_TNF_tac   = pmt,
	    test_derivation_rules = distinct (op=) (tdr@tdr')};


(* Context data *)

structure Data = Generic_Data
(
  type T = testenv
  val empty = initial_testenv
  val extend = I
  val merge = merge_testenv
);

val get_data = Data.get o Context.Proof;
val map_data = Data.map;

val get_data_global = Data.get o Context.Theory;
val map_data_global = Context.theory_map o map_data;

fun print_data ctxt =
    let val {test_thm_tab,
            type_candicates,
            cod_term_tab, abstest_data_tab,test_data_tab,pre_safe_tac,
            pre_normalize_TNF_tac,pre_minimize_TNF_tac, test_derivation_rules} =
            rep_testenv (get_data ctxt)
        val depth = Config.get ctxt depth
        val breadth = Config.get ctxt breadth
        val bound = Config.get ctxt bound
        val iterations = Config.get ctxt iterations
        fun H (n,thm) = [Pretty.str (n^":"), Display.pretty_thm ctxt thm]
        fun H2(n,thms)=
          [Pretty.str (n^":"), Pretty.str "======"] @
              map (Display.pretty_thm ctxt) thms @ [Pretty.str "======"]
    in  [Pretty.str ">>> Testenvironment >>>>>>>>>>>>>>>>>",
         Pretty.str "+++ Control Data: +++++++++++++++++++",
         Pretty.str ("*** default depth:   "^Int.toString(depth)),
         Pretty.str ("*** default breadth: "^Int.toString(breadth)),
         Pretty.str ("*** bound:           "^Int.toString(bound)),
         Pretty.str ("*** iterations:      "^Int.toString(iterations)),
         Pretty.str "+++ Testtheoremtable: +++++++++++++++"] @
         maps H (Symtab.dest test_thm_tab) @
        [Pretty.str "+++ Testjudgements: +++++++++++++++++"] @
         maps H2 (Symtab.dest test_data_tab) @
        [Pretty.str "+++ Testdatatable: ++++++++++++++++++"] @
         maps H2 (Symtab.dest abstest_data_tab) @
        [Pretty.str "<<< Testenvironment <<<<<<<<<<<<<<<<<"]
    end |> Pretty.chunks |> Pretty.writeln;


fun add_test_case (name,thm)
    (Testenv {test_thm_tab,
              type_candicates,
              cod_term_tab, abstest_data_tab,test_data_tab,pre_safe_tac,pre_normalize_TNF_tac,pre_minimize_TNF_tac,
	      test_derivation_rules}) =
    Testenv({test_thm_tab=Symtab.update(name,thm)test_thm_tab,
             type_candicates=type_candicates,
             cod_term_tab=cod_term_tab,
             abstest_data_tab=abstest_data_tab,
             test_data_tab=test_data_tab, pre_safe_tac=pre_safe_tac,pre_normalize_TNF_tac=pre_normalize_TNF_tac,
             pre_minimize_TNF_tac=pre_minimize_TNF_tac,
	     test_derivation_rules = test_derivation_rules});


fun del_test_case name (Testenv {test_thm_tab,
             type_candicates,cod_term_tab, abstest_data_tab,
             test_data_tab,pre_safe_tac,pre_normalize_TNF_tac,pre_minimize_TNF_tac,
				 test_derivation_rules}) =
    Testenv({test_thm_tab=Symtab.delete_safe name test_thm_tab,
             type_candicates=type_candicates,
             cod_term_tab=cod_term_tab, abstest_data_tab=abstest_data_tab,
             test_data_tab=test_data_tab, pre_safe_tac=pre_safe_tac,pre_normalize_TNF_tac=pre_normalize_TNF_tac,
             pre_minimize_TNF_tac=pre_minimize_TNF_tac,
	     test_derivation_rules = test_derivation_rules});




fun add_test_data (name,thm)
   (Testenv {test_thm_tab,
             type_candicates,
             cod_term_tab, abstest_data_tab,test_data_tab,pre_safe_tac,pre_normalize_TNF_tac,pre_minimize_TNF_tac,
	     test_derivation_rules}) =
    Testenv({test_thm_tab=test_thm_tab,
             type_candicates=type_candicates,
             cod_term_tab=cod_term_tab,
             abstest_data_tab=Symtab.cons_list (name,thm) abstest_data_tab,
             test_data_tab=test_data_tab,pre_safe_tac=pre_safe_tac,pre_normalize_TNF_tac=pre_normalize_TNF_tac,
             pre_minimize_TNF_tac=pre_minimize_TNF_tac,
	     test_derivation_rules = test_derivation_rules});


fun del_test_data name
   (Testenv {test_thm_tab,
             type_candicates,
             cod_term_tab,abstest_data_tab,test_data_tab,pre_safe_tac,pre_normalize_TNF_tac,pre_minimize_TNF_tac,
	     test_derivation_rules}) =
    Testenv({test_thm_tab=test_thm_tab,
             type_candicates=type_candicates,
             cod_term_tab=cod_term_tab,
             abstest_data_tab=Symtab.delete_safe name abstest_data_tab,
             test_data_tab=test_data_tab,pre_safe_tac=pre_safe_tac,pre_normalize_TNF_tac=pre_normalize_TNF_tac,
             pre_minimize_TNF_tac=pre_minimize_TNF_tac,
	     test_derivation_rules = test_derivation_rules});


fun thm_tab te = #test_thm_tab (rep_testenv te)
fun absdata_tab te = #abstest_data_tab(rep_testenv te)
fun jdmt_tab te = #test_data_tab(rep_testenv te)
(* In the sequel we also use the term "test judgement" synonymously
   for "test data statement". *)

fun thm_tab_update thm_tab
       (Testenv{test_thm_tab=tttab,
            type_candicates=tc,
            cod_term_tab=ctt,     abstest_data_tab=tdt,
            test_data_tab=tjt,pre_safe_tac=pst,pre_normalize_TNF_tac=pnt,pre_minimize_TNF_tac=pmt,
		test_derivation_rules = tdr}) =
       (Testenv{test_thm_tab=thm_tab,
                type_candicates=tc,
                cod_term_tab=ctt,     abstest_data_tab=tdt,
                test_data_tab=tjt,pre_safe_tac=pst,pre_normalize_TNF_tac=pnt,pre_minimize_TNF_tac=pmt,
		test_derivation_rules = tdr});

fun jdmt_tab_update jdmt_tab
       (Testenv{test_thm_tab=tttab,
            type_candicates=tc,
            cod_term_tab=ctt,     abstest_data_tab=tdt,
            test_data_tab=tjt,pre_safe_tac=pst,pre_normalize_TNF_tac=pnt,pre_minimize_TNF_tac=pmt,
		test_derivation_rules = tdr}) =
       (Testenv{test_thm_tab=tttab,
                type_candicates=tc,
                cod_term_tab=ctt,     abstest_data_tab=tdt,
                test_data_tab=jdmt_tab,pre_safe_tac=pst,pre_normalize_TNF_tac=pnt,pre_minimize_TNF_tac=pmt,
		test_derivation_rules = tdr});


fun type_candidates_update (type_candidates)
       (Testenv{test_thm_tab=tttab,
                type_candicates=tc,
                cod_term_tab=ctt,     abstest_data_tab=tdt,
                test_data_tab=tjt,pre_safe_tac=pst,pre_normalize_TNF_tac=pnt,pre_minimize_TNF_tac=pmt,
		test_derivation_rules = tdr})
        =
       (Testenv{test_thm_tab=tttab,type_candicates=type_candidates,
                cod_term_tab=ctt,     abstest_data_tab=tdt,
                test_data_tab=tjt,pre_safe_tac=pst,pre_normalize_TNF_tac=pnt,pre_minimize_TNF_tac=pmt,
		test_derivation_rules = tdr});

fun pre_safe_tac_update (pre_safe_tat)
       (Testenv{test_thm_tab=tttab,
                type_candicates=tc,
                cod_term_tab=ctt,     abstest_data_tab=tdt,
                test_data_tab=tjt,pre_safe_tac=pst,pre_normalize_TNF_tac=pnt,pre_minimize_TNF_tac=pmt,
		test_derivation_rules = tdr})
        =
       (Testenv{test_thm_tab=tttab,type_candicates=tc,
                cod_term_tab=ctt,     abstest_data_tab=tdt,
                test_data_tab=tjt,pre_safe_tac=pre_safe_tat,pre_normalize_TNF_tac=pnt,pre_minimize_TNF_tac=pmt,
		test_derivation_rules = tdr});


fun pre_normalize_TNF_tac_update (pre_normalize_TNF_tac)
       (Testenv{test_thm_tab=tttab,
                type_candicates=tc,
                cod_term_tab=ctt,     abstest_data_tab=tdt,
                test_data_tab=tjt,pre_safe_tac=pst,pre_normalize_TNF_tac=pnt,pre_minimize_TNF_tac=pmt,
		test_derivation_rules = tdr})
        =
       (Testenv{test_thm_tab=tttab,
                type_candicates=tc,
                cod_term_tab=ctt,     abstest_data_tab=tdt,
                test_data_tab=tjt,pre_safe_tac=pst,pre_normalize_TNF_tac=pre_normalize_TNF_tac,
                pre_minimize_TNF_tac=pmt,
		test_derivation_rules = tdr});


fun pre_minimize_TNF_tac_update (pre_minimize_TNF_tac)
       (Testenv{test_thm_tab=tttab,
                type_candicates=tc,
                cod_term_tab=ctt,     abstest_data_tab=tdt,
                test_data_tab=tjt,pre_safe_tac=pst,pre_normalize_TNF_tac=pnt,
                pre_minimize_TNF_tac=pmt,
		test_derivation_rules = tdr})
        =
       (Testenv{test_thm_tab=tttab,
                type_candicates=tc,
                cod_term_tab=ctt,     abstest_data_tab=tdt,
                test_data_tab=tjt,pre_safe_tac=pst,pre_normalize_TNF_tac=pnt,
                pre_minimize_TNF_tac=pre_minimize_TNF_tac,
		test_derivation_rules = tdr});




fun get_pre_safe_tac (Testenv{pre_safe_tac=pst, ...}) = pst;
fun get_pre_normalize_TNF_tac (Testenv{pre_normalize_TNF_tac=pnt, ...}) = pnt;
fun get_pre_minimize_TNF_tac (Testenv{pre_minimize_TNF_tac=pmt, ...}) = pmt;

fun get_test_derivation_rules (Testenv{test_derivation_rules = tdr, ...}) = map (op !) tdr;

fun add_test_derivation_rule (tdr)
       (Testenv{test_thm_tab=tttab,
                type_candicates=tc,
                cod_term_tab=ctt,     abstest_data_tab=tdt,
                test_data_tab=tjt,pre_safe_tac=pst,pre_normalize_TNF_tac=pnt,
                pre_minimize_TNF_tac=pmt,
		test_derivation_rules = tdrs})
        =
       (Testenv{test_thm_tab=tttab,
                type_candicates=tc,
                cod_term_tab=ctt,     abstest_data_tab=tdt,
                test_data_tab=tjt,pre_safe_tac=pst,pre_normalize_TNF_tac=pnt,
                pre_minimize_TNF_tac=pmt,
		test_derivation_rules = (Unsynchronized.ref tdr)::tdrs});

(* module setup *)

val setup =
  prelude_setup #>
  wrapper_setup #>
  toString_setup #>
  setup_code_setup #>
  dataconv_code_setup #>
  depth_setup #>
  breadth_setup #>
  bound_setup #>
  case_breadth_setup #>
  iterations_setup #>
  SMT_setup #>
  TestGen_SMT.setup;

end (*struct *);


