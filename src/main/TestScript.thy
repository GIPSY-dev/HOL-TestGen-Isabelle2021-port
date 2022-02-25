(*****************************************************************************
 * HOL-TestGen --- theorem-prover based test case generation
 *                 http://www.brucker.ch/projects/hol-testgen/
 *                                                                            
 * TestScript.thy --- Test Script and Test Data exporter
 * This file is part of HOL-TestGen.
 *
 * Copyright (c) 2011-2015 Achim D. Brucker, Germany
 *               2016-2017 The University of Sheffield, UK
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
(* $Id: TestScript.thy 13147 2017-08-18 19:42:12Z brucker $ *)


theory   TestScript
imports  TestGen
	       "codegen_fsharp/code_fsharp"
keywords "generate_test_script"  :: thy_decl
	  and  "export_test_data"      :: diag
begin 

code_printing constant "RSF" \<rightharpoonup>
       (SML) "TestHarness.rsf"
   and (Fsharp) "TestHarness.rsf"
   and (Scala) "TestHarness.rsf"

datatype Lazy = "lazy" bool

code_printing constant "lazy"  \<rightharpoonup> 
        (SML)    "fn () => (_)" 
    and (Fsharp) "lazy ((_))"
    and (Scala)  "() =>  ((_))"

code_printing type_constructor Lazy   \<rightharpoonup> 
        (SML)    "(unit -> bool)"
    and (Fsharp) "Lazy<bool>"
    and (Scala)  "() => Boolean"

code_printing code_module "Header" \<rightharpoonup> (SML)
{* 
  (********************************************************)
  (* This file is generated automatically. Do not edit    *)
  (********************************************************)
*}

ML{*
open List;
  fun gen_ts_def dataname thy = let 

    val tsname = "test_script"
    val fqtsname = (Context.theory_name thy)^"."^dataname^"."^tsname
    val tsbnd = Binding.name tsname
    val tstype = HOLogic.listT (HOLogic.mk_tupleT[HOLogic.listT @{typ "Lazy"},@{typ "Lazy"}])

    val (td,_) = (TestGen.get_test_data thy dataname,thy);

    fun def const bnd term thy = snd (Global_Theory.add_defs  false [((bnd, 
                         (Logic.mk_equals (const, term))),[Code.add_default_eqn_attribute Code.Equation])] thy) 
      
    val prop_terms = List.map (fn p => let val _ $ ret = Thm.concl_of p  in ret end) td;
    val prems_terms = map (fn data => (map (fn p => let val _ $ ret = p in ret end) 
                                      (Thm.prems_of data))) td;
    val spec = map2 (fn x => fn y => (x,y))  prems_terms prop_terms

    fun mk_abs t = Const("TestScript.Lazy.lazy",@{typ "bool"} --> @{typ "Lazy"})$t  

    val ts_term = HOLogic.mk_list (HOLogic.mk_tupleT[HOLogic.listT @{typ "Lazy"},@{typ "Lazy"}])
                  (map (fn (a,b) =>  HOLogic.mk_tuple [HOLogic.mk_list @{typ "Lazy"} 
                  (map mk_abs a), mk_abs b]) spec) 
  in
    thy |> (Sign.add_path (space_implode "_" [dataname]))
        |> Sign.add_consts [(tsbnd, tstype, NoSyn)] 
        |> def (Const(fqtsname,tstype))  (tsbnd) ts_term
        |> (Sign.parent_path)
  end

*}


ML {*  (Outer_Syntax.command (("generate_test_script"), Position.none)
                             "generate code equation representing test script"  
                             (Parse.name >> (fn name => Toplevel.theory (gen_ts_def name)))) 
*}

ML{*
fun export_test_data ctxt filename dataname =
    let
        val filename = Path.explode filename
        val thy = Proof_Context.theory_of ctxt
        val master_dir = Resources.master_directory thy 
        val td = TestGen.get_test_data thy dataname
        val today = (Date.toString(Date.fromTimeUniv (Time.now())))^" (UTC)";
        val abs_filename = if (Path.is_absolute filename) then filename else Path.append master_dir filename
        val thyname = Context.theory_name thy
        (* fun string_of_term ctxt = Pretty.unformatted_string_of o (Syntax.unparse_term ctxt) *)
        val string_of_term  = Sledgehammer_Util.hackish_string_of_term
        fun generate () =
            let
                val num = Int.toString(length td)
                fun string_of_prems ctxt []      = ""
                  | string_of_prems ctxt (p::ps) = ("<precondition>\n"
                                                   ^"    "^(string_of_term ctxt p) ^ "\n" 
                                                   ^"  </precondition>\n")^(string_of_prems ctxt ps) 
                val thmsstrings = String.concat (map (fn t => "<testcase>\n" 
                                                              ^(string_of_prems ctxt (Thm.prems_of t))
                                                              ^"  <test>\n"
                                                              ^"    "^string_of_term ctxt (Thm.prop_of t) ^ "\n" 
                                                              ^"  </test>\n"
                                                              ^"</testcase>\n"
                                                            ) td)
            in
                "<!---------------------------------------------------------------------\n"
                ^" --    Test-Data ("^thyname^"."^dataname^", "^num^" test cases)\n"
                ^" --           generated by HOL-TestGen "^testgen_version^"\n"
                ^" --           generated on "^today^"\n"
                ^" --------------------------------------------------------------------->\n\n"
                ^thmsstrings
            end

        val test_data_str  = Print_Mode.setmp [] generate ();
        val _  = File.write (abs_filename) test_data_str
                 handle (IO.Io{name=name,...}) => warning ("Could not write \""^(name)^"\".")
    in () end
*}

ML {* 
    Outer_Syntax.command (("export_test_data"), Position.none)
                    "export test data to an external file"
                        (Parse.name -- Parse.name
                                >> (fn (filename,name) =>
                                        (Toplevel.keep (fn state => export_test_data (Toplevel.context_of state) filename name))));

 *}

end
