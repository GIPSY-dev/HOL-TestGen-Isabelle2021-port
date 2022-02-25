(*****************************************************************************
 * HOL-TestGen --- theorem-prover based test case generation
 *                 http://www.brucker.ch/projects/hol-testgen/
 *
 * isar_setup.sml --- Isar setup for HOL-TestGen
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
(* $Id: isar_setup.ML 9653 2013-04-17 23:17:08Z abderrahmane.feliachi $ *)

(* at the moment, calling store_test_thm without the optional argument  works only
   in an ProofGeneral session because otherweise the call of Toplevel.pretty_state
   results in an empty list \<dots>
*)

fun store_test_thm name = Toplevel.end_proof (fn _ => fn state =>
  let
    val ctxt = Proof.context_of state;
    val _ = if Config.get ctxt TestGen.profiling then
                (Clocks.start_clock "unnamed_test_thm";
                 Clocks.rename_clock "unnamed_test_thm" name;
                 Clocks.stop_clock name)
            else
                ()

    val _ = Proof.assert_backward state;
    val {context = goal_ctxt, goal, ...} = Proof.goal state
    fun up_thy thy =
        let
          fun add_to_dm name thm thy =
              let
                val thy = TestEnv.map_data_global (TestEnv.add_test_case (name,thm)) thy
                val t = LogThy.get_tc_delta ()
                val num_of_tc = List.length
                                (List.filter (fn tc => TestGen.is_test tc) (prems_of thm))
                val _ = writeln (String.concat ["Test theorem (gen_test_cases) '",name,"': ",
						Int.toString num_of_tc,
						" test cases in ",Time.toString t, " seconds"])

                val _ = LogThy.append (String.concat [Context.theory_name thy, ", "
						    ,name, ", "
						    ,"test case, "
						    ,Int.toString num_of_tc,", "
						    , Time.toString t,"\n"])
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

(*val _ =
  Outer_Syntax.command  ("store_test_thm", (Keyword.tag_proof Keyword.qed)) "store test state (theorem)"
    (Parse.name >> store_test_thm);*)

val _ =
  Outer_Syntax.command  @{command_spec "store_test_thm"} "store test state (theorem)"
    (Parse.name >> store_test_thm);






(**********************)
fun gen_test_dataT name thy =
    let
        fun gen_test_data name   =
            let
                val _  = LogThy.start_td_timer ()
                val _ = if Config.get_global thy TestGen.profiling then
                            (Clocks.init_clocks thy;
                             Clocks.start_clock name;
                             Clocks.start_clock "gen_test_data")
                        else
                            ()

                val thy = Context.theory_map (TestGen.gen_test_data name) thy
		val t = LogThy.get_td_delta ()
                val thy = if Config.get_global thy TestGen.profiling then
                              (Clocks.stop_clock "gen_test_data";
                               Clocks.stop_clock name;
                               Clocks.flush_clocks thy)
                          else
                              thy

                val data = TestGen.get_test_data thy name
                val hyps = TestGen.get_test_hyps thy name
                val pos = TestGen.get_pos thy name
                val thy  = Sign.add_path (space_implode "_" [name]) thy;
                val thy = snd(Global_Theory.add_thmss [((@{binding test_hyps},hyps),[])] (thy));
                val thy = snd(Global_Theory.add_thmss [((@{binding test_data},data),[])] (thy))
		val thy = snd(Global_Theory.add_thmss [((@{binding pos},pos),[])] (thy))
		val _ = writeln (String.concat ["Test theorem (gen_test_data) '",name,"': ",
						Int.toString (List.length data),
						" test cases in ",Time.toString t, " seconds"])
                val _ = if not (null pos) then
                            writeln ("Warning: There were unsolved POs.")
                        else
                            ()

                val _ = LogThy.append (String.concat [Context.theory_name thy, ", "
						    ,name, ", "
						    ,"test data, "
						    ,Int.toString (List.length data),", "
						    ,Time.toString t,"\n"])
			
                val thy = Sign.parent_path thy;
            in
                thy
            end
        val thy = gen_test_data name
    in
        thy
    end

(*val _ =
    Outer_Syntax.command ("gen_test_data", Keyword.thy_script) "generate test data"
                        (Parse.name  >> (Toplevel.theory o gen_test_dataT));*)

val _ =
  Outer_Syntax.command @{command_spec "gen_test_data"} "generate test data"
                        (Parse.name  >> (Toplevel.theory o gen_test_dataT));

(**********************)

val _ =
 (* Outer_Syntax.local_theory_to_proof ("test_spec", Keyword.thy_schematic_goal) "define test specification"*)
   Outer_Syntax.local_theory_to_proof @{command_spec "test_spec"} "define test specification"   
     (Scan.optional (Parse_Spec.opt_thm_name ":" --|
      Scan.ahead (Parse_Spec.includes >> K "" ||
       Parse_Spec.locale_keyword || Parse_Spec.statement_keyword)) Attrib.empty_binding --
      Scan.optional Parse_Spec.includes [] --
      Parse_Spec.general_statement >> (fn ((a, includes), (elems, concl)) => fn lthy =>
          let val _ = if Config.get lthy TestGen.profiling then Clocks.init_clocks (Proof_Context.theory_of lthy) else ()
          in
              Specification.schematic_theorem_cmd "test_spec" NONE (K I) a includes elems concl false lthy
          end));

