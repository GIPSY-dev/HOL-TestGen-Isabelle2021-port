(*****************************************************************************
 * HOL-TestGen --- theorem-prover based test case generation
 *                 http://www.brucker.ch/projects/hol-testgen/
 *                                                                            
 * FWTesting.thy --- 
 * This file is part of HOL-TestGen.
 *
 * Copyright (c) 2005-2010 ETH Zurich, Switzerland
 *               2008-2015 Achim D. Brucker, Germany
 *               2009-2017 Université Paris-Sud, France
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
 *****************************************************************************)

theory 
  FWTesting
imports 
  Testing
  "$AFP/UPF_Firewall/UPF-Firewall"
keywords
  "export_fw_data" :: diag
begin

declare dom_eq_empty_conv [simp del]

  
text{* This is the formalisation in Isabelle/HOL of firewall policies
and corresponding networks and packets. It first contains the
formalisation of stateless packet filters as described
in~\cite{brucker.ea:model-based:2008}, followed by a verified policy
normalisation technique (described in~\cite{brucker.ea:icst:2010}),
and a formalisation of stateful protocols described
in~\cite{brucker.ea:test-sequence:2007}.  *}

text{* The following statement adjusts the pre-normalization step of
the default test case generation algorithm. This turns out to be more
efficient for the specific case of firewall policies.
*}


(*
setup{* TestEnv.map_data_global (TestEnv.pre_normalize_TNF_tac_update (
                fn ctxt =>
  (TestGen.ALLCASES (asm_full_simp_tac (global_simpset_of @{theory Int})))))
 *} 
*)

text{* Next, the Isar command @{text prepare_fw_spec} is specified. It
 can be used to turn test specifications of the form: 
"$C\ x \Longrightarrow FUT\ x\ =\ policy\ x$" 
into the desired form for test case generation.  *}
ML {*
fun prepare_fw_spec_tac ctxt   =
                 (TRY(( Rule_Insts.res_inst_tac ctxt [((("x", 0), Position.none),"x")] [] @{thm spec} 1) THEN
                  (resolve_tac ctxt [allI] 1) THEN
                  (split_all_tac ctxt 1) THEN
                  (TRY (resolve_tac ctxt [impI] 1))));
*}


method_setup prepare_fw_spec = 
 {*
   Scan.succeed  (fn ctxt => SIMPLE_METHOD
       (prepare_fw_spec_tac ctxt))*} "Prepares the firewall test theorem"



ML {*
fun conj_ts_tac ctxt   = 
 (REPEAT(CHANGED(TRYALL((resolve_tac ctxt [@{thm conjI}]) THEN' (resolve_tac ctxt [@{thm impI}])))));
 *}


method_setup conj_ts = 
 {*
   Scan.succeed  (fn ctxt => SIMPLE_METHOD
       (conj_ts_tac ctxt))*} "Prepares the firewall test theorem"






ML {*
fun export_fw_data ctxt filename dataname =
    let
        val thy = Proof_Context.theory_of ctxt
        val thms = Global_Theory.get_thms thy (dataname^".test_data")
        fun generate () =
            let
                val thmsstrings = String.concat (map (fn t => ((Syntax.string_of_term ctxt o Thm.prop_of) t)^"\n"
                                                        
                                                            ) thms)
            in
                thmsstrings
            end

         val test_data_str  = Print_Mode.setmp [] (generate) ();     
        val _  = File.write (Path.explode filename) test_data_str;

    in () end
*}


ML{*
val _ =
    Outer_Syntax.command @{command_keyword export_fw_data}  "export fw test data to an external file"
                        (Parse.name -- Parse.name
                                >> (fn (filename,name) =>
                  (Toplevel.keep (fn state => export_fw_data (Toplevel.context_of state) filename name)))) ;
*}




text{* This theory contains a collection of (rather unsorted lemmas)
which are of general use when processing test specification (including
Normalization) of the Firewall Testing heap. *}


(*
definition all_positive :: "(IntegerPort_TCPUDP,'b) packet \<Rightarrow> bool" where
 "all_positive x = (id x > 0 \<and> src_port x > (0::port) \<and> dest_port x > (0::port))"



definition src_fix :: "(IntegerPort_TCPUDP,'b) packet \<Rightarrow> bool" where
 "src_fix x =  (src_port x = (1::port) \<and> src_protocol x = udp)"
*)


definition policyID where 
 "policyID = (\<lambda> x. (Some (allow (x))))"
                      

lemma setDistinct: "\<lbrakk>x \<in> a; x \<notin> b\<rbrakk> \<Longrightarrow> a \<noteq> b"
apply auto
done

lemma setDistinct3: "\<lbrakk>x \<noteq> y\<rbrakk> \<Longrightarrow>
 {{(a, b, c). a \<in> x}} \<noteq> {{(a, b, c). a \<in> y}}"
apply auto
done


lemma setDistinct4: "\<lbrakk>(a::int) \<noteq> x; a < b; x < y\<rbrakk>
                       \<Longrightarrow> {a..b} \<noteq> {x..y}"
apply (case_tac "a < x")
apply simp_all
done

lemma setDistinct2: "\<lbrakk>x \<noteq> y\<rbrakk> \<Longrightarrow>
 {(a, b). a \<in> x} \<noteq> {(a, b). a \<in> y}"
apply auto
done


lemma setDistinct1: "\<lbrakk>x \<noteq> y\<rbrakk> \<Longrightarrow>
 {(a, b, c). a \<in> x} \<noteq> {(a, b, c). a \<in> y}"
apply auto
done
 
(*
lemma AllowNMT: "\<lbrakk>x \<noteq> {}; y \<noteq> {}\<rbrakk>  \<Longrightarrow> 
 dom (Cp (AllowPortFromTo {{(a, b, c). a \<in> x}} {{(a, b, c). a \<in> y}} (p,i))) \<noteq> {}"
apply (simp add: PLemmas)
apply auto
done



lemma domDA1Cp: "dom (Cp (DenyAll \<oplus> P)) = UNIV"
apply (simp add: PLemmas)
apply (auto split: option.splits simp: deny_all_def)
done*)


lemma aux: "\<lbrakk>x \<noteq> a; y\<noteq>b; (x \<noteq> y \<and> x \<noteq> b) \<or>  (a \<noteq> b \<and> a \<noteq> y)\<rbrakk> \<Longrightarrow> {x,a} \<noteq> {y,b}"
  apply auto
done

lemma aux2: "{a,b} = {b,a}"
  apply auto
done

lemma deny_comm[simp]: "(deny() = X) = (X = deny())"
by auto

lemma allow_comm[simp]: "(allow() = X) = (X = allow())"
by auto

(*
lemma PO_add: "PO P \<Longrightarrow> P"
by (simp add: PO_def)
*)

lemma dom_2_subset1: "dom (r o_f ((A \<Otimes>\<^sub>2 B) o (\<lambda> x. (x,x)))) \<subseteq> dom A"
apply (simp add: dom_def prod_2_def  policy_range_comp_def)
apply (simp split: option.splits decision.splits)
apply auto
done


lemma dom_2_comm: "dom (A \<Otimes>\<^sub>2 B) = dom (B \<Otimes>\<^sub>2 A)"
apply (simp add: dom_def prod_2_def  policy_range_comp_def)
apply (simp split: option.splits decision.splits prod.splits)
oops


lemma dom_2_subset2: "dom (r o_f ((A \<Otimes>\<^sub>2 B) o (\<lambda> x. (x,x)))) \<subseteq> dom B"
apply (rule subsetI)
apply (simp add: dom_def prod_2_def policy_range_comp_def)
apply (simp split: option.splits decision.splits)
done


lemma dom_2: "dom A = UNIV \<Longrightarrow>
 dom (r o_f ((A \<Otimes>\<^sub>2 B) o (\<lambda> x. (x,x)))) = dom B"
apply (rule equalityI)
apply (rule dom_2_subset2)
apply (rule subsetI)
apply (simp add: dom_def prod_2_def policy_range_comp_def)
apply (simp split: option.splits decision.splits)
apply auto
done
(*
lemma domDA1: "dom (C (DenyAll \<oplus> P)) = UNIV"
apply (simp add: PLemmas)
apply (auto simp: deny_all_def C.simps)
apply (auto split: option.splits simp: deny_all_def)
done


lemma if_DA_simp: "((if P then (deny_all x) else None) =
        None) = (\<not> P)"
apply (simp add: deny_all_def)
done


lemma if_DA_simp2: "(\<exists>y. (if P then deny_all x else None) = Some y) = P"
apply auto
apply (simp add: deny_all_def)
done

lemma if_DA_simp3: "((if P then deny_all x else None) =
        Some ae) = (P \<and> deny_all x = Some ae)"
apply (simp add: deny_all_def)
done


lemma if_DA_simp4: "((if P
         then Some (allow x)
         else None) =
        None) = (\<not> P)"
apply auto
done

lemma if_DA_simp5: "((if P
         then Some (deny x)
         else None) =
        None) = (\<not> P)"
apply auto
done
*)


lemma setDistinct6: "\<lbrakk>x \<noteq> y\<rbrakk> \<Longrightarrow>
 {(a, b, c). a = x} \<noteq> {(a, b, c). a = y}"
by auto

definition ip2int :: "(int \<times> int \<times> int \<times> int) \<Rightarrow> int" where
 "ip2int x = (((fst x)*16777216) + ((fst (snd x))*65536) +
              ((fst (snd (snd x)))*256) + snd (snd (snd x)))"

(*
lemmas if_DA = if_DA_simp if_DA_simp2 if_DA_simp3 if_DA_simp4 if_DA_simp5

declare if_DA [simp]
*)
end
