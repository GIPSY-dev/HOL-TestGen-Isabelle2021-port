theory SharedMemory_test
imports 
Testing
       "SharedMemory"
begin

subsection{* Our Local Instance of a Global memory Model *}

type_synonym task_id = int
type_synonym loc = int

type_synonym global_mem = "((task_id\<times>loc), int)memory"

definition \<sigma>\<^sub>0 :: "global_mem"
where     "\<sigma>\<^sub>0 \<equiv> init |> (0,0) <| [0,0,0,0]
                     |> (2,0) <| [0,0]
                     |> (4,0) <| [2,0]" 


(* value "(\<sigma>\<^sub>0 ((4, 0)\<Join>(2, 1))) $ (4, 0)" *)
find_theorems "sharing"

lemma \<sigma>\<^sub>0_Domain: "Domain \<sigma>\<^sub>0 = {(4, 1), (4, 0), (2, 1), (2, 0), (0, 3), (0, 2), (0, 1), (0, 0)}"
unfolding \<sigma>\<^sub>0_def
by(simp add: \<sigma>\<^sub>0_Domain sharing_upd)


datatype in_c = load   task_id loc
              | store  task_id loc int
              | share  task_id loc task_id loc

thm in_c.split

datatype out = load_ok   int
             | store_ok
             | share_ok

fun    precond :: "global_mem \<Rightarrow> in_c \<Rightarrow> bool"
where "precond \<sigma> (load  tid addr) = ((tid,addr) \<in> Domain \<sigma>)"
    | "precond \<sigma> (store tid addr n) = True"
    | "precond \<sigma> (share tid addr tid' addr') = ((tid,addr) \<in> Domain \<sigma> \<and> (tid',addr') \<in> Domain \<sigma>)"

term "load_ok (\<sigma>\<^sub>0 $ (tid,addr))"

fun    postcond :: "in_c \<Rightarrow> global_mem \<Rightarrow> (out \<times> global_mem) set"
where "postcond (load tid addr) \<sigma>    = {(n,\<sigma>'). (n = load_ok (\<sigma> $ (tid,addr))) \<and> \<sigma>'=\<sigma>}"
    | "postcond (store tid addr m) \<sigma> = {(n,\<sigma>'). (n = store_ok \<and> \<sigma>'= \<sigma>((tid, addr):=\<^sub>$ m))}"
    | "postcond (share tid addr tid' addr' ) \<sigma> = { (n,\<sigma>'). n = share_ok \<and> \<sigma>'=\<sigma>((tid,addr) \<Join> (tid',addr'))}" 


definition "SYS = (strong_impl precond postcond)"

lemma SYS_is_strong_impl : "is_strong_impl precond postcond SYS"
by(simp add: SYS_def is_strong_impl)


lemma precond_postcond_implementable: 
     "implementable precond postcond"
apply(auto simp: implementable_def)
apply(case_tac "\<iota>", simp_all)
done

typ "in_c"
thm SYS_is_strong_impl[simplified is_strong_impl_def,THEN spec,of "(alloc c no m)", simplified]

lemma Eps_split_eq' : "(SOME (x', y'). x'= x  \<and> y'= y) = (SOME (x', y'). x = x' \<and> y = y')"
by(rule arg_cong[of _ _ "Eps"], auto)

(* PUT must be a constant for coding conventions ... *)
consts PUT :: "in_c \<Rightarrow>  (out, '\<sigma>)MON\<^sub>S\<^sub>E"

interpretation load : efsm_det 
                      "precond" "postcond" "SYS" "(load tid addr)"
                      "\<lambda>\<sigma>. load_ok (\<sigma> $ (tid,addr))" 
                      "\<lambda> \<sigma>. \<sigma>"
                      "\<lambda> \<sigma>. (tid,addr) \<in> Domain \<sigma>"
               by unfold_locales (auto simp: SYS_def Eps_split_eq')

interpretation store : efsm_det 
                        "precond" "postcond" "SYS" "(store tid addr m)"
                        "\<lambda>_. store_ok" 
                         "\<lambda> \<sigma>. \<sigma>((tid, addr):=\<^sub>$ m)" 
                         "\<lambda> \<sigma>.(True)"
               by unfold_locales (auto simp: SYS_def Eps_split_eq')

interpretation share : efsm_det 
                       "precond" "postcond" "SYS" "(share tid addr tid' addr')" 
                       "\<lambda>_. share_ok" 
                       "\<lambda> \<sigma>. \<sigma>((tid,addr) \<Join> (tid',addr'))"
                       "\<lambda> \<sigma>. ((tid,addr) \<in> Domain \<sigma> \<and> (tid',addr') \<in> Domain \<sigma>)"
               by unfold_locales (auto simp: SYS_def Eps_split_eq')

subsubsection{* The TestGen Setup*} 

(* deep splitting on *)
typ SharedMemory_test.in_c

set_pre_safe_tac{*
  (fn ctxt => TestGen.ALLCASES(
                  TestGen.CLOSURE (
                      TestGen.case_tac_typ ctxt ["ShareMemory_test.in_c"]))) 
*}


declare Monads.mbind'_bind[simp del]

lemmas update_simps = update_share  sharing_upd update_apply update_other
                      update_cancel update_triv update_commute 

                      shares_dom Domain_transfer Domain_update

                      shares_init sharing_refl sharing_upd transfer_share  share_transfer 
                      sharing_commute

thm update_simps 

section{* An Abstract Test-Case Generation Scenario *} 

text{* Scenario with tests starting on an fixed initialized memory.
       This corresponds roughly to checking that all inductively defined
       shared memories build over store, load and transfer reveal the
       behaviour rescribed by the model. *}

fun split :: "in_c list \<Rightarrow> bool"
where "split [] = True"
     |"split (a#R) = ((\<exists> tid loc. a =  load tid loc \<and> split R) \<or>
                       (\<exists> tid loc n. a =  store  tid loc n \<and> split R) \<or>
                       (\<exists> tid loc tid' loc'. a = share tid loc tid' loc' \<and> split R))"

(*
test_spec test_status:
assumes sym_exec_spec:
       "init \<Turnstile> (s \<leftarrow> mbind\<^sub>F\<^sub>a\<^sub>i\<^sub>l\<^sub>S\<^sub>t\<^sub>o\<^sub>p S SYS; return (s = x))"
shows  "init \<Turnstile> (s \<leftarrow> mbind\<^sub>F\<^sub>a\<^sub>i\<^sub>l\<^sub>S\<^sub>t\<^sub>o\<^sub>p S PUT; return (s = x))" 
apply(insert assms) 
apply(erule rev_mp,rule_tac x=x in spec[OF allI])
*)
test_spec test_status:
       "split S \<Longrightarrow>
        init \<Turnstile> (s \<leftarrow> mbind\<^sub>F\<^sub>a\<^sub>i\<^sub>l\<^sub>S\<^sub>t\<^sub>o\<^sub>p S SYS; return (s = x)) \<Longrightarrow>
        init \<Turnstile> (s \<leftarrow> mbind\<^sub>F\<^sub>a\<^sub>i\<^sub>l\<^sub>S\<^sub>t\<^sub>o\<^sub>p S PUT; return (s = x))"
using [[no_uniformity]]
apply((erule rev_mp)+,rule_tac x=x in spec[OF allI])
apply(gen_test_cases 5 1 "PUT")
apply(tactic "ALLGOALS(TestGen.REPEAT'(ematch_tac @{context} [@{thm load.exec_mbindFStop_E},
                                                              @{thm store.exec_mbindFStop_E},
                                                              @{thm share.exec_mbindFStop_E},
                                                              @{thm valid_mbind'_mtE}
                          ]))")
txt{* Normalization *}
apply(simp_all add: update_simps)
apply(tactic "TestGen.ALLCASES(TestGen.TRY'(fn n => REPEAT_DETERM1 ( (safe_steps_tac @{context} n ))))") 
apply(simp_all add: update_simps)
txt{* Closing : Extracting PO's *}
using [[no_uniformity=false]]
apply(tactic "TestGen.ALLCASES(TestGen.uniformityI_tac @{context} [\"PUT\"])") 
mk_test_suite "SharedMemoryNB"

section{* Concrete Test Data Selection *} 

declare [[testgen_iterations=0]]
declare [[testgen_SMT2]]

(*
declare [[testgen_pon = 1]]
declare [[testgen_smt_model]]
declare [[smt_trace]]
*)

gen_test_data "SharedMemoryNB"
print_conc_tests SharedMemoryNB
thm "SharedMemoryNB.test_thm_inst"



end
