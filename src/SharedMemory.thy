chapter{* A Shared-Memory-Model*}

theory  SharedMemory
imports Main
begin 
section {*Shared Memory Model\label{SharedMemoryThy}*}
subsection{* Prerequisites *}

text{* Prerequisite: a generalization of @{thm [source] fun_upd_def}: @{thm fun_upd_def}.
       It represents updating modulo a sharing equivalence, i.e. an equivalence relation
       on parts of the domain of a memory. *}

definition fun_upd_equivp :: "('\<alpha> \<Rightarrow> '\<alpha> \<Rightarrow> bool) \<Rightarrow> ('\<alpha> \<Rightarrow> '\<beta>) \<Rightarrow> '\<alpha> \<Rightarrow> '\<beta> \<Rightarrow> ('\<alpha> \<Rightarrow> '\<beta>)"
where     "fun_upd_equivp eq f a b = (\<lambda>x. if eq x a then b else f x)"


--{*This lemma is the same as @{thm [source] Fun.fun_upd_same}: @{thm Fun.fun_upd_same}; applied  
    on our genralization @{thm fun_upd_equivp_def} of @{thm fun_upd_def}. This proof  tell
    if our function @{term "fun_upd_equivp (op =) f x y" } is equal to @{term f} this is equivalent 
    to the fact that @{term "f x = y"}*}

lemma fun_upd_equivp_iff: "((fun_upd_equivp (op =) f x y) = f) = (f  x =  y)"
  by (simp add :fun_upd_equivp_def, safe, erule subst, auto)

--{*Now we try to proof the same lemma applied on any equivalent relation @{term "equivp eqv"}
    instead of the equivalent relation @{term "op ="}. For this case, we had split the lemma to 2 
    parts. the lemma @{term "fun_upd_equivp_iff_part1"} to proof the case when 
    @{term "eq (f a) b \<longrightarrow>  eq (fun_upd_equivp eqv f a b z)  (f z) "}, and the second part is 
    the lemma @{term "fun_upd_equivp_iff_part2"} to proof the case 
    @{term "equivp eqv \<Longrightarrow> fun_upd_equivp eqv f a b = f \<longrightarrow> f a = b"}. *}

lemma fun_upd_equivp_iff_part1: 
  assumes is_equivp:  "equivp R"
  and     2: "(\<And>z. R x z \<Longrightarrow> R (f z) y) "
  shows "R (fun_upd_equivp R f x y z) (f z)"
  using assms  
  unfolding fun_upd_equivp_def  
  by (auto simp: Equiv_Relations.equivp_reflp Equiv_Relations.equivp_symp)

lemma fun_upd_equivp_iff_part2: 
  assumes is_equivp: "equivp R"
  shows "fun_upd_equivp R f x y = f \<longrightarrow> f x = y"
  using assms
  apply (simp add :fun_upd_equivp_def, safe)
  apply (erule subst, auto simp: Equiv_Relations.equivp_reflp)
done

--{*Just anotther way to formalise @{thm fun_upd_equivp_iff_part2} without using the strong equality*}

lemma 
  assumes is_equivp:"equivp R"
  and  2:  "(\<And>z. R x z \<Longrightarrow> R (fun_upd_equivp R f x y z) (f z))"
  shows    "R  y (f x)"
  using assms
  by (simp add: fun_upd_equivp_def Equiv_Relations.equivp_symp equivp_reflp)

text{*this lemma is the same  in @{thm fun_upd_equivp_iff_part1} where @{term "(op =)"} is 
      generalized by another equivalence relation*}

lemma fun_upd_equivp_idem: 
  assumes image:"f x = y" 
  shows         "(fun_upd_equivp (op =) f x y) = f"
  using assms
  by (simp only: fun_upd_equivp_iff)

lemma fun_upd_equivp_triv :
  "fun_upd_equivp (op =) f x (f x) = f "
  by (simp only: fun_upd_equivp_iff)

--{*This is the generalization of @{thm fun_upd_equivp_triv} on a given equivalence relation*}

lemma fun_upd_equivp_triv_part1 : 
  "equivp R  \<Longrightarrow>  (\<And>z. R x z \<Longrightarrow>fun_upd_equivp (R') f x (f x) z) \<Longrightarrow>  f x "
  apply (auto simp:fun_upd_equivp_def)
  apply (metis equivp_reflp)
done

lemma fun_upd_equivp_triv_part2 : 
  "equivp R  \<Longrightarrow>  (\<And>z. R x z \<Longrightarrow> f z ) \<Longrightarrow>  fun_upd_equivp (R') f x (f x) x "
  by (simp add:fun_upd_equivp_def equivp_reflp split: if_split)

lemma fun_upd_equivp_apply [simp]: 
  "(fun_upd_equivp (op =) f x y) z = (if z = x then y else f z)"
  by (simp only: fun_upd_equivp_def)

--{*This is the generalization of @{thm fun_upd_equivp_apply} with e given equivalence relation and
     not only with @{term "op ="}*}

lemma fun_upd_equivp_apply1 [simp]: 
  "equivp R \<Longrightarrow>(fun_upd_equivp R f x y) z = (if R z x then y else f z)"
  by (simp add: fun_upd_equivp_def)

lemma fun_upd_equivp_same: 
  "(fun_upd_equivp (op =) f x y) x = y"
  by (simp only: fun_upd_equivp_def)simp

--{*This is the generalization of @{thm fun_upd_equivp_same} with a given equivalence relation*}

lemma  fun_upd_equivp_same1: 
  assumes is_equivp:"equivp R"
  shows   "(fun_upd_equivp R f x y) x = y"
  using assms
  by (simp add: fun_upd_equivp_def equivp_reflp)


text{* For the special case that {@term eq} is just the equality {@term "op ="}, sharing 
update and classical update are identical.*}

lemma fun_upd_equivp_vs_fun_upd: "(fun_upd_equivp (op =)) = fun_upd"
  by(rule ext, rule ext, rule ext,simp add:fun_upd_def fun_upd_equivp_def)



subsection{* Definition of the shared-memory type*}

typedef ('\<alpha>, '\<beta>) memory = "{(\<sigma>::'\<alpha> \<rightharpoonup>'\<beta>, R). equivp R \<and> (\<forall>x y. R x y \<longrightarrow> \<sigma> x = \<sigma> y)}"
proof
  show "(Map.empty, (op =)) \<in> ?memory"
    by (auto simp: identity_equivp)
qed

fun memory_inv :: "('\<alpha> \<Rightarrow> '\<beta> option) \<times> ('\<alpha> \<Rightarrow> '\<alpha> \<Rightarrow> bool) \<Rightarrow> bool"
where     "memory_inv (Pair f R) = (equivp R \<and> (\<forall>x y. R x y \<longrightarrow> f x = f y))"



lemma Abs_Rep_memory [simp]:
  "Abs_memory (Rep_memory \<sigma>) = \<sigma>"
  by (simp add:Rep_memory_inverse)

lemma memory_invariant [simp]:
     "memory_inv \<sigma>_rep = (Rep_memory (Abs_memory \<sigma>_rep) = \<sigma>_rep)"
  using Rep_memory [of "Abs_memory \<sigma>_rep"] Abs_memory_inverse mem_Collect_eq
        case_prodE case_prodI2 memory_inv.simps
  by smt 

lemma Pair_code_eq :
 "Rep_memory \<sigma>  = Pair (fst (Rep_memory \<sigma>)) (snd (Rep_memory \<sigma>))"
  by (simp add: Product_Type.surjective_pairing)

lemma snd_memory_equivp [simp]: "equivp(snd(Rep_memory \<sigma>))"
  by(insert Rep_memory[of \<sigma>], auto)

subsection{* Operations on Shared-Memory *}

setup_lifting type_definition_memory (*Mandatory for lift_definition*)

abbreviation mem_init :: "('a \<Rightarrow> 'b option) \<times> ('a \<Rightarrow> 'a \<Rightarrow> bool)"
where
  "mem_init \<equiv> (Map.empty, (op =))"

lemma memory_init_eq_sound: 
     "mem_init \<in> {(\<sigma>, R). equivp R \<and> (\<forall>x y. R x y \<longrightarrow> \<sigma> x = \<sigma> y)}"
proof -
  obtain mem and R 
    where Pair: "(mem, R) =mem_init " and Eq: "equivp R" 
      using  identity_equivp by auto 
  have D1: "R = (op =)"
  and  D2: "mem = Map.empty "  
    using Pair prod.inject
    by auto
  moreover have inv_part2: "\<forall> x y . R x y \<longrightarrow> mem x = mem y"
            unfolding D1 D2 by auto   
  ultimately show ?thesis  
    using  Eq  Abs_memory_cases Pair_inject Rep_memory_cases Rep_memory_inverse 
           identity_equivp memory_inv.elims(3) memory_invariant 
    by auto
qed

lift_definition init :: "('\<alpha>, '\<beta>) memory"
  is "mem_init :: ('\<alpha> \<Rightarrow> '\<beta> option) \<times> ('\<alpha> \<Rightarrow> '\<alpha> \<Rightarrow> bool)"
  using memory_init_eq_sound by simp

(*code generation test*)
value "init::(nat,int)memory"
value "map (\<lambda>x. the (fst (Rep_memory init)x)) [1 .. 10]"
value "take (10) (map (Pair Map.empty) [(op =) ])"
value "replicate  10 init"
term  "Rep_memory \<sigma>"
term "[(\<sigma>::nat \<rightharpoonup> int, R )<-xs . equivp R \<and> (\<forall>x y. R x y \<longrightarrow> \<sigma> x = \<sigma> y)]"

(* deprecated >>>> *)
definition init_mem_list :: "'\<alpha> list \<Rightarrow> (nat, '\<alpha>) memory"
where     "init_mem_list s = Abs_memory (let h = zip (map nat [0 .. int(length s)]) s
                                         in foldl (\<lambda>x (y,z). fun_upd x y (Some z)) 
                                            Map.empty h, 
                                         op =)"

(* <<<<<<<<<<<<<<<< *)


subsubsection{* Memory Read Operation*}

definition lookup :: "('\<alpha>, '\<beta>) memory \<Rightarrow> '\<alpha> \<Rightarrow> '\<beta>" (infixl "$" 100)
where      "\<sigma> $ x = the (fst (Rep_memory \<sigma>) x)"

subsubsection{* Memory Update Operation*}

fun Pair_upd_lifter:: "('\<alpha> \<Rightarrow> '\<beta> option) \<times> ('\<alpha> \<Rightarrow> '\<alpha> \<Rightarrow> bool) \<Rightarrow> '\<alpha> \<Rightarrow> '\<beta> \<Rightarrow> 
                       ('\<alpha> \<Rightarrow> '\<beta> option) \<times> ('\<alpha> \<Rightarrow> '\<alpha> \<Rightarrow> bool)" 
  where   "Pair_upd_lifter ((f, R)) x y = (fun_upd_equivp R f x (Some y), R)"

lemma update\<^sub>_sound': 
  assumes "\<sigma> \<in> {(\<sigma>, R). equivp R \<and> (\<forall>x y. R x y \<longrightarrow> \<sigma> x = \<sigma> y)}"
  shows   "Pair_upd_lifter \<sigma> x y \<in> {(\<sigma>, R). equivp R \<and> (\<forall>x y. R x y \<longrightarrow> \<sigma> x = \<sigma> y)}"
proof -
  obtain mem and R 
    where Pair: "(mem, R) = \<sigma>" and Eq: "equivp R" and Mem: "\<forall> x y . R x y \<longrightarrow> mem x = mem y"
      using assms equivpE by auto
  obtain mem' and R'
    where Pair': "(mem', R') = Pair_upd_lifter \<sigma> x y"
      using surjective_pairing by metis
  have Def1: "mem' = fun_upd_equivp R mem x (Some y)"
  and  Def2: "R' = R"
    using Pair Pair' by auto
  have Eq': "equivp R'"
    using  Def2 Eq by auto
  moreover have "\<forall> y z . R' y z \<longrightarrow> mem' y = mem' z"
    using Mem equivp_symp equivp_transp 
      unfolding Def1 Def2 by (metis Eq fun_upd_equivp_def)
  ultimately show ?thesis
    using Pair' by auto
qed

lemma memory_inv_update_rep: 
  "memory_inv (Pair_upd_lifter (Rep_memory \<sigma>) x y)"
proof -
  have *:"(equivp o snd) (Pair_upd_lifter (Rep_memory \<sigma>) x y)"
  and **:"(\<forall>w z. snd (Pair_upd_lifter (Rep_memory \<sigma>) x y) w z  \<longrightarrow> 
                 fst (Pair_upd_lifter (Rep_memory \<sigma>) x y) w = 
                 fst (Pair_upd_lifter (Rep_memory \<sigma>) x y) z)"
    using update\<^sub>_sound'[OF Rep_memory,of \<sigma> x y]
    by auto
  have ***:"memory_inv (Pair_upd_lifter (Rep_memory \<sigma>) x y) =
            memory_inv (fst (Pair_upd_lifter (Rep_memory \<sigma>) x y),
                        snd (Pair_upd_lifter (Rep_memory \<sigma>) x y))"
   using surjective_pairing[of "(Pair_upd_lifter (Rep_memory \<sigma>) x y)"]
   by simp
  show ?thesis
   apply (simp only: * ** *** memory_inv.simps)
   using * **
   apply simp
   done
qed

lift_definition update :: " ('\<alpha>, '\<beta>) memory \<Rightarrow>'\<alpha> \<Rightarrow> '\<beta> \<Rightarrow>  ('\<alpha>, '\<beta>) memory" ("_ '(_ :=\<^sub>$ _')" 100)
  is Pair_upd_lifter
  using update\<^sub>_sound'
  by simp

lemma update': "\<sigma> (x :=\<^sub>$ y) = Abs_memory (fun_upd_equivp (snd (Rep_memory \<sigma>)) 
                                         (fst (Rep_memory \<sigma>)) x (Some y), (snd (Rep_memory \<sigma>)))"
  using Rep_memory_inverse surjective_pairing Pair_upd_lifter.simps  update.rep_eq
  by metis

(*update on list*)

fun    update_list_rep :: "('\<alpha> \<rightharpoonup> '\<beta>) \<times> ('\<alpha> \<Rightarrow> '\<alpha> \<Rightarrow> bool) \<Rightarrow> ('\<alpha> \<times> '\<beta> )list \<Rightarrow> 
                           ('\<alpha> \<rightharpoonup> '\<beta>) \<times> ('\<alpha> \<Rightarrow> '\<alpha> \<Rightarrow> bool)"
where  "update_list_rep (f, R) nlist = 
        (foldl (\<lambda>(f, R)(addr,val). 
         Pair_upd_lifter (f, R) addr val) (f, R) nlist)"

lemma update_list_rep_p:
  assumes 1: "P \<sigma>"
  and     2: "\<And>src dst \<sigma>. P \<sigma> \<Longrightarrow> P (Pair_upd_lifter \<sigma> src dst)"
  shows  "P (update_list_rep  \<sigma> list)"
  using 1 2
  apply (induct "list" arbitrary: \<sigma>)
  apply (force,safe) 
  apply (simp del: Pair_upd_lifter.simps)
  using surjective_pairing
  apply simp
done 

lemma update_list_rep_sound:
  assumes 1: "\<sigma> \<in> {(\<sigma>, R). equivp R \<and> (\<forall>x y. R x y \<longrightarrow> \<sigma> x = \<sigma> y)}"
  shows      "update_list_rep  \<sigma> (nlist) \<in> {(\<sigma>, R). equivp R \<and> (\<forall>x y. R x y \<longrightarrow> \<sigma> x = \<sigma> y)}"
  using  1 
  apply (elim update_list_rep_p)
  apply (erule  update\<^sub>_sound')
done

lift_definition update_list :: "('\<alpha>, '\<beta>) memory \<Rightarrow> ('\<alpha> \<times> '\<beta> )list \<Rightarrow> ('\<alpha>, '\<beta>) memory" (infixl "'/:=\<^sub>$" 30)
  is update_list_rep
  using update_list_rep_sound by simp

lemma update_list_Nil[simp]: "(\<sigma> /:=\<^sub>$ []) = \<sigma>"
  unfolding update_list_def
  by(simp,subst surjective_pairing[of "Rep_memory \<sigma>"],
     subst update_list_rep.simps, simp)

lemma update_list_Cons[simp] : "(\<sigma> /:=\<^sub>$ ((a,b)#S)) = (\<sigma>(a :=\<^sub>$ b) /:=\<^sub>$ S)"
  unfolding update_list_def
  apply(simp,subst surjective_pairing[of "Rep_memory \<sigma>"],
        subst update_list_rep.simps, simp)
  apply(subst surjective_pairing[of "Rep_memory (\<sigma> (a :=\<^sub>$ b))"],
        subst update_list_rep.simps, simp)
  apply(simp add: update_def)
  apply(subst Abs_memory_inverse)
  apply (metis (lifting, mono_tags) Rep_memory update\<^sub>_sound')
  apply simp
done
  
text{* Type-invariant: *}  
                        
lemma update\<^sub>_sound: 
  assumes "Rep_memory \<sigma> = (\<sigma>', eq)"
  shows   "(fun_upd_equivp eq \<sigma>' x (Some y), eq) \<in> 
           {(\<sigma>, R). equivp R \<and> (\<forall>x y. R x y \<longrightarrow> \<sigma> x = \<sigma> y)}"
  using assms  insert Rep_memory[of "\<sigma>"]
  apply(auto simp:  fun_upd_equivp_def)
  apply(rename_tac "xa" "xb", erule contrapos_np)
  apply(rule_tac R=eq and y=xa in equivp_transp,simp)
  apply(erule equivp_symp, simp_all)
  apply(rename_tac "xa" "xb", erule contrapos_np)
  apply(rule_tac R=eq and y=xb in equivp_transp,simp_all)
done

subsubsection{* Memory Transfer Based on Sharing Transformation*}

(*ref: def by Oto Havle *)

fun    transfer_rep :: "('\<alpha> \<rightharpoonup> '\<beta>) \<times> ('\<alpha>\<Rightarrow>'\<alpha> \<Rightarrow> bool) \<Rightarrow> '\<alpha> \<Rightarrow> '\<alpha> \<Rightarrow> ('\<alpha>\<rightharpoonup>'\<beta>) \<times> ('\<alpha>\<Rightarrow>'\<alpha> \<Rightarrow> bool)"
where "transfer_rep  (m, r) src dst = 
       (m o (id (dst := src)), 
        (\<lambda> x y . r ((id (dst := src)) x) ((id (dst := src)) y)))"

lemma  transfer_rep_simp : 
      "transfer_rep X src dst = 
       ((fst X) o (id (dst := src)), 
        (\<lambda> x y . (snd X) ((id (dst := src)) x) ((id (dst := src)) y)))"
  by(subst surjective_pairing[of "X"], 
     subst transfer_rep.simps, simp)

(*ref: proof by Oto Havle *)

lemma transfer_rep_sound:
  assumes "\<sigma> \<in> {(\<sigma>, R). equivp R \<and> (\<forall>x y. R x y \<longrightarrow> \<sigma> x = \<sigma> y)}"
  shows   "transfer_rep  \<sigma> src dst \<in> {(\<sigma>, R). equivp R \<and> (\<forall>x y. R x y \<longrightarrow> \<sigma> x = \<sigma> y)}"
proof -
  obtain mem and R
    where P: "(mem, R) = \<sigma>" and E: "equivp R" and M: "\<forall> x y . R x y \<longrightarrow> mem x = mem y"
      using assms equivpE by auto
  obtain mem' and R'
    where P': "(mem', R') = transfer_rep \<sigma> src  dst"
      by (metis surj_pair)
  have D1: "mem' = (mem o (id (dst := src)))"
   and D2: "R' = (\<lambda> x y . R ((id (dst := src)) x) ((id (dst := src)) y))"
    using P P' by auto
  have "equivp R'"
    using E unfolding D2  equivp_def by metis
  moreover have "\<forall> y z . R' y z \<longrightarrow> mem' y = mem' z"
    using M unfolding D1 D2 by auto
  ultimately show ?thesis
    using P' by auto
qed

lift_definition 
  transfer :: "('\<alpha>,'\<beta>)memory \<Rightarrow> '\<alpha> \<Rightarrow> '\<alpha>  \<Rightarrow> ('\<alpha>, '\<beta>)memory" ("_ '(_ \<Join> _')" [0,111,111]110)
  is transfer_rep
  using transfer_rep_sound
  by simp

lemma transfer_rep_sound2 :
     "transfer_rep (Rep_memory \<sigma>) a b \<in> 
       {(\<sigma>, R). equivp R \<and> (\<forall>x y. R x y \<longrightarrow> \<sigma> x = \<sigma> y)}"
      by (metis (lifting, mono_tags) Rep_memory transfer_rep_sound)
  
(* the following share_list construction is pretty indirect and motivated by code-generation
   principles; why not a  definition which is more direct ? e.g. :*)

fun   share_list2 :: "('\<alpha>, '\<beta>) memory \<Rightarrow> ('\<alpha> \<times> '\<alpha> )list \<Rightarrow> ('\<alpha>, '\<beta>) memory" (infix "'/\<Join>" 60)
where "\<sigma> /\<Join> S = (foldl (\<lambda> \<sigma> (a,b). (\<sigma> (a\<Join>b))) \<sigma> S)" 

lemma sharelist2_Nil[simp] : "\<sigma> /\<Join> [] = \<sigma>"  by simp

lemma sharelist2_Cons[simp] : "\<sigma> /\<Join> ((a,b)#S) = (\<sigma>(a\<Join>b) /\<Join> S)"  by simp

(* deprecated ??? >>> *)

fun     share_list_rep :: "('\<alpha> \<rightharpoonup> '\<beta>) \<times> ('\<alpha> \<Rightarrow> '\<alpha> \<Rightarrow> bool) \<Rightarrow> ('\<alpha> \<times> '\<alpha> )list \<Rightarrow> 
                           ('\<alpha> \<rightharpoonup> '\<beta>) \<times> ('\<alpha> \<Rightarrow> '\<alpha> \<Rightarrow> bool)"
where  "share_list_rep (f, R) nlist = 
                           (foldl (\<lambda>(f, R) (src,dst). transfer_rep (f, R) src dst) (f, R) nlist)"

fun     share_list_rep' :: "('\<alpha> \<rightharpoonup> '\<beta>) \<times> ('\<alpha> \<Rightarrow> '\<alpha> \<Rightarrow> bool) \<Rightarrow> ('\<alpha> \<times> '\<alpha>)list \<Rightarrow> 
                            ('\<alpha> \<rightharpoonup> '\<beta>) \<times> ('\<alpha> \<Rightarrow> '\<alpha> \<Rightarrow> bool)"
where  "share_list_rep' (f, R) [] = (f, R)"
     | "share_list_rep' (f, R) (n#nlist) = share_list_rep' (transfer_rep(f,R)(fst n)(snd n)) nlist"

lemma share_list_rep'_p:
  assumes 1: "P \<sigma>"
  and     2: " \<And>src dst \<sigma>. P \<sigma> \<Longrightarrow> P (transfer_rep \<sigma> src dst)"
  shows  "P (share_list_rep'  \<sigma> list)"
  using 1 2
  apply (induct "list" arbitrary: \<sigma> P)
  apply force 
  apply safe
  apply (simp del: transfer_rep.simps)
  using surjective_pairing
  apply metis
done 

lemma foldl_preserve_p:
  assumes 1: "P mem"
  and     2: "\<And>y z mem . P mem \<Longrightarrow> P (f mem y z)"
  shows  "P (foldl (\<lambda>a (y, z). f mem y z) mem list)"
  using 1 2
  apply (induct "list" arbitrary: f mem , auto)
  apply metis
done 

lemma share_list_rep_p:
  assumes 1: "P \<sigma>"
  and     2: "\<And>src dst \<sigma>. P \<sigma> \<Longrightarrow> P (transfer_rep \<sigma> src dst)"
  shows  "P (share_list_rep  \<sigma> list)"
  using 1 2
  apply (induct "list" arbitrary: \<sigma>)
  apply force 
  apply safe
  apply (simp del: transfer_rep.simps)
  using surjective_pairing
  apply metis
done 

text{* The modification of the underlying equivalence relation on adresses is only defined
       on very strong conditions --- which are fulfilled for the empty memory, but difficult to
       establish on a non-empty-one. And of course, the given relation must be proven to
       be an equivalence relation. So, the case is geared towards shared-memory scenarios
       where the sharing is defined initially once and for all. *}

definition update\<^sub>R :: "('\<alpha>, '\<beta>)memory \<Rightarrow> ('\<alpha> \<Rightarrow> '\<alpha> \<Rightarrow> bool) \<Rightarrow> ('\<alpha>, '\<beta>)memory" ("_ :=\<^sub>R _" 100)
where     "\<sigma> :=\<^sub>R R \<equiv> Abs_memory (fst(Rep_memory \<sigma>), R)"

definition lookup\<^sub>R :: "('\<alpha>, '\<beta>)memory \<Rightarrow> ('\<alpha> \<Rightarrow> '\<alpha> \<Rightarrow> bool)" ("$\<^sub>R _" 100)
where     "$\<^sub>R \<sigma> \<equiv> (snd(Rep_memory \<sigma>))"

lemma   update\<^sub>R_comp_lookup\<^sub>R: 
assumes equiv           : "equivp R"
    and sharing_conform : " \<forall> x y. R x y \<longrightarrow> fst(Rep_memory \<sigma>) x = fst(Rep_memory \<sigma>) y"
shows  "($\<^sub>R (\<sigma> :=\<^sub>R R)) = R"
unfolding lookup\<^sub>R_def update\<^sub>R_def
by(subst Abs_memory_inverse, simp_all add: equiv sharing_conform)

subsection{* Sharing Relation Definition*}

definition sharing :: "'\<alpha> \<Rightarrow> ('\<alpha>, '\<beta>)memory \<Rightarrow> '\<alpha> \<Rightarrow> bool" 
                      ("(_ shares()\<^bsub>_\<^esub>/ _)" [201, 0, 201] 200)
where     "(x shares\<^bsub>\<sigma>\<^esub> y) \<equiv> (snd(Rep_memory \<sigma>) x y)"                          

definition Sharing :: "'\<alpha> set \<Rightarrow> ('\<alpha>, '\<beta>)memory \<Rightarrow> '\<alpha> set \<Rightarrow> bool" 
                        ("(_ Shares()\<^bsub>_\<^esub>/ _)" [201, 0, 201] 200)
where     "(X Shares\<^bsub>\<sigma>\<^esub> Y) \<equiv> (\<exists> x\<in>X. \<exists> y\<in>Y. x shares\<^bsub>\<sigma>\<^esub> y)"

subsection{* Properties on Sharing Relation*}

lemma sharing_charn: 
  "equivp (snd (Rep_memory \<sigma>))"
  by auto

lemma sharing_charn':
  assumes 1:  "(x shares\<^bsub>\<sigma>\<^esub> y)"
  shows" (\<exists>R. equivp R \<and> R x y)"
  by (auto simp add: snd_def equivp_def)

lemma sharing_charn2:
  shows"\<exists>x y. (equivp (snd (Rep_memory \<sigma>)) \<and> (snd (Rep_memory \<sigma>)) x y) "
  using  sharing_charn [THEN equivp_reflp ]
  by (simp)fast

--{*Lemma to show that @{thm sharing_def} is reflexive*}
lemma sharing_refl: "(x shares\<^bsub>\<sigma>\<^esub> x)"
  using insert Rep_memory[of "\<sigma>"] 
  by (auto simp: sharing_def elim: equivp_reflp)

--{*Lemma to show that @{thm sharing_def} is symetric*}
lemma sharing_sym [sym]:
   assumes 1: "x shares\<^bsub>\<sigma>\<^esub> y"
   shows   "y shares\<^bsub>\<sigma>\<^esub> x"
   using 1 Rep_memory[of "\<sigma>"] 
   by (auto simp: sharing_def elim: equivp_symp)
   
lemma sharing_commute : "x shares\<^bsub>\<sigma>\<^esub> y = (y shares\<^bsub>\<sigma>\<^esub> x)" 
  by(auto intro: sharing_sym)
 
--{*Lemma to show that @{thm sharing_def} is transitive*}

lemma sharing_trans [trans]:
   assumes 1: "x shares\<^bsub>\<sigma>\<^esub> y"
   and     2: "y shares\<^bsub>\<sigma>\<^esub> z"
   shows   "x shares\<^bsub>\<sigma>\<^esub> z"
   using assms insert Rep_memory[of "\<sigma>"]
   by(auto simp: sharing_def elim: equivp_transp)

lemma shares_result: 
  assumes 1: "x shares\<^bsub>\<sigma>\<^esub> y"
  shows   "fst (Rep_memory \<sigma>) x = fst (Rep_memory \<sigma>) y"
  using 1
  unfolding sharing_def 
  using Rep_memory[of "\<sigma>"] 
  by auto
   
lemma  sharing_init:
  assumes 1: "i \<noteq> k"
  shows  "\<not>(i shares\<^bsub>init\<^esub> k)"
  unfolding sharing_def init_def
  using 1 
  by (auto simp: Abs_memory_inverse identity_equivp)

lemma shares_init[simp]:  "(x shares\<^bsub>init\<^esub> y) = (x=y)"
  unfolding sharing_def init_def
  by (metis init_def sharing_init sharing_def sharing_refl)

lemma  sharing_init_mem_list:
  assumes 1: "i \<noteq> k"
  shows  "\<not>(i shares\<^bsub>init_mem_list S\<^esub> k)"
  unfolding sharing_def init_mem_list_def
  using 1 
  by (auto simp: Abs_memory_inverse identity_equivp)

(* experimental: a simultaneous update to None for all elements in X and their equivalents. *)                          
definition reset :: "('\<alpha>, '\<beta>) memory \<Rightarrow> '\<alpha> set\<Rightarrow> ('\<alpha>, '\<beta>)memory" ("_ '(reset _')" 100)
where     "\<sigma> (reset X) = (let (\<sigma>',eq) = Rep_memory \<sigma>;
                              eq' = \<lambda> a b. eq a b \<or> (\<exists>x\<in>X. eq a x \<or> eq b x) 
                          in  if X={} then \<sigma>
                              else Abs_memory (fun_upd_equivp eq' \<sigma>' (SOME x. x\<in>X) None, eq))"                          
                            
lemma reset_mt : "\<sigma> (reset {}) =  \<sigma>"
  unfolding reset_def Let_def
  by simp 

lemma reset_sh :
assumes * : "(x shares\<^bsub>\<sigma>\<^esub> y)"
 and    **: "x \<in> X"
shows       "\<sigma> (reset X) $ y = None"
oops

subsection{* Memory Domain Definition*}

definition Domain :: "('\<alpha>, '\<beta>)memory \<Rightarrow> '\<alpha> set"
where     "Domain \<sigma> = dom (fst (Rep_memory \<sigma>))"

subsection{* Properties on Memory Domain*}

lemma Domain_charn:
  assumes 1:"x \<in> Domain \<sigma>"
  shows "\<exists> y. Some y = fst (Rep_memory \<sigma>) x"
  using 1
  by(auto simp: Domain_def)

lemma Domain_charn1:
  assumes 1:"x \<in> Domain \<sigma>"
  shows "\<exists> y. the (Some y) =  \<sigma> $ x"
  using 1
  by(auto simp: Domain_def lookup_def)

--{*This lemma says that if @{term "x"} and @{term "y"} are quivalent this 
    means that they are in the same set of equivalent classes*}

lemma shares_dom [code_unfold, intro]: 
  assumes 1:"x shares\<^bsub>\<sigma>\<^esub> y"
  shows   "(x \<in> Domain \<sigma>) = (y \<in> Domain \<sigma>)"
  using insert Rep_memory[of "\<sigma>"] 1
  by (auto simp: sharing_def Domain_def)

lemma Domain_mono: 
  assumes 1: "x \<in>  Domain \<sigma>"
  and     2: "(x shares\<^bsub>\<sigma>\<^esub> y)"
  shows      "y \<in> Domain \<sigma>"
  using 1 2 Rep_memory[of "\<sigma>"]
  by (auto simp add: sharing_def Domain_def )

corollary  Domain_nonshares : 
  assumes 1: "x \<in>  Domain \<sigma>"
  and     2: "y \<notin> Domain \<sigma> "
  shows      "\<not>(x shares\<^bsub>\<sigma>\<^esub> y)"
  using 1 2 Domain_mono
  by fast

lemma Domain_init[simp] : "Domain init = {}" 
  unfolding init_def Domain_def
  by(simp_all add:identity_equivp Abs_memory_inverse)

lemma Domain_update[simp] :"Domain (\<sigma> (x :=\<^sub>$ y)) =  (Domain \<sigma>) \<union> {y . y shares\<^bsub>\<sigma>\<^esub> x}"
unfolding update_def Domain_def sharing_def
proof (simp_all)
   have *  : "Pair_upd_lifter (Rep_memory \<sigma>) x y \<in> {(\<sigma>, R). equivp R \<and> (\<forall>x y. R x y \<longrightarrow> \<sigma> x = \<sigma> y)}"
             by (simp, metis (lifting, mono_tags) Rep_memory mem_Collect_eq update\<^sub>_sound')
   have ** : "snd (Rep_memory \<sigma>) x x"
             by(metis equivp_reflp sharing_charn2)
   show "dom (fst (Rep_memory (Abs_memory (Pair_upd_lifter (Rep_memory \<sigma>) x y)))) = 
         dom (fst (Rep_memory \<sigma>)) \<union> {y. snd (Rep_memory \<sigma>) y x}"
         apply(simp_all add: Abs_memory_inverse[OF *] )
         apply(subst surjective_pairing [of "(Rep_memory \<sigma>)"])
         apply(subst Pair_upd_lifter.simps, simp)
         apply(auto simp: ** fun_upd_equivp_def)
         done
qed

lemma Domain_share1: 
assumes 1 : "a \<in> Domain \<sigma>"
  and   2 : "b \<in> Domain \<sigma>"
shows     "Domain (\<sigma>(a\<Join>b)) = Domain \<sigma>"
proof(simp_all add:Set.set_eq_iff, rule allI)
   fix x
 have ***: "transfer_rep (Rep_memory \<sigma>) (id a) (id b) \<in> 
            {(\<sigma>, R). equivp R \<and> (\<forall>x y. R x y \<longrightarrow> \<sigma> x = \<sigma> y)}"
           by (metis (lifting, mono_tags) Rep_memory transfer_rep_sound)
   show "(x \<in> Domain (\<sigma> (a \<Join> b))) = (x \<in> Domain \<sigma>)"
        unfolding sharing_def Domain_def transfer_def map_fun_def o_def
         apply(subst Abs_memory_inverse[OF ***])
         apply(insert 1 2, simp add: o_def transfer_rep_simp Domain_def )
         apply(auto split: if_split if_split_asm )
         done
qed

lemma Domain_share_tgt : 
  assumes 1:"a \<in> Domain \<sigma>"
  shows    " b \<in> Domain (\<sigma> (a \<Join> b))"
    using 1
    unfolding sharing_def Domain_def transfer_def map_fun_def o_def id_def 
    apply(subst Abs_memory_inverse[OF transfer_rep_sound2])
    unfolding sharing_def Domain_def transfer_def map_fun_def o_def id_def 
    apply(simp add: o_def transfer_rep_simp Domain_def )
    apply(auto split: if_split)
    done
  
lemma Domain_share2 : 
assumes 1 : "a \<in> Domain \<sigma>"
  and   2 : "b \<notin> Domain \<sigma>"
shows     "Domain (\<sigma>(a\<Join>b)) = (Domain \<sigma> - {x. x shares\<^bsub>\<sigma>\<^esub> b} \<union> {b})"
proof(simp_all add:Set.set_eq_iff, auto) 
   fix x
   assume 3 : "x \<in> SharedMemory.Domain (\<sigma> (a \<Join> b))"
      and 4 : "x \<noteq> b"
   show "x \<in> SharedMemory.Domain \<sigma>"
         apply(insert 3 4)
         unfolding sharing_def Domain_def transfer_def map_fun_def o_def id_def 
         apply(subst (asm) Abs_memory_inverse[OF transfer_rep_sound2])
         apply(insert 1 , simp add: o_def transfer_rep_simp Domain_def )
         apply(auto split: if_split if_split_asm )
         done
next
    fix x  
    assume 3 : "x \<in> Domain (\<sigma> (a \<Join> b))"
      and  4 : "x \<noteq> b"
      and  5 : "x shares\<^bsub>\<sigma>\<^esub> b"
      have ** : "x \<notin> Domain \<sigma>"  using "2" "5" Domain_mono by (fast )
    show "False" 
         apply(insert 3 4 5, erule contrapos_pp, simp)
         unfolding sharing_def Domain_def transfer_def map_fun_def o_def id_def 
         apply(subst Abs_memory_inverse[OF transfer_rep_sound2])
         apply(insert 1 , simp add: o_def transfer_rep_simp Domain_def )
         apply(auto split: if_split if_split_asm )
         using "**" SharedMemory.Domain_def domI apply fast
         done
next
    show "b \<in> Domain (\<sigma> (a \<Join> b))"
         using 1 Domain_share_tgt  by fast
next
    fix x
     assume 3 : "x \<in> Domain \<sigma>"
        and 4 : "\<not> x shares\<^bsub>\<sigma>\<^esub> b "
     show       " x \<in> Domain (\<sigma> (a \<Join> b))"
         unfolding sharing_def Domain_def transfer_def map_fun_def o_def id_def 
         apply(subst Abs_memory_inverse[OF transfer_rep_sound2])
         apply(insert 1 , simp add: o_def transfer_rep_simp Domain_def )
         apply(auto split: if_split if_split_asm )
         using "3" SharedMemory.Domain_def domD
         apply fast 
         done
qed

lemma Domain_share3: 
assumes 1 : "a \<notin>  Domain \<sigma>"
shows     "Domain (\<sigma>(a\<Join>b)) = (Domain \<sigma> - {b}) "
proof(simp_all add:Set.set_eq_iff, auto) 
  fix x
  assume 3: "x \<in> Domain (\<sigma> (a \<Join> b))"
  show      "x \<in> Domain \<sigma>"
     apply(insert 3)
     unfolding sharing_def Domain_def transfer_def map_fun_def o_def id_def 
     apply(subst (asm) Abs_memory_inverse[OF transfer_rep_sound2])
     apply(insert 1 , simp add: o_def transfer_rep_simp Domain_def )
     apply(auto split: if_split if_split_asm )
     done
next
  assume 3: "b \<in> Domain (\<sigma> (a \<Join> b))"
  show False
     apply(insert 1  3) 
     apply(erule contrapos_pp[of "b \<in> SharedMemory.Domain (\<sigma> (a \<Join> b))"], simp)
     unfolding sharing_def Domain_def transfer_def map_fun_def o_def id_def 
     apply(subst Abs_memory_inverse[OF transfer_rep_sound2])
     apply(insert 1 , simp add: o_def transfer_rep_simp Domain_def )
     apply(auto split: if_split  )
     done
next 
  fix x
  assume 3: "x \<in> Domain \<sigma> "
  and    4: "x \<noteq> b"
  show      "x \<in> Domain (\<sigma> (a \<Join> b))"
     apply(insert 3 4)
     unfolding sharing_def Domain_def transfer_def map_fun_def o_def id_def 
     apply(subst  Abs_memory_inverse[OF transfer_rep_sound2])
     apply(insert 1 , simp add: o_def transfer_rep_simp Domain_def )
     apply(auto split: if_split if_split_asm )
     done
qed

lemma Domain_transfer : 
"Domain (\<sigma>(a\<Join>b)) = (if a \<notin> Domain \<sigma> 
                    then (Domain \<sigma> - {b})
                    else if b \<notin> Domain \<sigma> 
                         then  (Domain \<sigma> - {x. x shares\<^bsub>\<sigma>\<^esub> b} \<union> {b})
                         else   Domain \<sigma> )"
  using Domain_share1 Domain_share2 Domain_share3 
  by metis

lemma Domain_transfer_approx: 
      "Domain (\<sigma>(a\<Join>b)) \<subseteq> Domain (\<sigma>) \<union> {b}"
  by(auto simp: Domain_transfer)

lemma Domain_update1:    
      "add \<in> Domain (\<sigma>(add :=\<^sub>$ val))"
  by (simp add: sharing_refl)

subsection{* Sharing Relation and Memory Update*}

lemma sharing_upd: "x shares\<^bsub>(\<sigma>(a :=\<^sub>$ b))\<^esub> y = x shares\<^bsub>\<sigma>\<^esub> y"
  using insert Rep_memory[of "\<sigma>"] 
  by(auto simp: sharing_def update_def Abs_memory_inverse[OF update\<^sub>_sound])

--{*this lemma says that if we do an update on an adress @{term "x"}  all the elements that are 
     equivalent of @{term "x"} are updated*}


lemma update'': 
      "\<sigma> (x :=\<^sub>$ y) = Abs_memory(fun_upd_equivp (\<lambda>x y. x shares\<^bsub>\<sigma>\<^esub> y) (fst (Rep_memory \<sigma>)) x (Some y), 
                                snd (Rep_memory \<sigma>))"
   unfolding update_def sharing_def
   by (metis update' update_def)

theorem update_cancel: 
assumes "x shares\<^bsub>\<sigma>\<^esub> x'"
shows   "\<sigma>(x :=\<^sub>$ y)(x' :=\<^sub>$ z) = (\<sigma>(x' :=\<^sub>$ z))"     
   proof - 
      have * : "(fun_upd_equivp(snd(Rep_memory \<sigma>))(fst(Rep_memory \<sigma>)) x (Some y),snd (Rep_memory \<sigma>))
                  \<in> {(\<sigma>, R). equivp R \<and> (\<forall>x y. R x y \<longrightarrow> \<sigma> x = \<sigma> y)}" 
               unfolding fun_upd_equivp_def
               by(rule update\<^sub>_sound[simplified fun_upd_equivp_def], simp)
      have ** : "\<And> R \<sigma>. equivp R \<Longrightarrow> R x x' \<Longrightarrow>
                         fun_upd_equivp R (fun_upd_equivp R \<sigma> x (Some y)) x' (Some z)
                         = fun_upd_equivp R \<sigma> x' (Some z)"
               unfolding fun_upd_equivp_def
               apply(rule ext)
               apply(case_tac "R xa x'", auto)
               apply(erule contrapos_np, erule equivp_transp, simp_all)
               done
      show ?thesis 
      apply(simp add: update')
      apply(insert sharing_charn assms[simplified sharing_def])
      apply(simp add: Abs_memory_inverse [OF *] **)
      done
qed   
 
theorem update_commute: 
   assumes 1:"\<not> (x shares\<^bsub>\<sigma>\<^esub> x')"
   shows     "(\<sigma>(x :=\<^sub>$ y))(x' :=\<^sub>$ z) = (\<sigma>(x':=\<^sub>$ z)(x :=\<^sub>$ y))" 
      proof - 
      have * : "\<And> x y.(fun_upd_equivp(snd(Rep_memory \<sigma>))(fst(Rep_memory \<sigma>)) x (Some y),snd (Rep_memory \<sigma>))
                       \<in> {(\<sigma>, R). equivp R \<and> (\<forall>x y. R x y \<longrightarrow> \<sigma> x = \<sigma> y)}" 
               unfolding fun_upd_equivp_def
               by(rule update\<^sub>_sound[simplified fun_upd_equivp_def], simp)
      have ** : "\<And> R \<sigma>. equivp R \<Longrightarrow> \<not> R x x' \<Longrightarrow>
                         fun_upd_equivp R (fun_upd_equivp R \<sigma> x (Some y)) x' (Some z) =
                         fun_upd_equivp R (fun_upd_equivp R \<sigma> x' (Some z)) x (Some y)"
               unfolding fun_upd_equivp_def
               apply(rule ext)
               apply(case_tac "R xa x'", auto)
               apply(erule contrapos_np)
               apply(frule equivp_transp, simp_all)
               apply(erule equivp_symp, simp_all)
               done
      show ?thesis 
      apply(simp add: update')
      apply(insert  assms[simplified sharing_def])
      apply(simp add: Abs_memory_inverse [OF *] **)
   done
qed

subsection{* Properties on lookup and update wrt the Sharing Relation*}

lemma update_triv:
  assumes 1: "x shares\<^bsub>\<sigma>\<^esub> y"
    and   2: "y \<in> Domain \<sigma>" 
  shows      "\<sigma> (x :=\<^sub>$ (\<sigma> $ y)) = \<sigma>"
proof -
  {
    fix z
    assume zx: "z shares\<^bsub>\<sigma>\<^esub> x"
    then have zy: "z shares\<^bsub>\<sigma>\<^esub> y"
      using 1 by (rule sharing_trans)
    have  F: "y \<in> Domain \<sigma> \<Longrightarrow> x shares\<^bsub>\<sigma>\<^esub> y 
              \<Longrightarrow> Some (the (fst (Rep_memory \<sigma>) x)) = fst (Rep_memory \<sigma>) y"
      by(auto simp: Domain_def dest: shares_result)
    have "Some (the (fst (Rep_memory \<sigma>) y)) = fst (Rep_memory \<sigma>) z"
      using zx and shares_result [OF zy] shares_result [OF zx]
      using F [OF 2 1]
      by simp
  } note 3 = this
  show ?thesis
    unfolding update'' lookup_def fun_upd_equivp_def
    by (simp add: 3 Rep_memory_inverse if_cong)
qed

lemma update_idem' : 
   assumes 1: "x shares\<^bsub>\<sigma>\<^esub> y"
   and     2: "x \<in> Domain \<sigma>"
   and     3: "\<sigma> $ x = z"
   shows   "\<sigma>(y:=\<^sub>$ z) = \<sigma>"
proof - 
  have * : "y \<in> Domain \<sigma>"
            by(simp add: shares_dom[OF 1, symmetric] 2)
  have **: "\<sigma> (x :=\<^sub>$ (\<sigma> $ y)) = \<sigma>" 
    using 1 2 * 
    by (simp add: update_triv)
  also have "(\<sigma> $ y) = \<sigma> $ x"
    by (simp only: lookup_def shares_result [OF 1])
  finally show ?thesis 
    using 1 2 3 sharing_sym update_triv 
    by fast
qed  

lemma update_idem : 
   assumes 2: "x \<in> Domain \<sigma>"
   and     3: "\<sigma> $ x = z"
   shows   "\<sigma>(x:=\<^sub>$ z) = \<sigma>"
proof - 
 show ?thesis
 using 2 3 sharing_refl update_triv
 by fast 
qed  

lemma update_apply:  "(\<sigma>(x :=\<^sub>$ y)) $ z = (if z shares\<^bsub>\<sigma>\<^esub> x then y else \<sigma> $ z)"
proof -
   have *: "(\<lambda>z. if z shares\<^bsub>\<sigma>\<^esub> x then Some y else fst (Rep_memory \<sigma>) z, snd (Rep_memory \<sigma>)) 
           \<in> {(\<sigma>, R). equivp R \<and> (\<forall>x y. R x y \<longrightarrow> \<sigma> x = \<sigma> y)}" 
           unfolding sharing_def
           by(rule update\<^sub>_sound[simplified fun_upd_equivp_def], simp)
   show ?thesis  
      proof (cases "z shares\<^bsub>\<sigma>\<^esub> x")
         case True 
              assume A: "z shares\<^bsub>\<sigma>\<^esub> x" 
              show      "\<sigma> (x :=\<^sub>$ y) $ z = (if z shares\<^bsub>\<sigma>\<^esub> x then y else \<sigma> $ z)"
                       unfolding update'' lookup_def fun_upd_equivp_def
                       by(simp add: Abs_memory_inverse  [OF *])
      next
         case False 
              assume A: "\<not> z shares\<^bsub>\<sigma>\<^esub> x " 
              show      "\<sigma> (x :=\<^sub>$ y) $ z = (if z shares\<^bsub>\<sigma>\<^esub> x then y else \<sigma> $ z)"
                        unfolding update'' lookup_def fun_upd_equivp_def
                        by(simp add: Abs_memory_inverse  [OF *])
      qed
qed

lemma update_share: 
   assumes "z shares\<^bsub>\<sigma>\<^esub> x"
   shows   "\<sigma>(x :=\<^sub>$ a) $ z = a"
   using assms
   by (simp only: update_apply if_True)

lemma update_other: 
   assumes "\<not>(z shares\<^bsub>\<sigma>\<^esub> x)"
   shows   "\<sigma>(x :=\<^sub>$ a) $ z = \<sigma> $ z"
   using assms
   by (simp only: update_apply if_False)

lemma lookup_update_rep:
  assumes 1: "(snd (Rep_memory  \<sigma>')) x y"
  shows      "(fst (Pair_upd_lifter (Rep_memory  \<sigma>') src dst)) x = 
              (fst (Pair_upd_lifter (Rep_memory  \<sigma>') src dst)) y"
  using 1 shares_result sharing_def sharing_upd update.rep_eq
  by (metis (hide_lams, no_types) )

lemma lookup_update_rep'':
  assumes 1: "x shares\<^bsub>\<sigma>\<^esub> y"
  shows      " (\<sigma> (src :=\<^sub>$ dst)) $ x = (\<sigma> (src :=\<^sub>$ dst)) $ y"
  using 1 lookup_def lookup_update_rep sharing_def update.rep_eq
  by metis 

theorem  memory_ext :
 assumes *     : "\<And> x y. (x shares\<^bsub>\<sigma>\<^esub> y) = (x shares\<^bsub>\<sigma>'\<^esub> y)"
  and    **    : "Domain \<sigma> = Domain \<sigma>'"
  and    ***   : "\<And> x. \<sigma> $ x = \<sigma>' $ x"
 shows           "\<sigma> = \<sigma>'"
apply(subst Rep_memory_inverse[symmetric])
apply(subst (3) Rep_memory_inverse[symmetric])
apply(rule arg_cong[of _ _ "Abs_memory"])
apply(auto simp:Product_Type.prod_eq_iff)
proof -
  show "fst (Rep_memory \<sigma>) = fst (Rep_memory \<sigma>')"
        apply(rule ext, insert ** ***, simp add: SharedMemory.lookup_def Domain_def)
        apply (metis domIff option.expand)
        done
next
  show "snd (Rep_memory \<sigma>) = snd (Rep_memory \<sigma>')"
        by(rule ext, rule ext, insert *, simp add: sharing_def)
qed  

text{* Nice connection between sharing relation, domain of the memory and content equaltiy
       on the one hand and equality on the other; this proves that our memory model is fully
       abstract in these three operations. *}
corollary memory_ext2: "(\<sigma> = \<sigma>') = ((\<forall> x y. (x shares\<^bsub>\<sigma>\<^esub> y) = (x shares\<^bsub>\<sigma>'\<^esub> y)) 
                                    \<and>  Domain \<sigma> = Domain \<sigma>' 
                                    \<and>  (\<forall> x. \<sigma> $ x = \<sigma>' $ x))"
by(auto intro: memory_ext)

subsection{* Rules On Sharing and Memory Transfer *}

(*memory transfer*)

lemma transfer_rep_inv_E:
  assumes 1 : "\<sigma> \<in> {(\<sigma>, R). equivp R \<and> (\<forall>x y. R x y \<longrightarrow> \<sigma> x = \<sigma> y)}"
  and     2 : "memory_inv (transfer_rep \<sigma> src dst) \<Longrightarrow> Q"
  shows Q
  using assms transfer_rep_sound[of \<sigma>]
  by (auto simp: Abs_memory_inverse)

lemma transfer_rep_fst1:
  assumes 1: "\<sigma> = fst(transfer_rep  (Rep_memory  \<sigma>') src dst)"
  shows "\<And>x. x = dst \<Longrightarrow> \<sigma> x = (fst (Rep_memory  \<sigma>')) src"
  using 1  unfolding transfer_rep_simp    
  by simp

lemma transfer_rep_fst2:
  assumes 1: "\<sigma> = fst(transfer_rep  (Rep_memory  \<sigma>') src dst)"
  shows "\<And>x. x \<noteq>  dst \<Longrightarrow> \<sigma> x = (fst (Rep_memory  \<sigma>')) (id x)"
  using 1  unfolding transfer_rep_simp    
  by simp

lemma lookup_transfer_rep':
    "(fst (transfer_rep (Rep_memory  \<sigma>') src dst)) src = 
     (fst (transfer_rep (Rep_memory  \<sigma>') src dst)) dst"
  using Rep_memory [of "\<sigma>'"]
  apply (erule_tac src= "src" and dst = "dst" in transfer_rep_inv_E)
  apply (rotate_tac 1)
  apply (subst (asm) surjective_pairing[of "(transfer_rep (Rep_memory \<sigma>') src dst)"])
  unfolding memory_inv.simps 
  apply (erule conjE)
  apply (erule allE)+
  apply (erule impE)
  unfolding transfer_rep_simp
  apply auto
  using equivp_reflp snd_memory_equivp
  apply metis 
done

theorem share_transfer: 
   "x shares\<^bsub>\<sigma>(a \<Join> b)\<^esub> y = ( (y = b \<and> (x = b 
                                        \<or> (x \<noteq> b \<and>  x shares\<^bsub>\<sigma>\<^esub> a))) \<or>
                             (y \<noteq> b \<and> ((x = b \<and> a shares\<^bsub>\<sigma>\<^esub> y) 
                                        \<or> (x \<noteq> b \<and> x shares\<^bsub>\<sigma>\<^esub> y))))"
unfolding sharing_def transfer_def 
unfolding transfer_def map_fun_def o_def id_def 
apply(subst Abs_memory_inverse[OF transfer_rep_sound2], 
      simp add: transfer_rep_simp)
apply (metis equivp_reflp sharing_charn2)
done

lemma transfer_share:"a shares\<^bsub>\<sigma>(a \<Join> b)\<^esub> b" 
  by(simp add: share_transfer sharing_refl)

lemma transfer_share_sym:"a shares\<^bsub>\<sigma> (b \<Join> a)\<^esub> b" 
  by(simp add: share_transfer sharing_refl)

lemma transfer_share_mono:"x shares\<^bsub>\<sigma>\<^esub> y \<Longrightarrow> \<not>(x shares\<^bsub>\<sigma>\<^esub> b) \<Longrightarrow> (x shares\<^bsub>\<sigma> (a \<Join> b)\<^esub> y)"
   by(auto simp: share_transfer sharing_refl)

lemma  transfer_share_charn: 
   "\<not>(x shares\<^bsub>\<sigma>\<^esub> b) \<Longrightarrow> \<not>(y shares\<^bsub>\<sigma>\<^esub> b) \<Longrightarrow> x shares\<^bsub>\<sigma>(a \<Join> b)\<^esub> y = x shares\<^bsub>\<sigma>\<^esub> y"
  by(auto simp: share_transfer sharing_refl)
 
lemma transfer_share_trans:"(a shares\<^bsub>\<sigma>\<^esub> x) \<Longrightarrow> (x shares\<^bsub>\<sigma>(a \<Join> b)\<^esub> b)"
  by(auto simp: share_transfer sharing_refl sharing_sym)

lemma transfer_share_trans_sym:"(a shares\<^bsub>\<sigma>\<^esub> y) \<Longrightarrow> (b shares\<^bsub>(\<sigma>(a \<Join> b))\<^esub> y)"
  using transfer_share_trans sharing_sym  
  by fast

lemma transfer_share_trans': "(a shares\<^bsub>(\<sigma>(a \<Join> b))\<^esub> z) \<Longrightarrow> (b shares\<^bsub>(\<sigma>(a \<Join> b))\<^esub> z)"
  using transfer_share sharing_sym sharing_trans 
  by fast

lemma transfer_tri : "x shares\<^bsub>\<sigma> (a \<Join> b)\<^esub> y \<Longrightarrow> x shares\<^bsub>\<sigma>\<^esub> b \<or> b shares\<^bsub>\<sigma>\<^esub> y \<or> x shares\<^bsub>\<sigma>\<^esub> y"
by (metis sharing_sym transfer_share_charn)

lemma transfer_tri' :  "\<not> x shares\<^bsub>\<sigma> (a \<Join> b)\<^esub> y \<Longrightarrow>  y shares\<^bsub>\<sigma>\<^esub> b \<or> \<not> x shares\<^bsub>\<sigma>\<^esub> y"
by (metis sharing_sym sharing_trans transfer_share_mono)

lemma transfer_dest' : 
assumes 1: "a shares\<^bsub>\<sigma> (a \<Join> b)\<^esub> y"
    and 2: "b \<noteq> y"
  shows       "a shares\<^bsub>\<sigma>\<^esub> y"
  using assms 
  by(auto simp: share_transfer sharing_refl sharing_sym)

lemma transfer_dest : 
assumes 1: "\<not>(x shares\<^bsub>\<sigma>\<^esub> a)" 
    and 2: "x \<noteq> b"
    and 3: "x shares\<^bsub>\<sigma>\<^esub> b"
  shows    "\<not>(x shares\<^bsub>\<sigma> (a \<Join> b)\<^esub> b)"
  using assms 
  by(auto simp: share_transfer sharing_refl sharing_sym)

lemma transfer_dest'':"x = b \<Longrightarrow> y shares\<^bsub>\<sigma>\<^esub> a \<Longrightarrow> x shares\<^bsub>\<sigma>(a \<Join> b)\<^esub> y"
by (metis sharing_sym transfer_share_trans_sym)

thm  share_transfer  (* the universal catch-all *) 
     transfer_share          
     transfer_share_sym      
     sharing_sym [THEN transfer_share_trans]     
     (*  transfer_share_trans  *)
     sharing_sym [THEN transfer_share_trans_sym]
     (* transfer_share_trans_sym *)
     transfer_share_trans'   
     transfer_dest''         
     transfer_dest'          
     transfer_tri'           
     transfer_share_mono     
     transfer_tri           
     transfer_share_charn   
     transfer_dest          

subsection{* Properties on Memory Transfer and Lookup *}

lemma transfer_share_lookup1:  "(\<sigma>(x \<Join> y)) $ x = \<sigma> $ x"
  using  lookup_transfer_rep' transfer_rep_fst1
  unfolding lookup_def transfer.rep_eq
  by metis

lemma transfer_share_lookup2:
      "(\<sigma>(x \<Join> y)) $ y = \<sigma> $ x"
  using transfer_rep_fst1
  unfolding transfer.rep_eq lookup_def
  by metis  

lemma add\<^sub>e_not_share_lookup:
  assumes 1: "\<not>(x shares\<^bsub>\<sigma>\<^esub> z)"
  and     2: "\<not>(y shares\<^bsub>\<sigma>\<^esub> z)"
  shows  "\<sigma> (x \<Join> y) $ z = \<sigma> $ z"
  using assms
  unfolding sharing_def lookup_def  transfer.rep_eq
  using id_def sharing_def sharing_refl transfer_rep_fst2
  by metis

lemma transfer_share_dom:
  assumes 1: "z \<in> Domain \<sigma>"
  and     2: "\<not>(y shares\<^bsub>\<sigma>\<^esub> z)"
  shows      "(\<sigma>(x \<Join> y)) $ z = \<sigma> $ z"
  using assms
  unfolding  Domain_def sharing_def lookup_def 
  using 2 transfer.rep_eq id_apply sharing_refl transfer_rep_fst2
  by metis 

lemma shares_result':
  assumes   1: "(x shares\<^bsub>\<sigma>\<^esub> y)"
  shows      " \<sigma> $ x = \<sigma> $ y"
  using assms lookup_def shares_result
  by metis 

lemma transfer_share_cancel1:
  assumes 1: "(x shares\<^bsub>\<sigma>\<^esub> z)"
  shows      "(\<sigma>(x \<Join> y)) $ z = \<sigma> $ x"
  using 1 transfer.rep_eq transfer_share_trans lookup_def 
          transfer_rep_fst1 shares_result
  by (metis)

subsection{* Test on Sharing and Transfer via smt ... *}

(*test to see the needed lemmas by smt*)
lemma "\<forall>x y. x \<noteq> y \<longrightarrow> \<not>(x shares\<^bsub>\<sigma>\<^esub> y) \<Longrightarrow>
       \<sigma> $ x > \<sigma> $ y \<Longrightarrow>  \<sigma>(3 \<Join> (4::nat))= \<sigma>' \<Longrightarrow> 
       \<sigma>'' = (\<sigma>'(3 :=\<^sub>$ ((\<sigma>' $ 4) + 2))) \<Longrightarrow>
       x \<noteq> 3 \<Longrightarrow> x \<noteq> 4 \<Longrightarrow> y \<noteq> 3 \<Longrightarrow> y \<noteq> 4 \<Longrightarrow>  \<sigma>'' $ x > \<sigma>'' $ y"
by (smt add\<^sub>e_not_share_lookup share_transfer update_apply)

subsection{* Instrumentation of the smt Solver*}

lemma  transfer_share_charn_smt : 
   "\<not>(i  shares\<^bsub>\<sigma>\<^esub> k') \<and>
    \<not>(k shares\<^bsub>\<sigma>\<^esub> k') \<longrightarrow>
    i shares\<^bsub>\<sigma>(i' \<Join> k')\<^esub> k = i shares\<^bsub>\<sigma>\<^esub> k"
  using transfer_share_charn
  by fast  

lemma add\<^sub>e_not_share_lookup_smt:
 "\<not>(x shares\<^bsub>\<sigma>\<^esub> z)\<and> \<not>(y shares\<^bsub>\<sigma>\<^esub> z)\<longrightarrow> (\<sigma> (x \<Join> y) $ z) = (\<sigma> $ z)"
  using add\<^sub>e_not_share_lookup
  by auto

lemma transfer_share_dom_smt:
  "z \<in> Domain \<sigma> \<and> \<not>(y shares\<^bsub>\<sigma>\<^esub> z)\<longrightarrow> (\<sigma>(x \<Join> y)) $ z = \<sigma> $ z"
  using transfer_share_dom
  by auto 

lemma transfer_share_cancel1_smt:
   "(x shares\<^bsub>\<sigma>\<^esub> z)\<longrightarrow> (\<sigma>(x \<Join> y)) $ z = \<sigma> $ x"
  using transfer_share_cancel1
  by auto

lemma lookup_update_rep''_smt:
 "x shares\<^bsub>\<sigma>\<^esub> y\<longrightarrow>(\<sigma> (src :=\<^sub>$ dst)) $ x = (\<sigma> (src :=\<^sub>$ dst)) $ y"
  using lookup_update_rep''
  by auto 

theorem update_commute_smt: 
  "\<not> (x shares\<^bsub>\<sigma>\<^esub> x') \<longrightarrow> ((\<sigma>(x :=\<^sub>$ y))(x' :=\<^sub>$ z)) = (\<sigma>(x':=\<^sub>$ z)(x :=\<^sub>$ y))" 
   using update_commute
   by auto

theorem update_cancel_smt: 
   "(x shares\<^bsub>\<sigma>\<^esub> x')\<longrightarrow> (\<sigma>(x :=\<^sub>$ y)(x' :=\<^sub>$ z)) = (\<sigma>(x' :=\<^sub>$ z))"  
  using update_cancel
  by auto

lemma update_other_smt: 
    "\<not>(z shares\<^bsub>\<sigma>\<^esub> x)\<longrightarrow> (\<sigma>(x :=\<^sub>$ a) $ z) = \<sigma> $ z"
   using update_other
   by auto

lemma update_share_smt: 
  "(z shares\<^bsub>\<sigma>\<^esub> x) \<longrightarrow> (\<sigma>(x :=\<^sub>$ a) $ z) = a"
   using update_share
  by auto

lemma update_idem_smt : 
  "(x shares\<^bsub>\<sigma>\<^esub> y)\<and> x \<in> Domain \<sigma> \<and> (\<sigma> $ x = z) \<longrightarrow> (\<sigma>(x:=\<^sub>$ z)) = \<sigma>"
   using update_idem
   by fast

lemma update_triv_smt:
  "(x shares\<^bsub>\<sigma>\<^esub> y) \<and> y \<in> Domain \<sigma> \<longrightarrow> (\<sigma> (x :=\<^sub>$ (\<sigma> $ y))) = \<sigma>"
  using update_triv
  by auto

lemma shares_result_smt: 
 "x shares\<^bsub>\<sigma>\<^esub> y\<longrightarrow> \<sigma> $ x = \<sigma> $ y"
  using shares_result'
  by fast

lemma shares_dom_smt : 
  "x shares\<^bsub>\<sigma>\<^esub> y \<longrightarrow> (x \<in> Domain \<sigma>) = (y \<in> Domain \<sigma>)"
  using shares_dom  by fast

lemma sharing_sym_smt  : 
    "x shares\<^bsub>\<sigma>\<^esub> y\<longrightarrow>y shares\<^bsub>\<sigma>\<^esub> x"
   using sharing_sym
   by auto

lemma sharing_trans_smt:
   "x shares\<^bsub>\<sigma>\<^esub> y \<and> y shares\<^bsub>\<sigma>\<^esub> z \<longrightarrow> x shares\<^bsub>\<sigma>\<^esub> z"
   using sharing_trans
   by auto

lemma nat_0_le_smt: "0 \<le> z \<longrightarrow> int (nat z) = z"
 by transfer clarsimp

lemma nat_le_0_smt: "0 > z \<longrightarrow> int (nat z) = 0"
 by transfer clarsimp

lemma transfer_share_trans_smt:
  "(x shares\<^bsub>\<sigma>\<^esub> z) \<longrightarrow>(z shares\<^bsub>\<sigma>(x \<Join> y)\<^esub> y)"
  using transfer_share_trans
  by fast

lemma transfer_share_mono_smt:
  "(x shares\<^bsub>\<sigma>\<^esub> y)\<and> \<not>(x shares\<^bsub>\<sigma>\<^esub> y')\<longrightarrow> (x shares\<^bsub>\<sigma> (x' \<Join> y')\<^esub> y)"
  using transfer_share_mono
  by fast

lemma transfer_share_trans'_smt:
  "(x shares\<^bsub>(\<sigma>(x \<Join> y))\<^esub> z)\<longrightarrow>(y shares\<^bsub>(\<sigma>(x \<Join> y))\<^esub> z) "
  using transfer_share_trans'
  by fast

lemma transfer_share_old_new_trans_smt:
  "(x shares\<^bsub>\<sigma>\<^esub> z)\<longrightarrow>(y shares\<^bsub>(\<sigma>(x \<Join> y))\<^esub> z) "
  using transfer_share_trans_sym
  by fast

lemma transfer_share_old_new_trans1_smt:
      "a shares\<^bsub>\<sigma>\<^esub> b \<and> a shares\<^bsub>\<sigma>\<^esub> c \<longrightarrow> 
       (c shares\<^bsub>(\<sigma> (a \<Join> d))\<^esub> b ) "
  using transfer_share_trans_smt sharing_sym_smt sharing_trans_smt
  by metis

lemma Domain_mono_smt: 
 "x \<in> Domain \<sigma> \<and> (x shares\<^bsub>\<sigma>\<^esub> y)\<longrightarrow>y \<in> Domain \<sigma>"
  using Domain_mono
  by fast

lemma sharing_upd_smt: "x shares\<^bsub>(\<sigma>(a :=\<^sub>$ b))\<^esub> y = x shares\<^bsub>\<sigma>\<^esub> y"
  using sharing_upd
  by fast

lemma  sharing_init_mem_list_smt :
  "i \<noteq> k \<longrightarrow> \<not>(i shares\<^bsub>init_mem_list S\<^esub> k)"
  using sharing_init_mem_list
  by fast

lemma mem1_smt:
  "(\<sigma>(a\<Join>b) $ a) = (\<sigma>(a\<Join>b) $ b)" 
  using transfer_share_lookup1 transfer_share_lookup2
  by metis 

lemmas sharing_smt =  sharing_refl               transfer_share        
                      sharing_commute            nat_le_0_smt             
                      nat_0_le_smt               sharing_sym_smt          
                      transfer_share_lookup1 transfer_share_lookup2  
                      sharing_init_mem_list_smt  sharing_upd_smt          
                      shares_result_smt          transfer_share_old_new_trans_smt
                      transfer_share_trans_smt   mem1_smt                    
                      update_share_smt           shares_dom_smt            
                      Domain_mono_smt            sharing_trans_smt         
                      transfer_share_cancel1_smt transfer_share_trans'_smt    
                      update_apply               update_other_smt            
                      update_cancel_smt          transfer_share_old_new_trans1_smt
                      lookup_update_rep''_smt    update_triv_smt               
                      transfer_share_mono_smt    update_commute_smt            
                      transfer_share_dom_smt     add\<^sub>e_not_share_lookup_smt    
                      update_idem_smt            transfer_share_charn_smt
(* @Chantal : if you want, you could add a generic smt config here ... *)

subsection {*Tools for the initialization of the memory*}

definition update_memory\<^sub>i\<^sub>n\<^sub>i\<^sub>t :: "'address list \<Rightarrow> 'value list \<Rightarrow> ('address, 'value)memory"
where     "update_memory\<^sub>i\<^sub>n\<^sub>i\<^sub>t ADD VAL = 
           (foldl (\<lambda> m (x, y). (m (x:=\<^sub>$y))) init (zip ADD VAL))"


definition share_memory\<^sub>i\<^sub>n\<^sub>i\<^sub>t :: "'address list \<Rightarrow> 'address list \<Rightarrow>
                                ('address, 'value)memory \<Rightarrow>('address,'value)memory"
where     "share_memory\<^sub>i\<^sub>n\<^sub>i\<^sub>t SRC DST m = 
           (foldl (\<lambda>m (x, y). (m (x\<Join>y))) m (zip SRC DST))"

definition memory\<^sub>i\<^sub>n\<^sub>i\<^sub>t :: "'address list \<Rightarrow> 'value list \<Rightarrow> 'address list \<Rightarrow>
                            ('address,'value)memory"
where     "memory\<^sub>i\<^sub>n\<^sub>i\<^sub>t SRC VAL DST = 
           foldl (\<lambda> m (SRC, DST). share_memory\<^sub>i\<^sub>n\<^sub>i\<^sub>t SRC DST m) 
           (update_memory\<^sub>i\<^sub>n\<^sub>i\<^sub>t SRC VAL) [(SRC, DST)]"

lemmas sharing_refl_smt  = sharing_refl (* legacy *)


subsection{* An Intrastructure for Global Memory Spaces *}
text{* Memory spaces are common concepts in Operating System (OS) design since it is 
       a major objective of OS kernels to separate logical, linear memory spaces
       belonging to different processes (or in other terminologies such as PiKeOS: tasks)
       from each other. We achieve this goal by modeling the adresses of memory spaces
       as a \emph{pair} of a subject (e.g. process or task, denominated by a process-id or
       task-id) and a location (a conventional adress). *}
text{*
       Our model is still generic - we do not impose a particular type for subjects  
       or locations (which could be modeled in a concrete context by an enumeration type as well as
       integers of bitvector representations); for the latter, however, we require that
       they are instances of the type class @{typ "'\<alpha>::comm_semiring_1"} assuring that there
       is a minimum of infrastructure for address calculation: there must exist a
       @{term 0}-element, a distinct  @{term 1}-element and an addition operation with
       the usual properties.
*}

fun init\<^sub>g\<^sub>l\<^sub>o\<^sub>b\<^sub>a\<^sub>l\<^sub>m\<^sub>e\<^sub>m :: "(('sub\<times>'loc::comm_semiring_1), '\<beta>) memory 
                     \<Rightarrow>  ('sub\<times>'loc) \<Rightarrow> '\<beta> list 
                     \<Rightarrow> (('sub\<times>'loc), '\<beta>) memory"  ("_ |> _ <| _" [60,60,60] 70) 
where "\<sigma> |> start <| [] = \<sigma>"
    | "\<sigma> |> (sub,loc) <| (a # S) = ((\<sigma>((sub,loc):=\<^sub>$ a)) |> (sub, loc+1)<| S)"

lemma Domain_mem_init_Nil : "Domain(\<sigma> |> start <| []) = Domain \<sigma>"
by simp

subsubsection{* Example *}

type_synonym task_id = int
type_synonym loc = int

type_synonym global_mem = "((task_id\<times>loc), int)memory"

definition \<sigma>\<^sub>0 :: "global_mem"
where     "\<sigma>\<^sub>0 \<equiv> init |> (0,0) <| [0,0,0,0]
                     |> (2,0) <| [0,0]
                     |> (4,0) <| [2,0]" 

(* why does this not work ?
value "(\<sigma>\<^sub>0 ((4, 0)\<Join>(2, 1))) $ (4, 0)" 
*)

lemma \<sigma>\<^sub>0_Domain: "Domain \<sigma>\<^sub>0 = {(4, 1), (4, 0), (2, 1), (2, 0), (0, 3), (0, 2), (0, 1), (0, 0)}"
unfolding \<sigma>\<^sub>0_def
by(simp add: sharing_upd)
  
subsection{* Memory Transfer Based on Sharing Closure (Experimental) *}

text{* One might have a fundamentally different understanding on memory transfer --- at least as
far as the sharing relation is concerned. The prior definition of sharing is based on the idea that
the overridden part is ``carved out'' of the prior equivalence. Instead of transforming the
equivalence relation, one might think of transfer as an operation where the to be shared memory is
synchronized and then the equivalence relation closed via reflexive-transitive closure. *}

definition transfer' :: "('a,'b)memory \<Rightarrow> 'a \<Rightarrow> 'a  \<Rightarrow> ('a, 'b)memory" ("_ '(_ \<bar>\<Join>\<bar> _')" [0,111,111]110)
where     "\<sigma>(i \<bar>\<Join>\<bar> k) = 
           (\<sigma>(i :=\<^sub>$ (\<sigma> $ k)) :=\<^sub>R (rtranclp(\<lambda>x y. ($\<^sub>R \<sigma>) x y \<or> (x=i \<and> y = k) \<or> (x=k \<and> y = i))))" 


lemma transfer'_rep_sound:
    "(fst(Rep_memory (\<sigma>(i:=\<^sub>$(\<sigma> $ k)))),(\<lambda>xa ya. ($\<^sub>R \<sigma>) xa ya \<or> xa = x \<and> ya = y \<or> xa = y \<and> ya = x)\<^sup>*\<^sup>*) 
     \<in> 
     {(\<sigma>, R). equivp R \<and> (\<forall>x y. R x y \<longrightarrow> \<sigma> x = \<sigma> y)}"
unfolding update_def 
proof(auto)
    let ?R' = "((\<lambda>xa ya. ($\<^sub>R \<sigma>) xa ya \<or> xa = x \<and> ya = y \<or> xa = y \<and> ya = x)\<^sup>*\<^sup>*)"
    have E : "equivp ($\<^sub>R \<sigma>)"  unfolding lookup\<^sub>R_def by (metis snd_memory_equivp)
    have fact1 : "symp ?R'"
          unfolding symp_def      
          apply (auto) 
          apply (erule Transitive_Closure.rtranclp_induct,auto)
          apply (drule E[THEN equivp_symp])
          by (metis (lifting, full_types) converse_rtranclp_into_rtranclp)+
    have fact2 : "transp ?R'"
          unfolding transp_def
          by (metis (lifting, no_types) rtranclp_trans)
    have fact3 : "reflp ?R'"
          unfolding reflp_def
          by (metis (lifting) rtranclp.rtrancl_refl)
    show "equivp (\<lambda>xa ya. ($\<^sub>R \<sigma>) xa ya \<or> xa = x \<and> ya = y \<or> xa = y \<and> ya = x)\<^sup>*\<^sup>*"
         using fact1  fact2 fact3 equivpI  by auto
next
    fix xa ya
    assume H : "(\<lambda>xa ya. ($\<^sub>R \<sigma>) xa ya \<or> xa = x \<and> ya = y \<or> xa = y \<and> ya = x)\<^sup>*\<^sup>* xa ya"
    have   * : "(fun_upd_equivp (snd (Rep_memory \<sigma>)) (fst (Rep_memory \<sigma>)) i (Some (\<sigma> $ k)), 
                                                      snd (Rep_memory \<sigma>))
                \<in> {(\<sigma>, R). equivp R \<and> (\<forall>x y. R x y \<longrightarrow> \<sigma> x = \<sigma> y)}"  oops
(*
    show  "fst (Rep_memory (Abs_memory (Pair_upd_lifter (Rep_memory \<sigma>) i (\<sigma> $ k)))) xa =
           fst (Rep_memory (Abs_memory (Pair_upd_lifter (Rep_memory \<sigma>) i (\<sigma> $ k)))) ya"
           apply(subst surjective_pairing[of "(Rep_memory \<sigma>)"])
           apply(subst Pair_upd_lifter.simps)
           apply(subst (4)surjective_pairing[of "(Rep_memory \<sigma>)"])
           apply(subst Pair_upd_lifter.simps)
           apply(auto simp: Abs_memory_inverse[OF *])
           apply(simp add:  SharedMemory.lookup_def)
           apply(insert H, simp add: SharedMemory.lookup\<^sub>R_def)
oops
*)

subsection{* Framing Conditions on Shared Memories (Experimental)*}

text{* The Frame of an action --- or a monadic operation --- is the smallest possible subset of the
domain of a memory, in which the action has effect, i.e. it modifies only locations
in this set.*}


(* Experimental. Known problem: should run over all memory-maps, 
   but only one fixed sharing relation R, in which also the
   equivs of x in R were collected... Frame\<^bsub>R\<^esub> A ? Fibered Framing ?*)
definition Frame :: "(('\<alpha>, '\<beta>)memory \<Rightarrow> ('\<alpha>, '\<beta>)memory) \<Rightarrow> '\<alpha> set"
where     "Frame A \<equiv> Least(\<lambda>X. \<forall> \<sigma>. (\<sigma>(reset X)) = ((A \<sigma>)(reset X)))" 

(* hard. *)
lemma Frame_update : "Frame (\<lambda>\<sigma>. \<sigma>(x :=\<^sub>$ y)) = {x}"
oops

(* hard *)
lemma Frame_compose : "Frame (A o B) \<subseteq> Frame A \<union> Frame B"
oops


notation transfer ("add\<^sub>e")  (* legacy *)
lemmas add\<^sub>e_def = transfer_def (* legacy *)
lemmas add\<^sub>e_rep_eq = transfer.rep_eq (* legacy, was add\<^sub>e.rep_eq *)
lemmas transfer_share_old_new_trans = transfer_share_trans_sym (* legacy *)
lemmas sharing_commute_smt = sharing_commute (*legacy *)
lemmas update_apply_smt = update_apply (* legacy *)
lemmas transfer_share_lookup2_smt = transfer_share_lookup2 (* legacy *)
lemmas transfer_share_lookup1_smt = transfer_share_lookup1 (* legacy *)
lemmas transfer_share_smt = SharedMemory.transfer_share (* legacy *)


end
