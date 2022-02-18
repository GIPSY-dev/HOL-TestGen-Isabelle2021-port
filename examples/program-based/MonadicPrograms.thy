chapter {* Proof of concept for a monadic symbolic execution calculus for WHILE programs *}

theory MonadicPrograms
imports "Monads"
begin

section\<open>Monadic Presentation of Assignments (based on Records) \<close>

text{* A "lifter" that embeds a state transformer into the state-exception monad.  *}

definition assign :: "('\<sigma> \<Rightarrow> '\<sigma>) \<Rightarrow> (unit,'\<sigma>)MON\<^sub>S\<^sub>E"
where     "assign f = (\<lambda>\<sigma>. Some((), f \<sigma>))"

(* TODO : better syntax support *)

text{* Basic Symbolic execution rules. As they are equalities, they can also
be used as program optimization rules. *}

lemma exec_assign  : "(\<sigma> \<Turnstile> ( _ \<leftarrow> assign f; M)) = ((f \<sigma>) \<Turnstile>  M)"
by(subst Monads.exec_bind_SE_success, simp_all add: assign_def)

lemmas exec_assignD = exec_assign[THEN iffD1]

lemma exec_assign' : "(\<sigma> \<Turnstile> (assign f ;- M)) = ((f \<sigma>) \<Turnstile>  M)"
unfolding bind_SE'_def
by(subst Monads.exec_bind_SE_success, simp_all add: assign_def)

lemmas exec_assignD' = exec_assign'[THEN iffD1]

section\<open>Tactic Support \<close>

text\<open>TODO: unwind tactic\<close>


section\<open>A Monadic Version of the Hoare-Calculus \<close>


(* TODO Integrate this SE calculus into Monads *) 

(* TODO Develop a Hoare-Calculus with WP *) 

(* TODO Re-Develop IMP for Program testing *) 


end
