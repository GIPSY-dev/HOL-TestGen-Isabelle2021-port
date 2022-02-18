theory SchedulerTesting
imports 
Testing
begin

type_synonym Resource = nat

type_synonym Process  = nat

record System = 
       r       :: "Resource"
       last    :: "Process option"
       current :: "Process option"
       waiting :: "Process set"

section{* Macro OCL *}

definition OclnotEmpty :: "'a option \<Rightarrow> bool" ("_ ->notEmpty" 100)
where "OclnotEmpty x = (None \<noteq> x)"

definition OclnotEmpty' :: "'a set \<Rightarrow> bool"  ("_ ->notEmpty'" 100)
where "OclnotEmpty' x = ({} \<noteq> x)"

definition OclSize :: "'a set \<Rightarrow> nat" ("_ ->size'(')" [99]99)
where      "(S ->size()) = (card S)"

definition OclIncluding :: "'a set \<Rightarrow> 'a \<Rightarrow> 'a set" ("_ ->including'(_')" [99,99]99)
where     "S ->including(x) = S \<union> {x}"

definition OclExcluding :: "'a set \<Rightarrow> 'a \<Rightarrow> 'a set" ("_ ->excluding'(_')" [99,99]99)
where     "S ->excluding(x) = S - {x}"

definition OclAny :: "'a set \<Rightarrow> 'a"  ("_ ->any'(true')" [99]99)
where     "(S ->any(true)) = (SOME x. x \<in> S)"

definition swap\<^sub>p\<^sub>r\<^sub>e :: "System \<Rightarrow> bool"
where     "swap\<^sub>p\<^sub>r\<^sub>e s = (waiting s ->notEmpty')"


section{* OS Model*}

text {*

In OCL:

context System
inv: waiting -> notEmpty() implies current -> notEmpty()
 and last -> notEmpty() implies (last <> current and waiting -> includes(last))
 and current -> notEmpty() implies not waiting -> includes(current)
context System::swap(): Process
pre: waiting -> notEmpty()
post: let p = if last@pre -> isEmpty() or waiting@pre -> size() = 1
              then waiting@pre -> any(true)
              else waiting@pre -> excluding(last@pre) -> any(true)
      in current = p and result = p and
      waiting = waiting@pre -> excluding(p) -> including(current@pre)
      and last = current@pre

end 
*}


definition inv\<^sub>S\<^sub>y\<^sub>s\<^sub>t\<^sub>e\<^sub>m :: "System \<Rightarrow> bool"
where     "inv\<^sub>S\<^sub>y\<^sub>s\<^sub>t\<^sub>e\<^sub>m s = ((waiting s ->notEmpty' \<longrightarrow> (current s ->notEmpty)) \<and>
                        (last s ->notEmpty \<longrightarrow> 
                                (last s \<noteq> current s \<and>  (the(last s)) \<in> (waiting s))) \<and>
                        (current s ->notEmpty \<longrightarrow> (the(current s) \<notin>   (waiting s))))" 
thm inv\<^sub>S\<^sub>y\<^sub>s\<^sub>t\<^sub>e\<^sub>m_def


definition swap\<^sub>p\<^sub>o\<^sub>s\<^sub>t :: "System \<Rightarrow> System \<Rightarrow> Process \<Rightarrow> bool"
where    "(swap\<^sub>p\<^sub>o\<^sub>s\<^sub>t s\<^sub>p\<^sub>r\<^sub>e s res) = 
                  (((waiting s\<^sub>p\<^sub>r\<^sub>e) ->notEmpty' ) \<longrightarrow>
                  (let p =(if (last s ->notEmpty) \<and> waiting s\<^sub>p\<^sub>r\<^sub>e ->size() = 1
                           then ((waiting s\<^sub>p\<^sub>r\<^sub>e) ->excluding(the(last s\<^sub>p\<^sub>r\<^sub>e))) ->any(true)
                           else (waiting s\<^sub>p\<^sub>r\<^sub>e) ->any(true) )
                   in  res = p \<and> the(current s) = p   \<and> 
                       waiting s = waiting s\<^sub>p\<^sub>r\<^sub>e ->excluding(p) ->including(the(current s\<^sub>p\<^sub>r\<^sub>e))\<and> 
                       last s = current s\<^sub>p\<^sub>r\<^sub>e  ))"


section{* Test Generation *}
test_spec  "inv\<^sub>S\<^sub>y\<^sub>s\<^sub>t\<^sub>e\<^sub>m s\<^sub>p\<^sub>r\<^sub>e \<and>  swap\<^sub>p\<^sub>o\<^sub>s\<^sub>t s\<^sub>p\<^sub>r\<^sub>e s res  \<and> inv\<^sub>S\<^sub>y\<^sub>s\<^sub>t\<^sub>e\<^sub>m s"
nitpick
using[[goals_limit=40]]
unfolding swap\<^sub>p\<^sub>o\<^sub>s\<^sub>t_def inv\<^sub>S\<^sub>y\<^sub>s\<^sub>t\<^sub>e\<^sub>m_def Let_def
apply(gen_test_cases "res" "s")
(* apply(auto split:if_splits) *)
oops

text{* An interesting bug. TNF is not sufficient if we have just relational specifications.
       They MUST be rephrased as monadic system transitions: *}

definition swap\<^sub>p\<^sub>o\<^sub>s\<^sub>t' :: "System \<Rightarrow> (System \<times> Process) set"
where    "(swap\<^sub>p\<^sub>o\<^sub>s\<^sub>t' s\<^sub>p\<^sub>r\<^sub>e s res) = 
                  (let p =(if (last s ->notEmpty) \<and> waiting s\<^sub>p\<^sub>r\<^sub>e ->size() = 1
                           then ((waiting s\<^sub>p\<^sub>r\<^sub>e) ->excluding(the(last s\<^sub>p\<^sub>r\<^sub>e))) ->any(true)
                           else (waiting s\<^sub>p\<^sub>r\<^sub>e) ->any(true) )
                   in  res = p \<and> the(current s) = p   \<and> 
                       waiting s = waiting s\<^sub>p\<^sub>r\<^sub>e ->excluding(p) ->including(the(current s\<^sub>p\<^sub>r\<^sub>e))\<and> 
                       last s = current s\<^sub>p\<^sub>r\<^sub>e  )"


end
