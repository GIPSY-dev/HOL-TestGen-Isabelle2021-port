theory Interleaving
imports Main 
begin

(*
fun interleave :: "'a list => 'a list => 'a list set"
where "interleave [] [] = {[]}"
     |"interleave (A) [] = {A}"
     |"interleave [] B = {B}"  
     |"interleave (a#A)(b#B)  = (let S  = interleave A (b#B); 
                                     S' = interleave (a#A) (B) 
                                in (\<lambda> x. a # x) ` S \<union> (\<lambda> x. b # x) ` S')"  
*)

fun interleave :: "'a list => 'a list => 'a list set"
where  "interleave [] [] = {[]}"
     | "interleave (A) [] = {A}"
     | "interleave [] B = {B}"  
     |"interleave (a # A) (b # B) =
        (\<lambda>x. a # x) ` interleave A (b # B) \<union>
        (\<lambda>x. b # x) ` interleave (a # A) B"

find_theorems interleave

value"interleave [1::int,2,3] [11,12]"


fun interleave\<^sub>l\<^sub>i\<^sub>s\<^sub>t :: "'a list => 'a list => 'a list list"
where "interleave\<^sub>l\<^sub>i\<^sub>s\<^sub>t [] [] = [[]]"
     |"interleave\<^sub>l\<^sub>i\<^sub>s\<^sub>t (A) [] = [A]"
     |"interleave\<^sub>l\<^sub>i\<^sub>s\<^sub>t [] B = [B]"  
     |"interleave\<^sub>l\<^sub>i\<^sub>s\<^sub>t (a#A)(b#B)  = (let S  = interleave\<^sub>l\<^sub>i\<^sub>s\<^sub>t A (b#B); 
                                        S' = interleave\<^sub>l\<^sub>i\<^sub>s\<^sub>t (a#A) (B) 
                                   in   map (\<lambda> x. a # x)  S @  map (\<lambda> x. b # x)  S')"  


value "interleave' [1::int,2,1,2] [2,1]"
value "interleave [1::int,2] [1]"

(* Junk --- should be associativ application of interleave *)
fun interleave2 :: "'a list => 'a list => 'a list =>  'a list set"
where "interleave2 [] [] []  = {[]}"
     |"interleave2 (A) [] []  = {A}"
     |"interleave2 [] B  [] = {B}"
     |"interleave2 [] []  C = {C}"
     |"interleave2 (A)(B) []  = interleave A B"
     |"interleave2 (A)[] (C) = interleave A C"
     |"interleave2 [] B (C) = interleave B C"
     |"interleave2 (a#A)(b#B) (c#C)   = (let S  = interleave2 A (b#B) (c#C) ; 
                                     S' = interleave2 (a#A) (B) (c#C) ;
                                     S'' = interleave2 (a#A) (b#B) (C)  
                                in (\<lambda> x. a # x) ` ( S) \<union> (\<lambda> x. b # x) ` S' \<union> (\<lambda> x. c # x) ` S'')"

lemma replace : "interleave2 A B C = ((\<Union>x\<in>interleave A B. interleave X C))"
oops

(*
fun interleave1 :: "'a list => 'a list => 'a list => 'a list => 'a list set"
where "interleave1 [] [] [] [] = {[]}"
     |"interleave1 (A) [] [] [] = {A}"
     |"interleave1 [] B  [] []= {B}" 
     |"interleave1 [] []  C []= {C}"
     |"interleave1 [] []  [] D= {D}"
     |"interleave1 (A)(B) (C) []= interleave2 A B C"
     |"interleave1 (A)(B) [] D = interleave2 A B D"
     |"interleave1 (A)[] (C) D= interleave2 A C D"
     |"interleave1 [] B (C) D= interleave2 B C D"
     |"interleave1 (a#A)(b#B) (c#C) (d#D)  = (let S  = interleave1 A (b#B) (c#C) (d#D); 
                                     S' = interleave1 (a#A) (B) (c#C) (d#D);
                                     S'' = interleave1 (a#A) (b#B) (C) (d#D);
                                     S'''= interleave1 (a#A) (b#B) (c#C) (D)
                                in (\<lambda> x. a # x) ` S \<union> (\<lambda> x. b # x) ` S' \<union> (\<lambda> x. c # x) ` S'' \<union> (\<lambda> x. d # x) ` S''')"  

value "int(card(interleave1 [] []  [2::int,1,2,1] [1,2]))"
*)                             
fun bus_interleave :: " ('a::order) list \<Rightarrow> 'a list \<Rightarrow> 'a list set"
where "bus_interleave [] [] = {[]}"
     |"bus_interleave (A) [] = {A}"
     |"bus_interleave [] B = {B}"  
     |"bus_interleave (a#A)(b#B)  = 
         (if a \<le> b then (\<lambda> x. a # x) ` bus_interleave A (b#B)
          else if b \<le> a then (\<lambda> x. b # x) ` bus_interleave (a#A) (B) 
               else  (let S  = bus_interleave A (b#B); 
                          S' = bus_interleave (a#A) (B) 
                       in (\<lambda> x. a # x) ` S \<union> (\<lambda> x. b # x) ` S'))"  

fun sync_interleave :: "('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow>'a list \<Rightarrow> 'a list \<Rightarrow> 'a list set"
where "sync_interleave L S R [] [] = {[]}"
     |"sync_interleave L S R (A) [] = {A}"
     |"sync_interleave L S R [] B = {B}"  
     |"sync_interleave L S R (a#A)(b#B)  = 
         (if L a  \<and> \<not> L b then  sync_interleave L S R (A) (b#B)
          else if \<not> L a  \<and> L b then  sync_interleave L S R (a#A) (B) 
               else  
                  if L a  \<and> L b \<and> S a b then (\<lambda> x. a # x) ` sync_interleave L S R (A) (B) 
                 else (let IL  = sync_interleave L S R A (b#B); 
                           IL' = sync_interleave L S R (a#A) (B) 
                       in  (\<lambda> x. a # x) ` IL \<union> (\<lambda> x. b # x) ` IL'))" 

fun sync_interleave\<^sub>l\<^sub>i\<^sub>s\<^sub>t :: "'a \<Rightarrow>'a list \<Rightarrow> 'a list \<Rightarrow> 'a list list"
where "sync_interleave\<^sub>l\<^sub>i\<^sub>s\<^sub>t n [] [] = [[]]"
     |"sync_interleave\<^sub>l\<^sub>i\<^sub>s\<^sub>t n (A) [] = [A]"
     |"sync_interleave\<^sub>l\<^sub>i\<^sub>s\<^sub>t n [] B = [B]"  
     |"sync_interleave\<^sub>l\<^sub>i\<^sub>s\<^sub>t n (a#A)(b#B)  = 
         (if a = n  \<and> b \<noteq> n then  sync_interleave\<^sub>l\<^sub>i\<^sub>s\<^sub>t n (A) (b#B)
          else if a \<noteq> n  \<and> b = n then  sync_interleave\<^sub>l\<^sub>i\<^sub>s\<^sub>t n (a#A) (B) 
               else  
                  if a = n \<and> b= n then  map (\<lambda> x. n # x) (sync_interleave\<^sub>l\<^sub>i\<^sub>s\<^sub>t n (A) (B) )
                 else (let S  = sync_interleave\<^sub>l\<^sub>i\<^sub>s\<^sub>t  n A (b#B); 
                           S' = sync_interleave\<^sub>l\<^sub>i\<^sub>s\<^sub>t n (a#A) (B) 
                       in map (\<lambda> x. a # x)  S @ map (\<lambda> x. b # x)  S'))" 

value "((sync_interleave\<^sub>l\<^sub>i\<^sub>s\<^sub>t 2 [1::int,3,2 ] [1,2]))"



value "sync_interleave' 2 [1::int,3,2 ] [1,2]"

fun sync_interleave1 :: "'a list \<Rightarrow>'a list \<Rightarrow> 'a list \<Rightarrow> 'a list set"
where 
      "sync_interleave1 [] [] [] = {[]}"
     |"sync_interleave1 n [] [] = {[]}"
     |"sync_interleave1 [] A [] = {A}"
     |"sync_interleave1 [] [] B = {B}"
     |"sync_interleave1 n (A) [] = {A}"
     |"sync_interleave1 n [] B = {B}"
     |"sync_interleave1 [] A B = interleave A B"  
     |"sync_interleave1 (n#N) (a#A)(b#B)  = 
         (if a = n  \<and> b \<noteq> n then  sync_interleave1 (n#N) (A) (b#B)
          else if a \<noteq> n  \<and> b = n then  sync_interleave1 (n#N) (a#A) (B) 
               else  
                  if a = n \<and> b= n then (\<lambda> x. n # x) ` sync_interleave1 (n#N) (A) (B) 
                 else
                    (let S  = sync_interleave1 (n#N) A (b#B); 
                          S' = sync_interleave1 (n#N) (a#A) (B) 
                       in (\<lambda> x. a # x) ` S \<union> (\<lambda> x. b # x) ` S'))" 

value "((sync_interleave1 [1,3] [1::int,3,2 ] [1,2]))"
value "((sync_interleave1 [3,1] [1::int,3,2 ] [1,2]))"
value "(sync_interleave1 [3,1] [1::int,2 ] [1,3,2])"
                                
find_theorems " interleave"                                
value "int (card (interleave [1::int,2,3,4 ] [8,9,10,11]))"    

term" \<Union> X"


lemma "x \<in> set A \<Longrightarrow> x \<in> \<Union>(set ` interleave A B)"
proof (induct A B rule: interleave.induct)
  case 1
  then show ?case by simp
next
  case (2 a A)
  then show ?case by simp
next
  case (3 b B)
  then show ?case by simp
next
  case (4 a A b B)
  from 4 have "x \<in> \<Union>(set ` interleave (a # A) B)" by simp
  then show ?case by auto
qed


lemma commute1[simp]: "interleave A [] = interleave [] A" by(case_tac A, simp_all)

 
lemma interleave_commute'[rule_format]: "\<forall>B. interleave A B = interleave B A"
proof(induct A)
  show "\<forall>B. interleave [] B = interleave B []" by(simp)
next
  show "\<And>a A. \<forall>B. interleave A B = interleave B A \<Longrightarrow> \<forall>B. interleave (a # A) B = interleave B (a # A)"
  apply(rule allI,induct_tac B, simp_all) 
  apply(subst Set.Un_commute)
  apply (elim allE)
  apply (erule ssubst)+
  apply (simp only: triv_forall_equality) 
  done
qed


lemma interleave1 [simp] : "(x \<in> interleave [] A) = (x = A)"
by(induct A, simp_all only: interleave.simps, simp_all) 


lemma interleave2 [simp] : "(x \<in> interleave A []) = (x = A)"
by(induct A, simp_all only: interleave.simps, simp_all) 



lemma length_interleave_lemma: 
      "\<forall>n < k . length A + length B \<le> n
                    \<longrightarrow> (x::'a list) \<in> (interleave A B) 
                    \<longrightarrow> length x = (length A + length B)"
proof(induct k arbitrary: A B x)
   case 0 fix A::"'a list" and B::"'a list" and x::"'a list" 
        have *  : "\<And>A B. length A + length B \<le> 0 \<Longrightarrow> length A = 0" by auto
        have ** : "\<And>A B. length A + length B \<le> 0 \<Longrightarrow> length B = 0" by auto
        show "\<forall>n<0. length A + length B \<le> n 
                         \<longrightarrow> x \<in> interleave A B 
                         \<longrightarrow> length x = length A + length B"
        by auto
   case (Suc k)  fix A::"'a list" and B::"'a list" and x::"'a list" 
        assume H: "\<And>(A::'a list) B x. \<forall>n<k. length A + length B \<le> n 
                            \<longrightarrow> x \<in> interleave A B 
                            \<longrightarrow> length x = length A + length B"
        have   H': "\<And>(A::'a list) B x n. x \<in> interleave A B \<Longrightarrow> n<k \<Longrightarrow> length A + length B \<le> n 
                              \<Longrightarrow> length x = length A + length B"
                   by(erule H[THEN spec, THEN mp, THEN mp, THEN mp], auto)
                    
        show      "\<forall>n<Suc k. length A + length B \<le> n 
                                  \<longrightarrow> x \<in> interleave A B 
                                  \<longrightarrow> length x = length A + length B"
                  apply(case_tac "A", simp_all)
                  apply(case_tac "B", simp_all)
                  apply(auto)
                  apply(case_tac "n", simp_all)
                  apply(case_tac "list",auto)
                  apply(rule trans, erule H', auto)
                  apply(rule trans, erule H', auto)
                  apply(case_tac "n", simp_all)
                  apply(case_tac "list",auto)
                  apply(rule trans, erule H', auto)
                  apply(rule trans, erule H', auto)
                  done
qed


lemma length_interleave: "x \<in> (interleave A B) \<Longrightarrow> length x = (length A + length B)"
apply(rule length_interleave_lemma[rule_format, of "length A + length B" "length A + length B  + 1"])
by auto
  
 
lemma cardinality: "card(interleave A B) = ( length A  * length B + 1)" (* really ? *)
oops

lemma causality : 
      "\<forall> k i. i < k \<longrightarrow> (\<forall> C \<in> (interleave A B). (\<exists> l m. l < m \<and> A!i = C!l  \<and> A!k = C!m))" (* really ? *)
oops



end

