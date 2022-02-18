(**
 * Copyright (c) 2003-2010 Kara Abdul-Qadar, Matthias Daum, Dirk Leinenbach,
 * Hristo Pentchev, Elena Petrova, Mareike Schmidt, Alexandra Tsyban.
 * Some rights reserved, Saarland University.
 *
 * This work is licensed under the German-Jurisdiction Creative Commons
 * Attribution Non-commercial Share Alike 2.0 License.
 * See the file LIZENZ for a full copy of the license.
**)
(* $Id: MoreList.thy 31555 2010-08-31 11:50:09Z MareikeSchmidt $ *)

chapter {* Extensions to Isabelle/HOL's standard theory List *}

theory MoreList
imports Main

begin

subsection {* Definitions *}

text{* Two functions which are similar to @{const takeWhile} and @{const dropWhile},
       they cut the list not before an element but after it *}


definition replicate_list :: "nat \<Rightarrow> 'a list \<Rightarrow> 'a list"
where
  "replicate_list n l \<equiv> concat (replicate n l)"



text{* Function  @{text "extr"} extracts @{text "s"} elements from list  @{text "xs"} starting from position  @{text "i"} *}


definition  extr :: "nat \<Rightarrow> nat \<Rightarrow> 'a list \<Rightarrow> 'a list"
where
"extr i s xs \<equiv> take s (drop i xs)"

text {* Function @{text list_sum} sums up all elements in list @{text xs}. *}


definition list_sum::"'a list \<Rightarrow> ('a::{zero,plus})"
 where
 "list_sum xs == foldr op + xs 0"

lemma
  list_sum_Nil[simp]:  "list_sum [] = 0"
and
  list_sum_Cons[simp]: "list_sum (x#xs) = x + list_sum xs"
by (simp_all add: list_sum_def)

subsection {* Lemmata *}

subsubsection {* @{text list_sum} *}

lemma distinct_list_sum_set_eq:
  "distinct xs \<Longrightarrow> list_sum xs = \<Sum>(set xs)"
proof (induct xs)
qed simp_all

lemma list_sum_append:
 "list_sum (xs@ys) = list_sum (xs::'a::{comm_monoid_add} list) + list_sum ys"
proof -
  show ?thesis
  by (induct xs, simp_all add: add.assoc)
qed 

lemma list_sum_take_suc:
"n < length (xs::'a::{comm_monoid_add} list)  \<Longrightarrow> 
 list_sum (take (Suc n) xs) = list_sum (take n xs) + xs !n  "
proof -
qed(simp add: take_Suc_conv_app_nth list_sum_append)

lemma list_sum_drop_suc:
"n < length (xs::'a::{comm_monoid_add} list)  \<Longrightarrow> 
 list_sum (drop n xs) = list_sum (drop (Suc n) xs) + xs !n  "
proof -
qed (simp add: Cons_nth_drop_Suc[symmetric] add_ac)

lemma add_list_sum_take_drop:
 "n \<le> length (xs::'a::{comm_monoid_add} list) \<Longrightarrow>
  list_sum (take n xs) + list_sum(drop n xs) = list_sum xs"
by (simp add: list_sum_append[symmetric])

lemma list_sum_nat_mono:
 "n \<le> length (xs::nat list)
  \<Longrightarrow> list_sum (take n xs) \<le> list_sum xs"
by (simp add: add_list_sum_take_drop[symmetric])

lemma list_sum_nat_mono'[rule_format]:
  "\<forall>xs::nat list. list_sum (drop n xs) \<le> list_sum xs"
proof (induct n)
  case (Suc n) thus ?case
    apply clarsimp
    apply (case_tac xs, simp+)
    apply (erule_tac x=list in allE)
    by clarsimp
qed simp


lemma list_equality_ind: "! ys. length ys = length xs \<longrightarrow> (\<forall> i < length xs. xs ! i = ys ! i) \<longrightarrow> (xs = ys)"
apply (induct xs)
apply auto
apply (case_tac "ys")
apply simp
apply fastforce
done

lemma list_equality: "\<lbrakk>  (\<forall>i.  i < length xs \<longrightarrow> xs ! i = ys ! i ); length xs = length ys \<rbrakk> \<Longrightarrow> xs =ys"
apply (insert "list_equality_ind" [of xs])
apply auto
done

lemma not_eq_hd_tl[rule_format]: "a \<noteq> b \<longrightarrow> length a = length b \<longrightarrow> hd a = hd b \<longrightarrow> tl a \<noteq> tl b"
apply clarsimp
apply (case_tac a, simp)
apply (case_tac b, simp)
apply simp
done

subsubsection {* \textbf{remove1} *}
lemma in_set_remove1: "\<lbrakk>x\<noteq>y; x \<in> set xs\<rbrakk> \<Longrightarrow> x \<in> set (remove1 y xs)"
  by (induct xs) auto


subsubsection {* \textbf{rev} *}

lemma rev_Cons: "rev ls = x # xs \<Longrightarrow> ls = (rev xs) @ [x]"
apply (subgoal_tac "ls = rev (rev ls)")
apply simp
apply (simp (no_asm))
done

lemma rev_rev: "rev ps = xs \<Longrightarrow> ps = rev xs"
apply (subgoal_tac "ps = rev (rev ps)")
apply simp
by (simp (no_asm))

lemma last_rev_is_head: "ps \<noteq> [] \<Longrightarrow> last (rev ps) = hd ps"
by (case_tac ps) simp_all

lemma head_rev_is_last: "ps \<noteq> [] \<Longrightarrow> hd(rev ps) = last ps"
apply (case_tac "rev ps") 
apply simp_all
done

lemma rev_tl: "rev (tl xs) = take (length xs - Suc 0) (rev xs)"
apply (induct_tac xs)
 apply simp
apply clarsimp
done

lemma tl_rev: "tl (rev xs) = rev (take (length xs - Suc 0) xs)"
apply (induct_tac xs)
 apply simp
apply clarsimp
apply (simp add: take_Cons)
apply (simp split: nat.split)
apply clarsimp
apply (simp add: tl_append)
apply (simp split: list.split)
apply auto
done

subsubsection {* \textbf{last} *}

lemma last_in_list[rule_format]: "ls \<noteq> [] \<longrightarrow> last ls \<in> set ls"
by (induct_tac ls) simp_all


lemma list_eq_iff_nth_eq:
  "(xs = ys) = (length xs = length ys \<and> (\<forall>i<length xs. xs!i = ys!i))"
  (is "?list_eq ys = ?nth_eq ys")
proof -
  have "\<And>ys. ?nth_eq ys \<Longrightarrow> ?list_eq ys"
    proof (induct xs)
      case (Cons x xs) thus ?case by (cases ys, simp) fastforce
    qed fastforce
  thus ?thesis by auto
qed


subsubsection {* \textbf{map} *}

lemma map_element: "map f [x] = [f x]"
by simp

lemma last_map: "xs \<noteq> [] \<Longrightarrow> last (map P xs) = P (last xs)"
apply (induct xs)
by auto

lemma head_map: "xs \<noteq> [] \<Longrightarrow> hd (map P xs) = P (hd xs)"
apply (induct xs)
by auto

lemma tail_map: "xs \<noteq> [] \<Longrightarrow> tl (map P xs) = map P (tl xs)"
apply (induct xs)
by auto

lemma map_tail[rule_format]: "map f (tl xs) = tl (map f xs)"
apply (induct_tac xs)
by auto

lemma map_upt: "(map f [a+x..<b+x]) = (map (\<lambda>i. f (i+x)) [a..<b])"
  apply (clarsimp simp add: list_eq_iff_nth_eq nth_map_upt)
  apply (rule_tac f=f in arg_cong)
  apply (cut_tac i=a and j=b and k=i in nth_upt)
  apply  arith
  apply (cut_tac i="a+x" and j="b+x" and k=i in nth_upt)
  by  arith+

lemma map_in_set: "x \<in> set xs \<Longrightarrow> P x \<in> set (map P xs)"
apply auto
done

lemma in_set_map_impl_ex_in_list: "x \<in> set (map P xs) \<Longrightarrow> \<exists>r. r \<in> set xs \<and> P r = x"
apply auto
done

lemma in_map_set_impl_ex_in_list: " x \<in> P ` set xs \<Longrightarrow> \<exists>r. r \<in> set xs \<and> P r = x"
apply auto
done

lemma map_fst_zip [rule_format]: "\<forall>ys. length xs = length ys \<longrightarrow> map fst (zip xs ys) = xs"
apply (induct xs)
apply simp
apply (intro allI impI)
apply (case_tac ys)
apply simp_all
done

lemma map_set_equality: "\<forall>x. x \<in> set dl \<longrightarrow> f x = g x \<Longrightarrow> f  ` set dl = g  ` set dl"
apply (subgoal_tac "map f dl = map g dl")
apply (subgoal_tac "set (map f dl) = set (map g dl)")
apply simp
apply (erule ssubst)
apply simp
apply (rule map_ext)
apply simp
done

lemma map_set_equality_ball: "\<forall>x \<in> set dl.  f x = g x \<Longrightarrow> f  ` set dl = g  ` set dl"
apply (simp add: map_set_equality)
done
 
lemma not_in_list_impl_update_map_set_eq: "a \<notin> set dl \<Longrightarrow> f(a := x)  ` set dl = f  ` set dl"
apply auto
done

lemma not_in_list_impl_update_map_eq: "a \<notin> set dl \<Longrightarrow> map (f(a := x) ) dl = map f dl"
apply auto
done

lemma list_update_outside[rule_format]: "\<forall> i.  length l \<le> i \<longrightarrow> l [i := x] = l"
apply (induct_tac l)
 apply simp
apply clarsimp
apply (simp split: nat.split)
done

lemma list_update_commute :  "\<forall> i j xs . i \<noteq> j \<longrightarrow>  xs[i := a, j := b ] = xs[j := b, i := a] "
 apply clarsimp
 apply (cut_tac xs="xs[i := a, j := b ]" and ys="xs [j := b, i := a]" in  list_equality )
   apply(intro allI)
   apply(rule impI)
   apply clarsimp
   apply(case_tac "i \<ge> length xs ")
    apply(case_tac "j \<ge> length xs ") 
     apply simp
    apply simp 
   apply(case_tac "j \<ge> length xs ") 
    apply simp 
   apply(subst nth_list_update)
    apply simp
   apply(subst nth_list_update) 
    apply simp 
   apply(subst nth_list_update) 
    apply simp 
   apply(subst nth_list_update) 
    apply simp 
   apply simp 
  apply simp 
 apply(assumption)
done 

lemma is_in_map_fst: "(x,y) \<in> set xs \<Longrightarrow> x \<in> set (map fst xs)"
apply (induct xs)
apply (auto)
done

lemma length_map_fst: "n < length ls \<Longrightarrow> n < length (map fst ls)"
by simp

lemma map_all[rule_format]: "\<forall> l'. length l' = length l \<longrightarrow> (\<forall> i < length l. f (l'!i) = f(l!i) ) \<longrightarrow> map f l' = map f l"
apply (induct_tac l)
 apply simp
apply clarify
apply (rename_tac h t l')
apply (erule_tac x="tl l'" in allE)
apply clarsimp
 apply (case_tac l', simp, simp)
apply (rule conjI)
 apply (erule_tac x="0" in allE)
 apply clarsimp
 apply (case_tac "l'", simp, simp)
apply clarsimp
apply (erule_tac x="Suc i" in allE)
apply clarsimp
done

lemma map_compose2: "map f (map g xs) = map (f o g) xs"
apply (simp)
done

lemma map_rev: "map f (rev xs) = rev (map f xs)"
apply (simp add: rev_map)
done

lemma map_ext2[rule_format]: "\<forall> xs. length xs = length ys 
                               \<longrightarrow> (\<forall> i < length xs. f (xs!i) = f (ys!i))
                               \<longrightarrow> map f xs = map f ys"
apply (induct_tac ys)
 apply simp
apply clarify
apply (erule_tac x="tl xs" in allE)
apply clarsimp
apply (case_tac xs, simp)
apply clarsimp
apply force
done

subsubsection {* \textbf{nth} *}

lemma notin_set_conv_nth: "(\<forall>i<length xs. (xs ! i) \<noteq> x) = (x \<notin> set xs)"
by (auto simp add: set_conv_nth)

lemma nth_append_less_length: "i < length xs \<Longrightarrow> (xs @ ys) ! i = xs ! i"
by (simp add: nth_append)

text{* Instead of the lemma @{text list_is_head_and_tail}
 use @{text hd_Cons_tl} and symmetry rule *}

lemma list_eq_conv_nth_eq[rule_format]:
"xs = ys \<longrightarrow> i < length xs \<longrightarrow> xs ! i = ys ! i "
apply simp
done

text{* The next lemma has now the its conclusion rotated and is combined with
 the lemma @{text i_revD} *}
lemma rev_nth[rule_format]:
  " ! i. i < length xs \<longrightarrow>  rev xs ! (length xs - Suc i) = xs ! i"
apply (induct xs)
apply simp
apply (intro  allI impI)
apply (case_tac "xs = []")
apply (simp)
apply (case_tac "i ")
apply simp
apply (subgoal_tac "length xs = length (rev xs)")
apply (rotate_tac -1, erule ssubst)
apply (simp only: nth_append_length)
apply simp
apply (erule_tac x="nat" in allE)
apply simp
apply (simp add: nth_append)
done


lemma nth_rev[rule_format]: "n < length ls \<longrightarrow> ls ! (length ls - Suc n) = (rev ls) ! n"
apply (induct_tac ls)
 apply simp
apply simp
apply (intro impI)
apply (case_tac "n = length list")
 apply (simp add: nth_append)
apply (drule mp)
 apply simp
apply (simp add: nth_append)

done

text{* the next lemma is combined with the lemma @{text in_set_impl_exD} and
 the syntax in conclusion is changed *}

lemma in_set_impl_ex_nth[rule_format]:
  "x \<in> set ls \<longrightarrow> (\<exists> i < length ls. ls ! i = x)"
apply (induct ls)
 apply simp_all
apply (intro conjI impI)
 apply (rule_tac x = "0" in exI)
 apply simp
apply clarsimp
apply (rule_tac x = "Suc i" in exI)
apply simp
done

text{* The next lemma is combined with the lemma @{text Suc_i_less_lengthD} *}
lemma nth_is_not_last_impl_Suc_less_length[rule_format]:
  "\<forall>i.  xs ! i = x \<longrightarrow> x \<noteq> last xs \<longrightarrow> i < length xs \<longrightarrow>  Suc i < length xs"
apply (induct xs)
apply simp
apply (intro allI impI)
apply (case_tac "i")
apply (case_tac "xs = []")
apply simp
apply simp
apply (case_tac "xs = []")
apply simp
apply auto
done

text{* '1' is changed by 'Suc 0' *}
lemma last_nth_eq: "xs \<noteq> [] \<Longrightarrow> last xs = xs ! (length xs - Suc 0)"
apply (case_tac "rev xs")
apply simp
apply (drule rev_Cons)
apply simp
apply (subgoal_tac "length list = length (rev list)")
apply (erule ssubst)
apply (simp only: nth_append_length)
apply simp
done

lemma butlast_nth[rule_format]: "\<forall> i. Suc i < length xs \<longrightarrow> xs ! i = butlast xs ! i"
apply (induct_tac xs)
 apply simp
apply clarsimp
apply (erule_tac x="i - 1" in allE)
apply clarsimp
apply (simp add: nth_Cons)
apply (simp split: nat.split)
apply clarsimp
done

lemma list_all_butlast:"list_all f x \<longrightarrow> list_all f (butlast x)"
apply (induct x) 
apply simp+
done

subsubsection {* \textbf{hd} and \textbf{tl} *}

lemma hd_mem[rule_format]: "l \<noteq> [] \<longrightarrow> hd l \<in> set l"
  by (induct l) (auto)


lemma head_is_in_list: "ls \<noteq> [] \<Longrightarrow> hd ls \<in> set ls"
apply (drule hd_Cons_tl)
apply (erule subst)
apply simp
done

lemma hd_notin_list_imp_Nil[simp]: "(hd xs \<notin> set xs) = (xs = Nil)"
by (induct xs) auto

lemma head_is_0th: "xs \<noteq> [] \<Longrightarrow> hd xs = xs ! 0"
by (induct xs, auto)

lemma length_is_1_impl_list_is_head: " length xs = 1  \<Longrightarrow> xs = [hd xs] "
apply (induct xs)
apply auto
done

lemma length_is_1_impl_list_is_last: " length xs = 1  \<Longrightarrow> xs = [last xs] "
apply (induct xs)
apply auto
done

lemma length_is_1_impl_in_list_is_head: "\<lbrakk>  length xs = 1;  x \<in> set xs  \<rbrakk> \<Longrightarrow> x = hd xs"
apply (induct xs)
apply auto
done

lemma hd_tl[rule_format]:"ls\<noteq>[] \<longrightarrow> ls = hd ls # tl ls"
  apply (induct_tac ls)
  apply simp
  apply simp
done

lemma tail_nth: "xs \<noteq> [] \<Longrightarrow> (tl xs)! i = xs ! Suc i"
apply (insert hd_Cons_tl [of xs, THEN sym])
apply (simp del: hd_Cons_tl)
apply (erule ssubst)
apply (simp del: hd_Cons_tl)
done

subsubsection {* \textbf{zip} *}

lemma zip_tail: "zip (tl a) (tl b) = tl (zip a b)"
apply (case_tac a, simp)
apply (case_tac b, simp)
apply simp
done

lemma zip_Nil2[rule_format]: "zip a b = [] \<longrightarrow> a = [] \<or> b = []"
apply clarsimp
apply (case_tac a, simp)
apply (case_tac b, simp)
apply simp
done

lemma in_zip_impl_in_fst: "x \<in> set (zip xs ys) \<Longrightarrow> fst x \<in> set xs"
apply (simp add: set_zip)
by auto

lemma in_zip_impl_in_snd: "x \<in> set (zip xs ys) \<Longrightarrow> snd x \<in> set ys"
apply (simp add: set_zip)
by  auto

lemma zip_is_not_empty: "\<lbrakk> xs \<noteq> [] ; length xs = length ys\<rbrakk> \<Longrightarrow> zip xs ys \<noteq>[]"
apply (induct xs)
apply simp
apply (case_tac "ys")
by auto

lemma head_zip: "\<lbrakk> xs \<noteq> []; ys \<noteq> [] \<rbrakk> \<Longrightarrow> hd (zip xs ys) = (hd xs, hd ys)"
apply (induct xs)
apply simp
apply (case_tac "ys")
by auto

lemma second_eq_impl_zip_eq: "xs = ys \<Longrightarrow>  zip zs xs = zip zs ys"
by simp

lemma take_zip[rule_format]: "\<forall>xs ys. take n (zip xs ys) = zip (take n xs) (take n ys)"
apply (induct n)
apply  simp
apply (rule allI)+
apply (case_tac xs, simp)
apply (case_tac ys, simp_all)
done

lemma drop_zip: "\<forall> xs ys. drop n (zip xs ys) = zip (drop n xs) (drop n ys)"
apply (induct n)
apply  simp
apply (rule allI)+
apply (case_tac xs, simp)
apply (case_tac ys, simp_all)
done

lemma map_zip_commute: "\<forall> b. (\<forall> u v. f (u, v) = f (v, u)) \<longrightarrow> length a = length b \<longrightarrow> map f (zip a b) = map f (zip b a)"
apply (induct_tac a)
 apply simp
apply clarsimp
apply (case_tac b, simp)
apply clarsimp
done

subsubsection {* \textbf{distinct} *}

text {*
  Just a renamed version of distinct which prevents automatic simplification for concrete lists.
  *}

definition 
DISTINCT :: "'a list \<Rightarrow> bool"
where
  "DISTINCT ls \<equiv> distinct ls"

lemma DISTINCT_different[rule_format]: "DISTINCT ls \<longrightarrow> y \<in> set ls \<longrightarrow> x \<in> set (remove1 y ls) \<longrightarrow> x \<noteq> y"
apply (simp add: DISTINCT_def)
done

lemma DISTINCT_upd[rule_format]: "DISTINCT xs \<longrightarrow> x \<in> set xs \<longrightarrow> y \<in> set (remove1 x xs) \<longrightarrow> l [ y := z ] ! x = l!x "
apply (simp add: DISTINCT_def)
done

lemma distinct_rev: "distinct ps \<Longrightarrow> distinct (rev ps)"
by (induct ps) auto


lemma distinct_def:
  "distinct xs = (\<forall>i<length xs. \<forall>j<i. xs ! i \<noteq> xs ! j)"
apply (rule iffI)
apply (clarsimp simp add: List.distinct_conv_nth)+
apply (case_tac "j < i", simp)
apply (erule_tac x=j in allE, simp)
apply (erule_tac x=i in allE, simp)
done


lemma distinct_zip[rule_format]: "\<forall>ys. distinct xs \<longrightarrow>  distinct (zip xs ys)"
apply (induct xs)
apply simp
apply (intro allI impI)
apply (case_tac "ys")
apply simp
apply simp
apply (rule classical)
apply simp
apply (drule  in_zip_impl_in_fst)
apply simp
done

lemma distinct_rev_impl_distinct: "distinct (rev ps) \<Longrightarrow> distinct (ps)"
by (induct ps) auto

lemma distinct_map_impl_diff_map: "\<lbrakk> distinct (map P xs) ; x \<in> set xs;  y\<in> set xs; x \<noteq> y\<rbrakk> \<Longrightarrow> P x \<noteq> P y"
apply (drule in_set_impl_ex_nth)
apply (drule in_set_impl_ex_nth)
apply (elim exE conjE)
apply (simp add: distinct_conv_nth)
by auto

lemma distinct_map_impl_distinct: "distinct (map f xs) \<Longrightarrow> distinct xs"
apply (induct xs)
apply auto
done

lemma hd_is_mem[rule_format]: "s \<noteq> [] \<longrightarrow> hd s \<in> set s "
by (induct_tac s) ( simp_all)

lemma tl_distinct[rule_format]: "distinct l \<longrightarrow> distinct (tl l)"
apply (induct_tac l)
 apply simp
apply simp
done

lemma distinct_hd_tl[rule_format]: "distinct l \<longrightarrow> l \<noteq> [] \<longrightarrow> \<not> hd l : set (tl l) "
by(induct_tac l) (simp_all)

lemma distinct_hd_not_mem_x_tl[rule_format]: 
      "distinct l \<longrightarrow> l \<noteq> [] \<longrightarrow> \<not> r : set l \<longrightarrow> \<not> hd l : set (r#tl l)"
by  (induct l) auto


lemma not_mem_not_hd[rule_format]:"\<not> d : set ls \<longrightarrow> ls \<noteq> []  \<longrightarrow> d \<noteq> hd ls"
by  auto

lemma not_in_set_not_hd[rule_format]:"\<not> d \<in> set ls \<longrightarrow> ls \<noteq> []  \<longrightarrow> d \<noteq> hd ls"
  by auto

lemma not_mem_not_hd_tl[rule_format]:"\<not> d : set ls \<longrightarrow> ls \<noteq> [] \<longrightarrow> tl ls \<noteq> [] \<longrightarrow> d \<noteq> hd (tl ls)"
by (induct ls) auto

lemma not_in_set_not_hd_tl[rule_format]:"\<not> d \<in> set ls \<longrightarrow> ls \<noteq> [] \<longrightarrow> tl ls \<noteq> [] \<longrightarrow> d \<noteq> hd (tl ls) "
by (induct ls)(auto)


lemma not_mem_tl_not_mem[rule_format]:
      "\<not> d : set (tl ls) \<longrightarrow> distinct ls \<longrightarrow> d \<noteq> hd ls \<longrightarrow> ls \<noteq> [] \<longrightarrow> tl ls \<noteq> [] \<longrightarrow> \<not> d : set  ls"
by (induct ls)  auto

lemma not_mem_not_mem_tl[rule_format]:"\<not> d : set ls \<longrightarrow> ls \<noteq> [] \<longrightarrow> \<not> d : set  ls"
  apply clarsimp
done


lemma not_mem_l_not_mem_tl_plus[rule_format]: 
      "xs\<noteq>[] \<longrightarrow> ((\<not> (r : set (xs @ ys))) \<longrightarrow> ((\<not> (r : set (((tl xs)) @ ys)))) \<and> r \<noteq> (hd xs ))"
by (induct_tac "xs") auto


subsubsection {* \textbf{take} and \textbf{drop} *}

lemma Cons_nth_drop_Suc[rule_format]:
  "!i. i < length l --> l!i # drop (Suc i) l = drop i l"
  apply (induct l)
  apply  simp+
  apply clarsimp
  apply (case_tac i)
  apply  simp+
done

lemma drop_is_not_empty: "n < length ps \<Longrightarrow> drop n ps \<noteq> []"
  by auto

lemma drop_is_last: "xs \<noteq> [] \<Longrightarrow> drop (length xs - (1:: nat)) xs = [last xs]"
  apply (case_tac "rev xs")
  apply simp
  apply (drule rev_rev)
  apply (erule ssubst)
  apply simp
done


lemma drop_Suc_diff[rule_format]: "0 < n \<longrightarrow> drop (n - Suc 0) (tl l) = drop n l"
  apply (induct_tac l)
   apply simp
  apply clarsimp
  apply (case_tac n)
   apply clarsimp
  apply clarsimp
done

lemma take_is_not_last: "\<lbrakk> distinct xs; xs \<noteq> [] \<rbrakk>\<Longrightarrow> take (length xs - (1:: nat)) xs \<noteq> [last xs]"
  apply (case_tac "rev xs")
  apply simp
  apply (drule rev_rev)
  apply simp
  apply clarsimp
done

lemma last_is_not_in_take: "\<lbrakk> distinct xs; xs \<noteq> [] \<rbrakk>\<Longrightarrow> last xs \<notin> set (take (length xs - (1:: nat)) xs)"
  apply (case_tac "rev xs")
  apply simp
  apply (drule rev_rev)
  apply simp
done

lemma take_length_Cons: "xs \<noteq> [] \<Longrightarrow> take (length xs) (x # xs) = x # butlast xs"
  apply (case_tac "length xs")
   apply simp
  apply simp
  apply (subgoal_tac "take nat xs = take nat (butlast xs @ [last xs])")
   apply (rotate_tac -1)
   apply (erule ssubst)
   apply (simp only: take_append)
   apply simp
  apply simp
done

lemma butlast_take: "\<forall> xs. n < length xs \<longrightarrow> butlast (take (Suc n) xs) = take n xs"
  apply (induct_tac n)
   apply clarsimp
   apply (case_tac xs)
    apply simp
   apply (simp add: take_Suc)
  apply clarsimp
  apply (case_tac xs, simp)
  apply (subst take_Suc, simp)
  apply clarsimp
done

lemma take_update_same : " \<forall> i i1. i \<le> i1 \<longrightarrow> take i (xs[i1 := a]) = take i xs "
 apply(intro allI impI)
 apply(subgoal_tac "xs = take i xs @ drop i xs ")
  apply(rotate_tac -1, erule ssubst)
  apply(subst take_append)
  apply(subst list_update_append)
  apply (simp add: min_def)
 apply simp
done 

lemma drop_update_same : "  \<forall> i i1. i > i1 \<longrightarrow> i < length xs \<longrightarrow> drop i (xs[i1 := a]) = drop i xs"
 apply(intro allI impI)
 apply(subgoal_tac "xs = take i xs @ drop i xs ")
  apply(rotate_tac -1, erule ssubst)
  apply(subst drop_append)
  apply(subst list_update_append)
  apply (simp add: min_def)
 apply simp
done 

lemma drop_update_trans [rule_format]:  "\<forall> i l .  drop l (xs[l+i := a]) = (drop l xs)[i := a] "
apply( induct_tac xs )
  apply simp
 apply(intro allI)
 apply(case_tac "l") 
  apply simp 
 apply(rename_tac "la") 
 apply(case_tac "i") 
  apply simp 
  apply(erule_tac x="0" in allE)
  apply(erule_tac x="la" in allE) 
  apply simp 
 apply(rename_tac "ia") 
 apply simp 
 apply(erule_tac x="Suc ia" in allE) 
 apply(erule_tac x="la" in allE) 
 apply simp 
done 

lemma take_update_trans :  "\<forall> i l .  take l (xs[i := a]) = (take l xs)[i := a] "
apply( induct_tac xs )
  apply simp
 apply(intro allI)
 apply(case_tac "i")
 apply simp
  apply(case_tac "l") 
   apply simp 
 apply simp 
 apply(case_tac "l") 
 apply simp 
 apply simp 
done 

lemma take_2_append_take[rule_format]: 
      "k \<le> m \<longrightarrow> take m wx = take k wx @ take (m - k) (drop k wx)"
by (metis le_add_diff_inverse take_add)


lemma hd_take: "0 < i \<Longrightarrow> hd (take i wx) = hd wx"
by (metis Suc_pred hd_Cons_tl list.sel(1) take_Suc_Cons take_eq_Nil)


lemma drop_but_one_eq_nth_last_ind[rule_format]:
      "! wx. wx \<noteq> [] \<longrightarrow> wx = rev rx \<longrightarrow> drop (length wx - Suc 0) wx = [wx ! (length wx - Suc 0)]"
by (metis One_nat_def drop_is_last last_list_update list_update_id)


lemma drop_but_one_eq_nth_last:
      "wx \<noteq> [] \<Longrightarrow> drop (length wx - Suc 0) wx = [wx ! (length wx - Suc 0)]"
using drop_is_last last_nth_eq by fastforce

subsection {* \textbf{takeWhile} and \textbf{dropWhile} *}

lemma takeWhile_is_empty: "\<not> P (hd xs) \<Longrightarrow> takeWhile P xs =[]"
by (metis hd_tl takeWhile.simps(1) takeWhile.simps(2))

text{* the next lemma is combined with the lemma @{text takeWhile_emptyD} *}
lemma takeWhile_is_empty_impl_test_is_head[rule_format]:
  " a \<in> set xs \<longrightarrow> takeWhile (\<lambda>x. x \<noteq> a) xs = [] \<longrightarrow>  a = hd xs"
by (induct xs)(auto)


lemma takeWhile_is_butlast:
  "\<lbrakk> distinct xs ; xs = ys @ [y]\<rbrakk> \<Longrightarrow> takeWhile(\<lambda>x. x \<noteq> y) xs = ys"
  apply simp 
  apply (erule ssubst)
  apply (subgoal_tac "\<forall>x \<in> set ys. x \<noteq> y")
  apply fastforce+
done

lemma Suc_length_takeWhile_less_length:  
      "\<lbrakk> a \<noteq> last xs ; a \<in> set xs\<rbrakk> \<Longrightarrow> Suc (length (takeWhile(\<lambda>x. x \<noteq> a) xs)) < length xs"
  apply (induct xs)
  apply simp
  apply (case_tac "xs = []")
  apply simp
  apply auto
done

lemma length_takeWhile_less_length:  
      "a \<in> set xs \<Longrightarrow>  length (takeWhile(\<lambda>x. x \<noteq> a) xs) < length xs"
by (induct xs) auto


lemma takeWhile_take_eq: 
      "\<lbrakk> i < length ls ; distinct ls \<rbrakk>  \<Longrightarrow> takeWhile (\<lambda>x. x \<noteq> ls! i) ls = take i ls "
  apply (subgoal_tac "ls = ((take i ls) @ (ls ! i # drop (Suc i) ls))")
  apply (subgoal_tac "distinct ((take i ls) @ (ls ! i # drop (Suc i) ls))")
  apply (subgoal_tac "takeWhile (\<lambda>x. x \<noteq> ls ! i) (take i ls @ ls ! i # drop (Suc i) ls) = 
         take i ls")
  apply simp
  apply (thin_tac "ls = take i ls @ ls ! i # drop (Suc i) ls")
  apply simp
  apply (subgoal_tac "\<forall>x. x \<in> set (take i ls ) \<longrightarrow>  x \<noteq> (ls ! i)" )
  apply simp
  apply (intro allI impI )
  apply fastforce
  apply simp
  apply (subgoal_tac "ls ! i # drop (Suc i) ls = drop i ls ")
  apply (erule ssubst)
  apply simp
  apply (simp add: Cons_nth_drop_Suc )
done

lemma in_takeWhile_in_dropWhile_commute: 
      "\<lbrakk> distinct xs ; xa \<in> set (takeWhile (\<lambda>x. x \<noteq> ha) xs) ; ha \<in> set xs \<rbrakk> \<Longrightarrow>  
       ha \<in> set (dropWhile (\<lambda>x. x \<noteq> xa) xs)"
apply (simp add: in_set_conv_decomp)
apply (elim exE)
apply simp
apply (subgoal_tac "\<forall>x \<in> set ysa . x \<noteq> ha")
apply simp
apply (rule_tac x ="xa # zs" in exI)
apply (rule_tac x ="zsa" in exI)
apply simp
apply (elim conjE)
apply (subgoal_tac "\<forall>x \<in> set ys. x \<noteq> xa")
apply (simp)
apply fastforce
apply fastforce
done

lemma not_last_is_in_takeWhile: 
      "\<lbrakk> distinct xs ; x \<in> set xs ; x \<noteq> last xs \<rbrakk> \<Longrightarrow> x \<in> set (takeWhile (\<lambda>y. y \<noteq> last xs) xs)"
apply (case_tac "rev xs")
apply simp
apply (drule rev_Cons)
apply (frule takeWhile_is_butlast, assumption+)
apply simp
done


lemma distinct_takeWhile:
  "distinct xs \<Longrightarrow> distinct (takeWhile P xs)"
proof (induct xs)
  case (Cons x xs)
  thus ?case by (metis distinct_takeWhile) 
qed simp


lemma dropWhile_Cons_eq: 
" \<lbrakk>distinct xs ; xs = y#ys ;  x \<in> set xs ; x \<noteq> y \<rbrakk> \<Longrightarrow> 
  dropWhile (\<lambda>z. z \<noteq> x) xs = dropWhile (\<lambda>z. z \<noteq> x) ys"
apply (induct xs)
apply auto
done

lemma test_is_in_dropWhile: " ha \<in> set dl \<Longrightarrow> ha \<in> set (dropWhile (\<lambda>x. x \<noteq> ha) dl)"
apply (induct dl)
apply auto
done

lemma in_dropWhile_impl_in_list: "x \<in> set (dropWhile P xs) \<Longrightarrow> x \<in> set xs"
apply (induct xs)
by (auto split: if_split_asm)

lemma not_in_list_impl_not_in_dropWhile: "x \<notin> set xs \<Longrightarrow> x \<notin> set (dropWhile P xs)"
by (induct xs) auto

lemma dropWhile_not_hd[rule_format]: "\<forall>y ys. dropWhile P xs = y#ys \<longrightarrow> \<not>P y"
  by (induct xs) auto


subsubsection {* \textbf{take\_with} and \textbf{drop\_with} *}


text{* The next lemma is combined with the lemma
 @{text drop_with_rev_takeWhileD} *}

subsubsection {* : set *}

lemma not_mem_impl_not_in_set[rule_format]: "\<not> a : set ls \<longrightarrow> a \<notin> (set ls)"
by (induct_tac ls) simp_all

lemma mem_tl_is_mem[rule_format]: "l \<noteq> [] \<longrightarrow> x : set (tl l) \<longrightarrow> x : set l"
by (induct_tac l) simp_all

lemma mem_tl[rule_format]: "x : set (tl l) \<longrightarrow> x : set l"
by(induct_tac l) simp_all

lemma distinct_hd_not_mem_x_tl_tl[rule_format]: 
      "distinct l \<longrightarrow> 2 \<le> length l \<longrightarrow> \<not> r : set l \<longrightarrow> \<not> hd (tl l) : set (r#tl (tl l))"
apply (induct l )
apply simp_all
apply (metis One_nat_def distinct_hd_tl hd_notin_list_imp_Nil length_0_conv not_one_le_zero)
done

subsubsection {* \textbf{list\_all} *}

lemma list_all_rev_conv: "list_all P ls = (\<forall> x \<in> set (rev ls). P x)"
by (simp add: list_all_iff)

lemma list_all_but_last[rule_format]: "list_all p l \<longrightarrow> list_all p (butlast l)"
apply clarsimp
apply (simp add: list_all_iff)
apply clarsimp
apply (rename_tac x)
apply (drule_tac x="x" in bspec)
 apply (frule in_set_butlastD)
 apply simp
apply simp
done

lemma list_all_take[rule_format]: "list_all p l \<longrightarrow> n \<le> length l \<longrightarrow> list_all p (take n l)"
apply clarsimp
apply (simp add: list_all_iff)
apply clarsimp
apply (rename_tac x)
apply (drule_tac x="x" in bspec)
 apply (frule in_set_takeD)
 apply simp
apply simp
done

lemma list_all_nth[rule_format]: "(\<forall> i. i < length l \<longrightarrow> p (l!i)) \<longrightarrow> list_all p l"
apply clarsimp
apply (simp add: list_all_iff)
apply clarsimp
apply (frule all_nth_imp_all_set, simp)
apply simp
done

lemma list_all_eq_all_nth[rule_format]: "list_all p l = (\<forall> i. i < length l \<longrightarrow> p (l!i))"
apply (simp add: list_all_iff)
apply auto
apply (frule all_nth_imp_all_set, simp)
apply simp
done

lemma list_all_tl[rule_format]: "list_all P xs \<longrightarrow> list_all P (tl xs)"
apply clarsimp
apply (simp add: list_all_iff)
apply clarsimp
apply (rename_tac x)
apply (erule_tac x="x" in bspec)
apply (case_tac xs)
 apply simp
apply simp
done

subsubsection {* \textbf{filter} *}

lemma filter_tl: "P (hd xs) \<Longrightarrow> filter P (tl xs) = tl (filter P xs)"
by (induct xs) simp_all

lemma filter_equality: 
      "(\<forall> x \<in> set xs. P x = Q x) \<Longrightarrow> [x\<leftarrow>xs . P x] = [x\<leftarrow>xs . Q x]"
by(induct xs)auto

lemma filter_is_element_impl_deconstruction_of_list: 
      "[x\<leftarrow>ls. P x] = [a] \<Longrightarrow> [x\<leftarrow>(tl ls)@[hd ls]. P x] = [a]"
by (induct ls) auto

text{* Conclusion is rotated *}

lemma filter_dropWhile_equality: 
      "distinct xs \<Longrightarrow> [x\<leftarrow>xs. x \<in> set (dropWhile P xs)] = dropWhile P xs"
  apply (induct xs)
  apply simp
  apply (case_tac "P a")
  apply (simp_all add: not_in_list_impl_not_in_dropWhile)
done

lemma filter_take_le_filter : "length (filter P  (take n xs)) \<le> length (filter P xs )"
 apply (subgoal_tac " xs = take n xs @ drop n xs")
 apply (erule ssubst)
  apply (simp only: filter_append, simp)
 apply (simp add:  append_take_drop_id [THEN sym])
done


subsection {* \textbf{replicate} *}

lemma concat_replicate[simp]: "concat (replicate n [x]) = replicate n x"
  by (induct n) simp_all

lemma replicate_not_empty: 
  "0 < i \<Longrightarrow> replicate i x \<noteq> []"
  apply (insert length_replicate [of i x])
  apply fastforce
done

lemma replicate_decompose: 
  "k < n \<Longrightarrow> replicate n x = replicate (n - k) x @ replicate k x"
  apply (simp add: replicate_add [THEN sym])
done

lemma replicate_eq: 
  "n = k \<Longrightarrow> replicate n x = replicate k x"
  apply simp
done


lemma replicate_append_commute: 
  "replicate n x @ replicate k x = replicate k x @ replicate n x"
  apply (simp add: replicate_add [THEN sym])
done

(* The lemmas take_replicate and drop_replicate can now be found in Isabelle's
 List.thy. *)

lemma replicate_suc[rule_format]:
  "replicate x a @ xs  = ls \<longrightarrow> replicate (Suc x) a @ xs = a # ls"
by clarsimp

(* The lemma replicate_append can now be found in Isabelle's List.thy as replicate_add[THEN sym]. *)

lemma append_equal_replicate[rule_format]: 
  "! n. m \<le> n \<longrightarrow> (replicate m b @ xs = replicate n b) = (xs = replicate (n - m) b)"
  apply (induct m)
   apply simp_all
  apply (intro allI impI)
  apply (case_tac n, simp)
  apply (erule_tac x = "nat" in allE)
  apply simp
done

lemma replicate_Suc': 
  "replicate k a @ [a] = replicate (Suc k) a"
  apply (induct_tac k)
   apply simp
  apply simp
done

lemma forall_replicate_conv [rule_format]:
  "(\<forall>x\<in>set list. x=a ) \<longrightarrow> list = replicate (length list) a"
  apply (induct_tac "list")
   apply simp
  apply simp
done

subsection {* \textbf{replicate\_list} *}

lemma length_replicate_list[simp]: "length (replicate_list n x) = n * length x"
  by (induct n, (simp add: replicate_list_def)+)

lemma nth_replicate_list[rule_format]:
  "!i. i < k * length l \<longrightarrow> replicate_list k l ! i = l!(i mod length l)"
  apply (induct k)
   apply simp
  apply (simp add: replicate_list_def)
  apply (simp add: nth_append)
  apply clarsimp
  apply (erule_tac x="i - length l" in allE)
  apply (subgoal_tac "i - length l < k * length l", simp)
   apply (subgoal_tac "(i - length l) mod length l = i mod length l", simp)
   apply (simp add: mod_geq)
  apply arith
done

lemma replicate_list_0[simp]: 
  "replicate_list 0 l = Nil"
by (simp add: replicate_list_def)

lemma replicate_list_Suc: 
  "replicate_list (Suc n) l = l @ (replicate_list n l)"
by (simp add: replicate_list_def)

lemma replicate_list_Suc_0[simp]: 
  "replicate_list (Suc 0) l = l"
by (simp add: replicate_list_Suc)


text{* \textbf{foldl} *}

lemma add_start_foldl_sum:
  "!!(y::'a::semigroup_add).
   x + foldl op + y xs = foldl op + (x+y) xs"
proof (induct xs)
qed (simp_all add: add.assoc)

lemma "foldl op + (0::'a::{ab_semigroup_add, zero}) xs = foldr op + xs 0"
proof (induct xs)
  case (Cons x xs) note calculation = this
  moreover
  have "0 + x = x + 0" by (rule add.commute)
  ultimately
  show ?case by (simp add: add_start_foldl_sum[symmetric])
qed simp

lemma foldl_sum_non_zero_base[rule_format]: "! a. foldl op + a ls = a + foldl op + (0::nat) ls"
apply (induct_tac ls)
 apply simp
apply (rule allI)
apply (simp (no_asm))
apply (frule_tac x = "a" in allE)
 apply (rotate_tac -1, assumption)
apply (erule ssubst)
apply (erule_tac x = "aa + a" in allE)
apply simp
done

text{* \textbf{foldr} *}


subsection{* \textbf{extr} *}

lemma extr_update_id[rule_format]:
"i + n \<le> k \<longrightarrow> extr i n (h[k := v]) = extr i n h"
apply (case_tac "k < length h")
 apply (clarsimp simp add: extr_def)
 apply (subgoal_tac "h = take i h @ (take n (drop i h) @ drop n (drop i h))")
  apply (simp del: append_take_drop_id)
  apply (erule ssubst)
  apply (simp add: list_update_append min_def)
  apply (subgoal_tac "n \<le> k - i")
   apply simp
 apply (metis append_take_drop_id drop_drop)
  apply arith
 apply simp
done

lemma extr_empty: "extr i 0 xs = []"
by (simp add: extr_def)

lemma extr_Suc_conv_append_nth: 
"i + s < length xs \<Longrightarrow> extr i (Suc s) xs = extr i s xs @ [xs!(i + s)]"
 apply (simp add: extr_def)
 apply (subst take_Suc_conv_app_nth)
  apply simp
 apply simp
done

lemma extr_update_id2[rule_format]:
  "k < i\<longrightarrow> extr i n (h[k := v]) = extr i n h"
  by (clarsimp simp add: extr_def)


lemma extr_update_nth:
  "\<lbrakk> n < s; i + n < length xs\<rbrakk> \<Longrightarrow> extr i s (xs[i + n := nv]) ! n = nv"
  by (simp add: extr_def)

lemma extr_update:
"\<lbrakk> n < s; i + n < length xs \<rbrakk> \<Longrightarrow>  extr i s (xs[i + n := nv]) = (extr i s xs) [n := nv]"
 apply (simp add: extr_def)
 apply (subgoal_tac "xs[i + n := nv] = (take i xs @ drop i xs)[i + n := nv]")
  apply (erule ssubst)
  apply (simp del: append_take_drop_id add: list_update_append min_def)
  apply (subgoal_tac "drop i xs = take s (drop i xs) @ drop s (drop i xs)")
   apply (erule ssubst)
   apply (simp del: append_take_drop_id add: list_update_append min_def)
  apply (simp only: append_take_drop_id)
 apply simp
done


lemma extr_length: 
"i + s \<le> length m \<Longrightarrow> length (extr i s m) = s"
 apply (simp add: extr_def min_def)
 apply arith
done

lemma extr_nth[rule_format]: 
"n < s \<longrightarrow> i + n < length mm \<longrightarrow> (extr i s mm)! n = mm !(i + n)"
 apply (simp add: extr_def)
done

lemma extr_Suc: 
"i + s < length xs \<Longrightarrow> extr i (Suc s) xs = (xs ! i) # extr (Suc i) s xs "
 apply (simp add: extr_def)
 apply (subst Cons_nth_drop_Suc[THEN sym])
  apply simp
 apply simp
done 

lemma extr_extr : " extr i0 s0 (extr i1 s1 xs ) = extr (i0+i1) (min s0 (s1 - i0)) xs "
 apply (simp only:  extr_def )
 apply(subst drop_take)
 apply(subst drop_drop)
 apply(subst take_take) 
 apply(rule refl)
done 

lemma extr_eq_impl_less_extr_eq[rule_format]:
" extr i (n + ofs) H = extr j (n + ofs) H'\<longrightarrow>
  extr (i + ofs) n H = extr (j + ofs) n H'" 
 apply (simp add: extr_def)
 apply (intro impI)
 apply (subst add.commute)
 apply (rule sym)
 apply (subst add.commute)
 apply (subst drop_drop[THEN sym])
 apply (subst drop_drop[THEN sym])

 apply (subst take_drop)
 apply (rule sym)
 apply (subst take_drop)
 apply simp
done

lemma extr_append_inverse :"length xs \<le> i \<longrightarrow> extr i s (xs @ ys ) = extr (i-length(xs)) s ys"
 apply(intro impI)
 apply(simp add: extr_def)
done   

lemma extr_append_twice :"
length xs = i \<longrightarrow> length ys = s \<longrightarrow> extr i s (xs @ ys @ zs) = extr 0 s ys"
 apply(intro impI)
 apply(simp add: extr_def)
done   

lemma extr_append: "\<lbrakk>ln + lnt + i \<le> length xs\<rbrakk> \<Longrightarrow> extr i ln xs @ extr (i+ln) lnt xs = extr i (ln+lnt) xs "
 apply (simp add: extr_def)
 apply (subst take_add)
 apply (subst drop_drop)
 apply (subst add.commute)
 apply (rule refl)
done

subsection{* \textbf{concat} *}

lemma length_concat [rule_format]:
"\<forall> ln . (\<forall>i < length xs. length (xs ! i)  = ln )\<longrightarrow>
 length (concat  xs ) = length xs * ln "
 apply(induct_tac xs)
  apply simp
 apply(intro allI impI)
 apply simp
 apply(case_tac "length list = 0")
  apply simp
 apply(erule_tac x="ln" in allE) 
 apply(drule mp)
  apply(intro allI)
  apply(rule impI)
  apply(erule_tac x="Suc i" in allE) 
  apply simp
 apply simp
 apply(erule_tac x="0" in allE) 
 apply(drule mp)
  apply simp
 apply simp 
done 

lemma length_concat_take [rule_format]:
" \<forall> n. n < length xs \<longrightarrow>
 (\<forall>i < length xs. length (xs ! i)  = ln )\<longrightarrow>
 length (concat (take n xs )) = n * ln "
 apply(intro allI impI)
 apply(subst length_concat [where ln="ln"])
  apply simp
 apply(subst length_take)
 apply (simp add: min_def)
done 

end
