(**
 * Copyright (c) 2004-2008 Matthias Daum, Thomas In der Rieden,
 * Dirk Leinenbach, Hristo Pentchev, Mareike Schmidt, Alexandra Tsyban.
 * Some rights reserved, Saarland University.
 *
 * This work is licensed under the German-Jurisdiction Creative Commons
 * Attribution Non-commercial Share Alike 2.0 License.
 * See the file LIZENZ for a full copy of the license.
**)
(* $Id: Memory.thy 28413 2009-06-15 18:23:35Z MatthiasDaum $ *)
chapter {* Memory Access *}

theory Memory imports Instr_convert Range begin

definition cell2data :: "mem_cell_t \<Rightarrow> int"
where     "cell2data x \<equiv> x"

definition data2cell :: "int \<Rightarrow> mem_cell_t"
where     "data2cell x \<equiv> x"

lemma data2cell2data:
  shows "cell2data (data2cell ls) = ls"
by (auto simp add: cell2data_def data2cell_def)

lemma cell2data2cell:
  shows "data2cell (cell2data mc) = mc"
by (auto simp add: cell2data_def data2cell_def)

definition   cell2instr :: "mem_cell_t \<Rightarrow> instr"
where
"cell2instr m \<equiv> int_to_instr (cell2data m)"

definition  instr2cell :: "instr \<Rightarrow> mem_cell_t"
where
"instr2cell i \<equiv> data2cell (instr_to_int i)"

lemma instr2cell2instr: "is_instr iw \<Longrightarrow> cell2instr (instr2cell iw) = iw"
apply (simp add: cell2instr_def instr2cell_def)
apply (simp add: data2cell2data)
apply (erule instr_to_int_to_instr)
done

lemma instr2cell2instr_list[rule_format]: "is_asm_prog ls \<longrightarrow> map cell2instr (map instr2cell ls) = ls"
apply (induct_tac ls)
apply (simp add: is_asm_prog_def instr2cell2instr)+
done

definition instr_mem_read :: "[mem_t, nat] \<Rightarrow> instr"
where     "instr_mem_read mm ad == cell2instr (mm (ad div 4))"

definition data_mem_read :: "[mem_t, nat] \<Rightarrow> int"
where     "data_mem_read mm ad == cell2data (mm (ad div 4))"

definition data_mem_write :: "[mem_t, nat, int] \<Rightarrow> mem_t"
where
  "data_mem_write mm ad data == mm ((ad div 4) := data2cell (data))"

text
{*
   gets the sequence of memory cells of length @{text len} starting from address @{text ad}
*}

primrec mem_part_word_access :: "[mem_t, nat, nat] \<Rightarrow> mem_cell_t list"
where
"mem_part_word_access memory ad 0 = []"
 | "mem_part_word_access memory ad (Suc n) = [memory ad] @ (mem_part_word_access memory (Suc ad) n)"

definition mem_part_access :: "[mem_t, nat, nat] \<Rightarrow> mem_cell_t list"
where
"mem_part_access memory ad len == mem_part_word_access memory (ad div 4) (len div 4)"

definition 
  data_mem_read_region :: "mem_t \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> int list"
where
  "data_mem_read_region m sa am \<equiv> map cell2data (mem_part_word_access m (sa div 4) am)"

definition mem_unchanged_word :: "mem_t \<Rightarrow> mem_t \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool"
where 
"mem_unchanged_word m m' a b \<equiv> (\<forall> i. a \<le> i \<and> i < b \<longrightarrow> m' i = m i)"

definition mem_unchanged :: "mem_t \<Rightarrow> mem_t \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool"
where 
"mem_unchanged m m' a b \<equiv> mem_unchanged_word m m' (a div 4) (b div 4)"

text {*
  Memory has only been changed inside a certain region
  *}

definition  mem_part_changed_word:: "mem_t \<Rightarrow> mem_t \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool"
where
"mem_part_changed_word m m' a l \<equiv> (\<forall> i. i < a \<or> a + l \<le> i \<longrightarrow> m' i = m i)"

lemma length_word_access[rule_format]: "! add. length (mem_part_word_access memory add len) = len"
by (induct len) simp_all

lemma length_access: "length (mem_part_access memory add len) = (len div 4)"
by (simp add: mem_part_access_def length_word_access)

lemma word_access_not_empty[rule_format]: "0 < l \<longrightarrow> mem_part_word_access m a l \<noteq> []"
apply (induct l)
  apply simp
apply clarsimp
done

lemma word_access_content[rule_format]: "! ad i. i < len \<longrightarrow> (mem_part_word_access memory ad len) ! i = memory (ad + i)"
apply (induct len)
 apply simp
apply clarsimp
apply (case_tac i)
apply simp_all
done

lemma access_content: "i < (len div 4) \<Longrightarrow> (mem_part_access memory ad len) ! i = memory (ad div 4 + i) "
by (simp add: mem_part_access_def word_access_content)

lemma mem_part_word_access_update[rule_format]: "! st. st + len \<le> ad \<longrightarrow> 
            mem_part_word_access ((mm d)(ad := val)) st len = mem_part_word_access (mm d) st len"
apply (induct_tac len)
 apply simp
apply (intro allI impI)
apply simp
done

lemma mem_part_word_access_head[rule_format]: "mem_part_word_access m b l = h#t \<longrightarrow> m b = h"
apply (induct_tac l)
  apply simp
apply simp
done

lemma mem_part_word_access_tail[rule_format]: "mem_part_word_access m b l = h#t \<longrightarrow> mem_part_word_access m (Suc b) (l - Suc 0) = t"
apply (induct_tac l)
  apply simp
apply simp
done

lemma mem_part_word_access_take1[rule_format]: "\<forall> b l. i \<le> l \<longrightarrow> take i (mem_part_word_access m b l) = take i (mem_part_word_access m b (l + x))"
apply (induct_tac i)
  apply simp
apply clarsimp
apply (case_tac "mem_part_word_access m b l")
  apply clarsimp
  apply (subgoal_tac "length (mem_part_word_access m b l)=l")
    apply simp
  apply (frule_tac memory="m" and len="l" and add="b" in length_word_access)
apply (case_tac "mem_part_word_access m b (l+x)")
  apply clarsimp
  apply (subgoal_tac "length (mem_part_word_access m b (l+x))=l+x")
    apply simp
  apply (frule_tac memory="m" and len="l+x" and add="b" in length_word_access)
apply simp
apply (erule_tac x="Suc b" in allE)
apply (erule_tac x="l - 1" in allE)
apply simp
apply (subgoal_tac "mem_part_word_access m (Suc b) (l - 1) = list")
  apply (subgoal_tac "mem_part_word_access m (Suc b) (l + x - 1) = lista")
    apply (subgoal_tac "n \<le> l - 1")
	   apply clarsimp
		apply (subgoal_tac "m b=a")
		  apply clarsimp
		  apply (simp add: mem_part_word_access_head)
		apply (simp add: mem_part_word_access_head)
	 apply arith
  apply clarsimp
  apply (frule_tac m="m" and b="b" and l="l+x" and h="aa" and t="lista" in mem_part_word_access_tail)
  apply simp
apply (frule_tac m="m" and b="b" and l="l" and h="a" and t="list" in mem_part_word_access_tail)
apply simp
done

lemma mem_part_word_access_take2[rule_format]: "\<forall> b. i \<le> l \<longrightarrow> mem_part_word_access m b i = take i (mem_part_word_access m b l)"
apply clarsimp
apply (subgoal_tac "mem_part_word_access m b i = take i (mem_part_word_access m b i)")
  apply (subgoal_tac "i \<le> i")
    apply (frule_tac m="m" and b="b" and i="i" and l="i" and x="l - i" in mem_part_word_access_take1)
	 apply clarsimp
  apply simp
apply (simp add: length_word_access)
done

lemma mem_part_word_access_append[rule_format]: "mem_part_word_access m base l = a@b \<longrightarrow> mem_part_word_access m base (length a) = a"
apply clarsimp
apply (subgoal_tac "length a \<le> l")
  apply (frule_tac m="m" and b="base" and l="l" and i="length a" in mem_part_word_access_take2)
  apply clarsimp
apply (subgoal_tac "length (a@b) = l")
  apply simp
apply (insert length_word_access[where memory="m" and add="base" and len="l"])
apply simp
done

lemma mem_part_word_access_drop[rule_format]: "i \<le> l \<longrightarrow> mem_part_word_access m (b + i) ( l - i) = drop i (mem_part_word_access m b l)"
apply (induct_tac i)
  apply simp
apply clarsimp
apply (case_tac "mem_part_word_access m (b + n) (l - n)")
  apply clarsimp
  apply (subgoal_tac "l - n = 0")
    apply simp
  apply (simp add: word_access_not_empty)
apply (subgoal_tac "mem_part_word_access m (Suc (b + n)) (l - Suc n)=tl (mem_part_word_access m (b + n) (l - n))")
  apply clarsimp
  apply (simp add: drop_Suc)
  apply (simp add: drop_tl)
apply (frule mem_part_word_access_tail)
apply simp
apply (subgoal_tac "tl (a#list) =list")
  apply simp
apply (simp (no_asm))
done

lemma mem_part_word_access_append2[rule_format]: "\<forall> base. mem_part_word_access m base l = a@b \<longrightarrow> mem_part_word_access m (base + length a) (length b) = b"
apply clarsimp
apply (case_tac b)
  apply clarsimp
apply (subgoal_tac "length b = l - length a")
  apply (subgoal_tac "mem_part_word_access m (base + length a) (length b) = drop (length a) a@b")
    apply simp
  apply clarsimp
  apply (subgoal_tac "length a < l")
    apply (simp add: mem_part_word_access_drop)
  apply arith
apply clarsimp
apply (subgoal_tac "length (mem_part_word_access m base l) = l")
  apply simp

apply (frule length_word_access)
done

lemma mem_part_word_access_add: "! add . mem_part_word_access m add (a+b) = (mem_part_word_access m add a) @ (mem_part_word_access m (add + a) b)"
apply (induct a)
 apply simp
apply (rule allI)
apply (erule_tac x="Suc add" in allE)
apply simp
done

lemma mem_part_word_access_Suc_def: "mem_part_word_access m st_ad (Suc n) = m st_ad # mem_part_word_access m (Suc st_ad) n"
apply simp
done

lemma mem_part_word_access_Suc[rule_format]:
    "! st_ad. mem_part_word_access m st_ad (Suc n) = mem_part_word_access m st_ad n @ mem_part_word_access m (st_ad + n) 1"
apply (induct_tac n)
 apply simp
apply (intro allI)
apply (rule sym)
apply (subst mem_part_word_access_Suc_def)
apply (rule sym)
apply (erule_tac x = "Suc st_ad" in allE)
apply clarsimp
done

lemma mem_part_access_Suc_def: "mem_part_access m st_ad (4 * (Suc n)) = m (st_ad div 4) # mem_part_access m (st_ad + 4) (4 * n)"
apply (simp add: mem_part_access_def)
  by (simp add: dvd_div_add1)

lemma mem_part_access_Suc[rule_format]:
    "! st_ad. mem_part_access m st_ad (4 * (Suc n)) = mem_part_access m st_ad (4 * n) @ mem_part_access m (st_ad + 4 * n) 4"
apply (induct_tac n)
 apply (simp add: mem_part_access_def)
apply (intro allI)
apply (rule sym)
apply (subst mem_part_access_Suc_def)
apply (rule sym)
apply (erule_tac x = "st_ad + 4" in allE)
apply (subst mem_part_access_Suc_def)
apply clarsimp
apply (subst add.assoc)
apply simp
done

lemma mem_cell_eq': 
      "\<lbrakk> mem_part_access mm' 0 border = mem_part_access mm 0 border;
         dpc' = dpc + 4 * n; 
         dpc + 4 * (Suc n) \<le> border \<rbrakk>
     \<Longrightarrow> mm' (n + dpc div 4) = mm (n + dpc div 4)"
apply (subgoal_tac "n + dpc div 4 < border div 4")
 prefer 2
 apply (subgoal_tac "\<exists> k. border = dpc + (4 + 4 * n) + k")
  apply (erule exE)
  apply simp
 apply (rule_tac x = "border - (dpc + (4 + 4 * n))" in exI)
 apply simp
apply (frule_tac ad = "0" and memory = "mm" in access_content)
apply (drule_tac ad = "0" and memory = "mm'" in access_content)
apply simp
done

lemma mem_cell_eq:
      "\<lbrakk> mem_part_access mm' (4 * low_border_words) code_size = mem_part_access mm (4 * low_border_words) code_size;
         dpc' = dpc + 4 * n;
         4 * low_border_words \<le> dpc;
         dpc + 4 * (Suc n) \<le> 4 * low_border_words + code_size \<rbrakk>
     \<Longrightarrow> mm' (n + dpc div 4) = mm (n + dpc div 4)"
apply (subgoal_tac "n + dpc div 4 - low_border_words < code_size div 4 \<and> low_border_words \<le> n + dpc div 4")
 prefer 2
 apply (subgoal_tac "\<exists> q. dpc = 4 * low_border_words + q")
  prefer 2
  apply (rule_tac x = "dpc - 4 * low_border_words" in exI)
  apply simp
 apply (erule exE)
 apply simp   
apply (erule conjE)
apply (frule_tac ad = "4 * low_border_words" and memory = "mm" in access_content)
apply (drule_tac ad = "4 * low_border_words" and memory = "mm'" in access_content)
apply simp
done

definition get_instr_list :: "mem_t \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> instr list"
where
"get_instr_list m ad l \<equiv> map cell2instr (mem_part_word_access m (ad div 4) l)"

definition  get_data_list :: "mem_t \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> int list"
where
"get_data_list m ad l \<equiv> map cell2data (mem_part_word_access m (ad div 4) l)"

lemma length_get_instr_list: "length (get_instr_list m ad len) = len"
apply (simp add: get_instr_list_def)
apply (simp add: length_word_access)
done

lemma length_get_data_list[rule_format]:
      "! ad. length (get_data_list m ad len) = len"
apply (induct len)
 apply (simp add: get_data_list_def)
apply (intro allI impI)
apply (erule_tac x = "ad + 4" in allE)
apply (simp add: get_data_list_def)
  using length_word_access by blast

(* TODO move *)
lemma map_result_append: 
     "map f l = x@y \<Longrightarrow> 
      \<exists> l1 l2. l = l1 @ l2 \<and> length l1 = length x \<and> length l2 = length y"
apply (rule_tac x = "take (length x) l" in exI)
apply (rule_tac x = "drop (length x) l" in exI)
apply (simp add: append_take_drop_id)
apply (insert length_map[of f l, THEN sym])
apply (simp add: min_def)
done

lemma get_instr_list_add : 
      "get_instr_list m ad (a + b) = 
       (get_instr_list m ad a) @ (get_instr_list m (ad + 4 * a) b)"
  apply (simp add: get_instr_list_def) 
  apply (simp add: mem_part_word_access_add)  
  apply (simp add: add.commute)
done

lemma get_instr_list_append: 
   "get_instr_list m a l = x@y \<Longrightarrow>
    \<exists> l1 l2. mem_part_word_access m (a div 4) l = (l1 @ l2) \<and> 
    length l1 = length x \<and> length l2 = length y"
apply (simp add: get_instr_list_def)
apply (frule_tac f = "cell2instr" and 
                 l = "(mem_part_word_access m (a div (4::nat)) l)" in map_result_append)
apply (elim exE)
apply (rule_tac x = "l1" in exI)
apply (rule_tac x = "l2" in exI)
apply simp
done

lemma get_instr_list_append1: 
     "get_instr_list m a (length(x@y)) = x@y \<Longrightarrow> 
      get_instr_list m a (length x) = x "
apply (frule get_instr_list_append)
apply (simp only: get_instr_list_def)
apply (elim exE conjE)
apply (frule mem_part_word_access_append)
apply simp
done

lemma get_instr_list_empty[rule_format]: 
      "get_instr_list m b 0 = []"
apply (simp add: get_instr_list_def)
done

lemma get_instr_list_drop[rule_format]: 
      "i \<le> l \<longrightarrow> get_instr_list m (b + 4 * i) (l - i) = drop i (get_instr_list m b l)"
apply clarsimp
apply (simp add: get_instr_list_def)
apply (simp add: drop_map)
apply (subgoal_tac "mem_part_word_access m (i + b div 4) (l - i) = drop i (mem_part_word_access m (b div 4) l)") 
  apply simp
apply (frule_tac i="i" and l="l" and m="m" and b="b div 4" in mem_part_word_access_drop)
apply (subgoal_tac "b div 4 + i = i + b div 4")
  apply simp
apply simp
done

lemma get_instr_list_take1[rule_format]: 
     "i \<le> l \<longrightarrow> take i (get_instr_list m b l) = 
                take i (get_instr_list m b (l + x))"
apply clarsimp
apply (simp add: get_instr_list_def)
apply (simp add: take_map)
apply (subgoal_tac "take i (mem_part_word_access m (b div 4) l) = take i (mem_part_word_access m (b div 4) (l + x))")
  apply clarsimp
apply (simp add: mem_part_word_access_take1)
done

lemma get_instr_list_take2[rule_format]: 
      "i \<le> l \<longrightarrow> get_instr_list m b i = 
                 take i (get_instr_list m b l)"
apply clarsimp
apply (simp add: get_instr_list_def)
apply (simp add: take_map)
apply (subgoal_tac "mem_part_word_access m (b div 4) i = 
                    take i (mem_part_word_access m (b div 4) l)")
  apply clarsimp
apply (simp add: mem_part_word_access_take2)
done

lemma get_instr_list_append2[rule_format]: 
      "\<forall> base. get_instr_list m base l = a@b \<longrightarrow> 
               get_instr_list m (base + 4 * length a) (length b) = b"
apply clarsimp
apply (case_tac b)
  apply clarsimp
  apply (simp add: get_instr_list_empty)
apply (subgoal_tac "length b = l - length a")
  apply (subgoal_tac "get_instr_list m (base + 4 * length a) (length b) = drop (length a) a@b")
    apply simp
  apply clarsimp
  apply (subgoal_tac "length a < l")
    apply (simp add: get_instr_list_drop)
  apply arith
apply clarsimp
apply (subgoal_tac "length (get_instr_list m base l) = l")
  apply simp
apply (frule length_get_instr_list)
done

lemma get_instr_list_append3[rule_format]: 
      "get_instr_list m base l = a@b \<longrightarrow> get_instr_list m base (length a) = a"
apply clarsimp
apply (subgoal_tac "length a \<le> l")
  apply (frule_tac m="m" and b="base" and l="l" and i="length a" in get_instr_list_take2)
  apply clarsimp
apply (subgoal_tac "length (a@b) = l")
  apply simp
apply (insert length_get_instr_list[where m="m" and ad="base" and len="l"])
apply simp
done

lemma get_instr_list_Suc: 
      "get_instr_list m st (Suc n) = 
       get_instr_list m st n @ get_instr_list m (st + 4 * n) 1"
apply (simp only: get_instr_list_def)
apply (subst map_append[THEN sym])
apply (rule_tac f = "map cell2instr" in arg_cong)
apply (subst mem_part_word_access_Suc)
apply simp
apply (subst add.commute)
apply (rule refl)
done

lemma get_instr_list_to_append[rule_format]: 
      "n \<le> len \<longrightarrow> get_instr_list m st len = 
                   get_instr_list m st n @ get_instr_list m (st + 4 * n) (len - n)"
apply (induct_tac n)
 apply (simp add: get_instr_list_def)
apply (intro impI)
apply (drule mp, simp)
apply (erule ssubst)
apply (subst get_instr_list_Suc)
apply simp
apply (case_tac len)
 apply simp
apply simp
apply (subst Suc_diff_le)
 apply assumption
apply (simp add: get_instr_list_def)
apply (subst div_add1_eq)
apply simp
apply (subst add.commute)
apply (rule refl)
done

lemma take_get_instr_list: 
      "get_instr_list m st n = 
       take n (get_instr_list m st (n + k))"
apply (subst get_instr_list_to_append[of n "n + k"])
 apply simp
apply (subst take_append)
apply (subst length_get_instr_list)
apply simp
apply (simp add: length_get_instr_list)
done

lemma get_instr_list_tail[rule_format]: 
      "get_instr_list m b l = h#t \<longrightarrow> get_instr_list m (b + 4) (l - Suc 0) = t"
apply clarsimp
apply (simp add: get_instr_list_def)
apply clarsimp
apply (frule mem_part_word_access_tail)
apply (subgoal_tac "(b + 4) div 4 = Suc (b div 4)")
  apply simp
apply arith
done

lemma get_instr_list_head[rule_format]: 
      "get_instr_list m b l = h#t \<longrightarrow> get_instr_list m b 1 = [h]"
apply clarsimp
apply (simp add: get_instr_list_def)
apply clarsimp
apply (simp add: mem_part_word_access_head)
done

lemma drop_get_instr_list: 
      "get_instr_list m (st + 4 * n) l = drop n (get_instr_list m st (l + n))"
apply (subst get_instr_list_to_append[of n "l + n"])
 apply simp
apply (subst drop_append)
apply (subst length_get_instr_list)
apply simp
apply (simp add: length_get_instr_list)
done

lemma instr_mem_read_from_get_instr_list[rule_format]:
      "! st_ad len i. get_instr_list m st_ad len = in_ls \<longrightarrow> i < len \<longrightarrow> 
       instr_mem_read m (st_ad + 4 * i) = in_ls ! i"
apply (induct_tac in_ls)
 apply (intro allI impI)
 apply (case_tac len)
  apply simp
 apply (simp add: get_instr_list_def)
apply (intro impI allI)
apply (case_tac i)
 apply simp
 apply (simp add: get_instr_list_def)
 apply (case_tac len)
  apply simp
 apply (simp add: instr_mem_read_def)
apply (case_tac len)
 apply (simp add: get_instr_list_def)
apply (erule_tac x = "st_ad + 4" in allE)
apply (erule_tac x = "nata" in allE)
apply (erule_tac x = "nat" in allE)
apply (drule mp)
 apply (clarsimp simp add: get_instr_list_def)
  apply (simp add: div_geq)
  by (simp add: add.assoc)

lemma nth_get_instr_list:
      "i < len \<Longrightarrow> get_instr_list m stad len ! i = instr_mem_read m (stad + 4 * i)"
apply (subst instr_mem_read_from_get_instr_list)
  apply (rule refl)
 apply assumption
apply (rule refl)
done

lemma nth_get_data_list[rule_format]:
      "! ad i. i < len \<longrightarrow> get_data_list m ad len ! i = cell2data (m (ad div 4 + i))"
apply (induct len)
 apply simp
apply (intro allI impI)
apply (erule_tac x = "ad + 4" in allE)
apply (simp add: get_data_list_def)
apply (case_tac i)
 apply simp
apply (erule_tac x = "nat" in allE)
apply simp
  using length_word_access word_access_content by force

lemma get_instr_list_same:
      "\<lbrakk> get_instr_list m st_ad len = code;
         mem_unchanged m nm st_ad (st_ad + 4 * len) \<rbrakk>
     \<Longrightarrow>
         get_instr_list nm st_ad len = code"
apply (erule subst)
apply (simp add: get_instr_list_def)
apply (rule_tac f = "map cell2instr" in arg_cong)
apply (rule list_equality)
 apply (simp_all add: length_word_access)
apply (intro allI impI)
apply (simp add: word_access_content)
apply (simp add: mem_unchanged_def)
apply (simp add: mem_unchanged_word_def)
done

lemma get_data_list_same:
      "\<lbrakk> get_data_list m st_ad len = code;
         mem_unchanged m nm st_ad (st_ad + 4 * len) \<rbrakk> 
     \<Longrightarrow>
         get_data_list nm st_ad len = code"
apply (erule subst)
apply (simp add: get_data_list_def)
apply (rule_tac f = "map cell2data" in arg_cong)
apply (rule list_equality)
 apply (simp_all add: length_word_access)
apply (intro allI impI)
apply (simp add: word_access_content)
apply (simp add: mem_unchanged_def)
apply (simp add: mem_unchanged_word_def)
done

lemma get_instr_list_no_change_3:
      "\<lbrakk> get_instr_list m st_ad (length code) = code;
         \<forall> ad. st_ad div 4 \<le> ad \<and> ad < st_ad div 4 + length code \<longrightarrow> nm ad = m ad \<rbrakk> 
   \<Longrightarrow>
       get_instr_list nm st_ad (length code) = code"
apply (erule subst)
apply (subst length_get_instr_list)
apply (simp add: get_instr_list_def)
apply (rule_tac f = "map cell2instr" in arg_cong)
apply (rule list_equality)
 prefer 2
 apply (simp add: length_word_access)
apply (simp add: length_word_access)
apply (intro allI impI)
apply (simp add: word_access_content)
done

lemma get_instr_list_no_change_2:
      "\<lbrakk> get_instr_list m st_ad (length code) = code;
         st_ad div 4 + length code \<le> cpa div 4;
         \<forall> ad. ad < cpa div 4 \<longrightarrow> nm ad = m ad \<rbrakk> \<Longrightarrow>
       get_instr_list nm st_ad (length code) = code"
apply (erule get_instr_list_no_change_3)
apply (intro allI impI)
apply (erule_tac x = "ad" in allE)
apply (erule mp)
apply arith
done

lemma get_instr_list_append_middle [rule_format]:"(get_instr_list m base l = a@b@c) \<longrightarrow>  (get_instr_list m (base + (4 *(length a))) (length b) = b)"
apply clarsimp
apply (frule_tac m = "m"  and  l = "l" and a = "a" and b = "b@c" in get_instr_list_append2)
apply (simp add: get_instr_list_append1)
done

text
{*
   writes the sequence of memory cells of length @{text len} starting from address @{text ad}
*}

definition mem_part_word_update :: "[mem_t, nat, mem_cell_t list] \<Rightarrow> mem_t"
where
"mem_part_word_update memory ad mem_ls == (\<lambda> i. if i < ad \<or> ad + length mem_ls \<le> i
                                                  then memory i
                                                  else mem_ls ! (i - ad))"

definition mem_part_update :: "[mem_t, nat, mem_cell_t list] \<Rightarrow> mem_t"
where
"mem_part_update memory ad mem_ls == mem_part_word_update memory (ad div 4) mem_ls"

definition data_mem_write_region :: "mem_t \<Rightarrow> nat \<Rightarrow> int list \<Rightarrow> mem_t"
where
"data_mem_write_region m sa xs ==
    mem_part_word_update m (sa div 4) (map data2cell xs)"
text
{*
   copies memory part of length @{text len} from the @{text mem2} starting 
   from @{text add2} to the @{text mem1} starting from @{text add1}
*}

definition mem_part_copy :: "[mem_t, nat, mem_t, nat, nat] \<Rightarrow> mem_t"
where
  "mem_part_copy mem1 add1 mem2 add2 len == mem_part_update mem1 add1 (mem_part_access mem2 add2 len)"

lemma mem_part_copy_def_2: "mem_part_copy mem1 add1 mem2 add2 len = (\<lambda> i. if i < (add1 div 4) \<or> (add1 div 4) + (len div 4) \<le> i 
                                                                          then mem1 i
                                                                          else mem2 ((add2 div 4) + i - (add1 div 4)))"
apply (simp add: mem_part_copy_def mem_part_update_def mem_part_access_def mem_part_word_update_def length_word_access)
apply (rule ext)
apply (split if_split)
apply clarsimp
apply (cut_tac len = "len div 4" and ad = "add2 div 4" and i = "i - add1 div 4" and  memory = "mem2" in word_access_content)
 apply (subgoal_tac "\<exists> k. i = add1 div 4 + k")
  apply (erule exE)
  apply simp
 apply (rule_tac x = "i - add1 div 4" in exI)
 apply simp
apply simp
done

lemma mem_parts_equal: "i < (len div 4) \<Longrightarrow> (mem_part_copy mem1 ba1 mem2 ba2 len) (ba1 div 4 + i) = mem2 (ba2 div 4 + i)"
by (simp add: mem_part_copy_def_2)

lemma other_mem_the_same: 
      "\<lbrakk> i < ba1; ba1 + len < i\<rbrakk> \<Longrightarrow> (mem_part_copy mem1 ba1 mem2 ba2 len) i = mem1 i"
by (clarsimp simp add: mem_part_copy_def_2)

lemma mem_part_access_mem_part_copy:
  assumes mod: "cstart mod 4 = 0" "astart mod 4 = 0" "alen mod 4 = 0"
  assumes ge: "cstart \<ge> astart + alen"
  shows
    "mem_part_access (mem_part_copy oldmem cstart newmem 0 clen) astart alen =
     mem_part_access oldmem astart alen"
using assms
apply (simp add: list_eq_iff_nth_eq length_access)
apply (intro allI impI)
apply (frule_tac memory=oldmem and ad=astart in access_content)
apply (frule_tac memory="mem_part_copy oldmem cstart newmem 0 clen"
  and ad=astart in access_content)
apply simp
by (auto simp add: mem_part_access_def mem_part_copy_def
  mem_part_word_update_def mem_part_update_def)


lemma mem_part_word_update_unchanged[rule_format]: 
      "4 dvd i \<longrightarrow> 4 dvd b \<longrightarrow> i < b \<or> b + 4 * length vl \<le> i \<longrightarrow> 
       (mem_part_word_update m (b div 4) vl) (i div 4) = m (i div 4)"
apply clarsimp
apply (rule conjI)
 apply clarsimp
 apply (simp add: mem_part_word_update_def)
 apply clarsimp
 apply (simp add: dvd_div_less_n)
apply clarsimp
apply (simp add: mem_part_word_update_def)
apply clarsimp
apply (subgoal_tac "4 dvd (b + 4 * length vl)")
 apply arith
apply arith
done

lemma mem_part_word_update_data_mem_read_unchanged[rule_format]: 
      "4 dvd i \<longrightarrow> 4 dvd b \<longrightarrow> i < b \<or> b + 4 * length vl \<le> i  \<longrightarrow> 
       data_mem_read (mem_part_word_update m (b div 4) vl) i = data_mem_read m i"
apply clarsimp
apply (simp add: data_mem_read_def)
apply (simp add: mem_part_word_update_unchanged)
done

lemma mem_part_word_update_data_mem_read_correct[rule_format]: 
      "4 dvd i \<longrightarrow> 4 dvd b \<longrightarrow> b \<le> i \<longrightarrow> i < b + 4 * length vl \<longrightarrow> 
       data_mem_read (mem_part_word_update m (b div 4) vl) i = 
       cell2data(vl!(i div 4 - b div 4))"
apply clarsimp
apply (simp add: mem_part_word_update_def data_mem_read_def)
apply (rule conjI)
 apply clarsimp
 apply arith
apply clarsimp
apply (cut_tac k="4" and b="b + 4 * length vl" in dvd_div_less_n)
   apply (simp_all add: dvd_add dvd_div_less_n)+
done

lemma mem_part_word_access_Suc_def2: 
      "m st_ad # mem_part_word_access m (Suc st_ad) n = 
       mem_part_word_access m st_ad (Suc n)"
apply (simp add: mem_part_word_access_Suc_def)
done

lemma mem_part_word_update_append: 
      "mem_part_word_update (mem_part_word_update m b vl) (b + length vl) vl' = 
       mem_part_word_update m b (vl@vl')"
apply (simp add: mem_part_word_update_def)
apply (rule ext)
apply (simp split: if_split_asm)
apply auto

apply (simp add: nth_append)
apply arith

apply (simp add: nth_append)
apply arith
done

lemma mem_part_word_update_cons: 
      "mem_part_word_update (mem_part_word_update m b [v]) (Suc b) vl = 
       mem_part_word_update m b (v#vl) "
apply (simp add: mem_part_word_update_def)
apply (rule ext)
apply clarsimp

done

lemma mem_unchanged_transitive[rule_format]: 
      "mem_unchanged m m' b l \<longrightarrow> mem_unchanged m' m'' b l \<longrightarrow> 
       mem_unchanged m m'' b l"
apply clarsimp
apply (simp add: mem_unchanged_def)
apply (simp add: mem_unchanged_word_def)
done

lemma mem_unchanged_self[rule_format, simp]: "mem_unchanged m m b l"
apply (simp add: mem_unchanged_def)
apply (simp add: mem_unchanged_word_def)
done

lemma mem_unchanged_word_mem_part_word_access_same[rule_format]: 
      "\<forall> base. mem_unchanged_word m m' a b \<longrightarrow> a \<le> base \<longrightarrow> base + l \<le> b \<longrightarrow> 
               mem_part_word_access m' base l = mem_part_word_access m base l"
apply (induct_tac l)
 apply clarsimp
apply clarsimp
apply (rename_tac n base)
apply (simp add: mem_unchanged_word_def)
done

lemma mem_unchanged_get_instr_list_same[rule_format]: 
      "mem_unchanged m m' a b \<longrightarrow> a \<le> base \<longrightarrow> base + 4 * l \<le> b \<longrightarrow> 
       get_instr_list m' base l = get_instr_list m base l"
apply clarsimp
apply (simp add: get_instr_list_def)
apply (simp add: mem_unchanged_def)
apply (frule_tac base="base div 4" and l="l" in mem_unchanged_word_mem_part_word_access_same)
  apply arith
 apply arith
apply simp
done

lemma mem_part_word_update_mem_unchanged_word2[rule_format]: 
      "e \<le> base \<longrightarrow> mem_unchanged_word m (mem_part_word_update m base vl) b e"
apply clarsimp
apply (simp add: mem_part_word_update_def)
apply (simp add: mem_unchanged_word_def)
done

lemma mem_part_word_update_mem_unchanged_word3[rule_format]: 
      "base + length vl \<le> b \<longrightarrow> mem_unchanged_word m (mem_part_word_update m base vl) b e"
apply clarsimp
apply (simp add: mem_part_word_update_def)
apply (simp add: mem_unchanged_word_def)
done

lemma mem_unchanged_data_mem_read_same[rule_format]: 
      "mem_unchanged m m' a b \<longrightarrow> 4 dvd x \<longrightarrow> 4 dvd b \<longrightarrow> a \<le> x \<longrightarrow> x < b \<longrightarrow> 
       data_mem_read m' x = data_mem_read m x"
apply clarsimp
apply (simp add: data_mem_read_def)
apply (simp add: mem_unchanged_def)
apply (simp add: mem_unchanged_word_def)
apply (erule_tac x="x div 4" in allE)
apply (simp add: div_le_mono)
apply (simp add: dvd_div_less_n)
done

lemma mem_unchanged_word_contained[rule_format]: 
      "mem_unchanged_word m m' a b \<longrightarrow> a \<le> a' \<longrightarrow> b' \<le> b \<longrightarrow> 
       mem_unchanged_word m m' a' b'"
apply clarsimp
apply (simp add: mem_unchanged_word_def)
done

lemma mem_unchanged_contained[rule_format]: 
      "mem_unchanged m m' a b \<longrightarrow> a \<le> a' \<longrightarrow> b' \<le> b \<longrightarrow> mem_unchanged m m' a' b'"
apply clarsimp
apply (simp add: mem_unchanged_def)
apply (frule_tac a'="a' div 4" and b'="b' div 4" in mem_unchanged_word_contained)
  apply arith
 apply arith
apply simp
done

lemma mem_part_word_update_is_data_mem_write[rule_format]: 
      "mem_part_word_update m (a div 4) [data2cell x] = data_mem_write m a x"
apply (simp add: mem_part_word_update_def data_mem_write_def)
apply (rule ext)
apply clarsimp
done

lemma mem_part_word_update_mem_part_word_access_unchanged_aux[rule_format]: 
      "\<forall> c. \<not> range_overlap (a, b) (4 * c, 4 * l) \<longrightarrow> 4 dvd a \<longrightarrow> b div 4 = length vl \<longrightarrow>
            mem_part_word_access (mem_part_word_update m (a div 4) vl) c l = 
            mem_part_word_access m c l"
apply (induct_tac l)
 apply simp
apply clarsimp
apply (rule conjI)
 apply (simp add: range_overlap_def)
 apply (subgoal_tac "4 dvd 4 * c")
  apply (frule_tac i="4 * c" and b="a" and m="m" and vl="vl" in mem_part_word_update_unchanged, simp)
   apply clarsimp
   apply arith
  apply clarsimp
 apply simp
apply (rename_tac l c)
apply (erule_tac x="Suc c" in allE)
apply clarsimp
apply (simp add: range_overlap_def)
done

lemma mem_part_word_update_mem_part_word_access_unchanged[rule_format]: 
"\<not> range_overlap (a,b) (c,d) \<longrightarrow> 4 dvd a \<longrightarrow> b div 4 = length vl \<longrightarrow> 4 dvd c \<longrightarrow> 
   4 dvd d \<longrightarrow> mem_part_word_access 
               (mem_part_word_update m (a div 4) vl) (c div 4) (d div 4)= 
   mem_part_word_access m (c div 4) (d div 4)"
apply clarsimp
apply (insert mem_part_word_update_mem_part_word_access_unchanged_aux
              [where a="a" and b="b" and c="c div 4" and l="d div 4" and vl="vl" and m="m"])
apply clarsimp
done

lemma mem_part_word_update_mem_unchanged_word[rule_format]:
 "\<not> range_overlap (base, length vl) (b, l) \<longrightarrow> 
   mem_unchanged_word m (mem_part_word_update m base vl) b (b + l)"
apply clarsimp
apply (simp add: range_overlap_def mem_part_word_update_def)
apply (simp add: mem_unchanged_word_def)
apply clarsimp
done

lemma mem_part_word_update_mem_unchanged[rule_format]: 
"\<not> range_overlap (base, length vl) (b div 4, l div 4) \<longrightarrow> 4 dvd b \<longrightarrow> 
  mem_unchanged m (mem_part_word_update m base vl) b (b + l)"
apply clarsimp
apply (frule mem_part_word_update_mem_unchanged_word)
apply (simp add: mem_unchanged_def)
apply (simp add: dvd_div_add2)
done

lemma mem_part_word_update_commute[rule_format]: 
"\<not> range_overlap (b, length vl) (b', length vl') \<longrightarrow> 
  mem_part_word_update (mem_part_word_update m b vl) b' vl' = 
  mem_part_word_update (mem_part_word_update m b' vl') b vl"
apply clarsimp
apply (simp add: mem_part_word_update_def)
apply (simp add: range_overlap_def)
apply (rule ext)
apply auto
done

lemma data_mem_read_data_mem_write: 
"data_mem_read (data_mem_write m a d) a = d"
apply (simp add: data_mem_read_def data_mem_write_def)
apply (simp add: data2cell2data)
done

lemma mem_part_word_update_mem_part_changed_word[rule_format]: 
"b' \<le> b \<longrightarrow> b + length vl \<le> b' + l \<longrightarrow> mem_part_changed_word m (mem_part_word_update m b vl) b' l"
by (simp add: mem_part_changed_word_def mem_part_word_update_def)

lemma mem_part_changed_word_trans[rule_format]: 
"mem_part_changed_word m m' b l \<longrightarrow> range_contains (b',l') (b,l) \<longrightarrow> 
 mem_part_changed_word m m' b' l'"
apply clarsimp
apply (simp add: range_contains_def mem_part_changed_word_def)
done

lemma mem_part_changed_word_trivial[simp]: 
      "mem_part_changed_word m m b l"
by (simp add: mem_part_changed_word_def)

lemma mem_part_changed_word_data_mem_read_unchanged[rule_format]: 
   "mem_part_changed_word m m' a b \<longrightarrow> 
    \<not> inside_range (a, a + b) (i div 4) \<longrightarrow> 
    data_mem_read m' i = data_mem_read m i"
apply clarsimp
apply (simp add: mem_part_changed_word_def inside_range_def data_mem_read_def)
apply (erule_tac x="i div 4" in allE)
apply clarsimp
apply (case_tac "a \<le> i div 4")
 apply clarsimp
apply simp
done

lemma mem_part_changed_word_append[rule_format]:
 "mem_part_changed_word m m' b l \<longrightarrow> 
  mem_part_changed_word m' m'' b' l' \<longrightarrow> 
  mem_part_changed_word m m'' (fst (range_union (b,l) (b',l'))) 
                              (snd (range_union (b,l) (b',l')))"
apply clarsimp
apply (simp add: mem_part_changed_word_def)
apply clarsimp
using range_union_lower[where a="(b,l)" and b="(b',l')"]
using range_union_upper[where a="(b,l)" and b="(b',l')"]
apply simp
done

text
  {*
  combination of @{text mem_part_changed_word} for two intervals which adjacent to each other
  *}
lemma mem_part_changed_word_append2[rule_format]: 
"mem_part_changed_word m m' b l \<longrightarrow> 
 mem_part_changed_word m' m'' b' l' \<longrightarrow> 
 b + l \<le> b' \<longrightarrow> 
 mem_part_changed_word m m'' b (b' - b + l')"
apply clarsimp
apply (simp add: mem_part_changed_word_def)
done

lemma mem_part_changed_word_mem_unchanged_word1[rule_format]: 
"mem_part_changed_word m m' a l \<longrightarrow> a + l \<le> x \<longrightarrow> mem_unchanged_word m m' x y"
apply clarsimp
apply (simp add: mem_part_changed_word_def mem_unchanged_def mem_unchanged_word_def)
done

lemma mem_part_changed_word_mem_unchanged_word2[rule_format]: 
"mem_part_changed_word m m' a l \<longrightarrow> y \<le> a \<longrightarrow> mem_unchanged_word m m' x y"
apply clarsimp
apply (simp add: mem_part_changed_word_def mem_unchanged_def mem_unchanged_word_def)
done

lemma mem_part_changed_word_and_not_range_overlap_impl_mem_unchanged:
      "\<lbrakk> mem_part_changed_word m m' (ch_ad div 4) ch_len;
         \<not> range_overlap (unch_st, 4 * unch_len) (ch_ad, 4 * ch_len) \<rbrakk>
    \<Longrightarrow>
         mem_unchanged m m' unch_st (unch_st + 4 * unch_len)"
apply (simp add: mem_unchanged_def)
apply (simp add: mem_unchanged_word_def)
apply (intro allI impI)
apply (simp only: mem_part_changed_word_def)
apply (erule_tac x = "i" in allE)
apply (erule mp)
apply (simp add: range_overlap_def)
apply (case_tac "ch_ad < unch_st + 4 * unch_len", simp_all)
 apply (rule disjI2)
 apply (rule_tac j = "unch_st div 4" in le_trans)
  apply simp_all
 apply arith
done

text{* @{text data_mem_read} and @{text data_mem_read_region} *}

lemma data_mem_read_eq_read_region:
assumes "4 dvd ad" "4 dvd sa"
        "ad \<ge> sa" "(ad - sa) div 4 < am"
shows
 "data_mem_read m ad =
  data_mem_read_region m sa am ! ((ad - sa) div 4)"

proof -
  from assms
  have "(ad - sa) div 4 = ad div 4 - sa div 4"
  by (rule_tac sym, rule_tac nat_div_diff, simp+)

thus ?thesis using assms
  apply (simp add: data_mem_read_region_def data_mem_read_def)
  apply (simp add: nth_map length_word_access word_access_content)
  apply (simp add: cell2data_def add.commute)
by (simp add: div_le_mono)
qed

lemma data_mem_read_in_read_region:
assumes "(ad - sa) div 4 < am" "ad \<ge> sa" "4 dvd sa" "4 dvd ad"
shows "data_mem_read m ad \<in> set (data_mem_read_region m sa am)"

proof -
from assms show ?thesis
using data_mem_read_eq_read_region
      [where ad= "ad" and sa = "sa" and m = "m" and am ="am"]
by (simp add: nth_mem data_mem_read_region_def length_word_access)
qed

end
