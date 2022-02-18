(**
 * Copyright (c) 2003-2009 Dirk Leinenbach.
 * Some rights reserved, Saarland University.
 *
 * This work is licensed under the German-Jurisdiction Creative Commons
 * Attribution Non-commercial Share Alike 2.0 License.
 * See the file LIZENZ for a full copy of the license.
**)
(* $Id: Range.thy 27165 2009-04-08 12:01:52Z DirkLeinenbach $ *)
theory Range imports MoreDivides begin
text {* A range is a pair of base address and length *}

type_synonym  rangeT = "nat \<times> nat"

text {* Predicate that indicates whether two ranges @{term a} and @{term b} overlap *}

definition  range_overlap :: "rangeT \<Rightarrow> rangeT \<Rightarrow> bool"
where
"range_overlap a b \<equiv> fst b < fst a + snd a \<and> fst a < fst b + snd b"

text {* Predicate that indicates if range @{term b} is completely contained in range @{term a} *}

definition range_contains :: "rangeT \<Rightarrow> rangeT \<Rightarrow> bool"
where
"range_contains a b \<equiv> (fst a \<le> fst b) \<and> (fst b + snd b \<le> fst a + snd a)"

definition range_union:: "rangeT \<Rightarrow> rangeT \<Rightarrow> rangeT"
where
"range_union a b \<equiv> (min (fst a) (fst b),
                       max (fst a + snd a) (fst b + snd b) - min (fst a) (fst b))"
text {*
  Observe, that for @{text inside_range} the range has a different meaning: 
  it is a pair of base address and end address.
  This is ugly, but a fix would require too much changes in too many proofs.
  *}

definition inside_range :: "rangeT \<Rightarrow> nat \<Rightarrow> bool"
where
"inside_range rangee i \<equiv> fst rangee \<le> i \<and> i < snd rangee"

(* convert word addressed range to byte addresses *)

definition  word_range_to_byte :: "rangeT \<Rightarrow> rangeT"
where
"word_range_to_byte rangee \<equiv> (4 * fst rangee, 4 * snd rangee)"

lemma range_overlap_symmetric[rule_format]: 
  "range_overlap a b = range_overlap b a"
apply (simp add: range_overlap_def)
apply force
done

lemma range_contains_not_range_overlap[rule_format]: 
  "range_contains a b \<longrightarrow> \<not> range_overlap a c \<longrightarrow> 0 < snd b \<longrightarrow> 
   \<not>range_overlap b c"
apply clarsimp
apply (simp add: range_contains_def range_overlap_def)
done

lemma range_contains_transitive[rule_format]: 
  "range_contains a b \<longrightarrow> range_contains b c \<longrightarrow> range_contains a c"
apply clarsimp
apply (simp add: range_contains_def)
done

lemma range_contains_add_offset[rule_format]: 
  "range_contains (a,b) (c,d) \<longrightarrow> range_contains (a+offset,b) (c+offset,d)"
apply clarsimp
apply (simp add: range_contains_def)
done

lemma range_contains_range_overlap[rule_format]: 
  "0 < sb \<longrightarrow> range_contains (a,sa) (b,sb) \<longrightarrow> range_overlap (a,sa) (b,sb)"
apply clarsimp
apply (simp add: range_contains_def range_overlap_def)
done

lemma range_contains_not_range_overlap2[rule_format]: 
  "range_contains b b' \<longrightarrow> \<not> range_overlap a b \<longrightarrow> \<not> range_overlap a b'"
apply clarsimp
apply (simp add: range_overlap_def range_contains_def)
done

lemma not_range_overlap1[rule_format]: 
  "a + b \<le> c \<longrightarrow> \<not> range_overlap (a,b) (c,d)"
apply clarsimp
apply (simp add: range_overlap_def)
done


lemma dvd_range_overlap_div_mono[rule_format]: "k dvd a \<longrightarrow> k dvd b \<longrightarrow> k dvd c \<longrightarrow> k dvd d
                                                 \<longrightarrow> range_overlap (a div k, b div k) (c div k, d div k)
                                                 \<longrightarrow> range_overlap (a, b) (c, d)"
apply clarsimp
apply (simp add: range_overlap_def)
apply clarsimp
apply (rule conjI)
apply (metis div_less_mono dvd_div_add2)
apply (metis div_less_mono dvd_div_add2)
done

lemma range_contained_range_overlap2[rule_format]:
      "range_overlap a b \<longrightarrow> range_contains a' a  \<longrightarrow> 
       range_contains b' b  \<longrightarrow> range_overlap a' b'"
apply clarsimp
apply (simp add: range_overlap_def)
apply (simp add: range_contains_def)
done

lemma range_union_lower[rule_format]: 
  "fst (range_union a b) \<le> fst a \<and> fst (range_union a b) \<le> fst b"
by (simp add: range_union_def)

lemma range_union_upper[rule_format]: 
  "fst a + snd a \<le> fst (range_union a b) + snd (range_union a b) \<and> 
   fst b + snd b \<le> fst (range_union a b) + snd (range_union a b)"
by (simp add: range_union_def)

lemma inside_range_interval[rule_format]: 
     "inside_range rangee a \<longrightarrow> inside_range rangee b \<longrightarrow> a \<le> x \<longrightarrow> 
      x \<le> b \<longrightarrow> inside_range rangee x"
by (simp add: inside_range_def)
end
