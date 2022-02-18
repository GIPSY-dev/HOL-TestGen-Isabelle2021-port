(**
 * Copyright (c) 2003-2008 Matthias Daum, Mark Hillebrand, Dirk Leinenbach,
 * Elena Petrova, Mareike Schmidt, Martin Strecker, Alexandra Tsyban,
 * Sergey Tverdyshev, Hristo Tzigarov.
 * Some rights reserved, Saarland University.
 *
 * This work is licensed under the German-Jurisdiction Creative Commons
 * Attribution Non-commercial Share Alike 2.0 License.
 * See the file LIZENZ for a full copy of the license.
**)
(* $Id: MoreWord.thy 25585 2008-10-07 22:00:58Z DirkLeinenbach $ *)

chapter {* Extensions to Isabelle/HOL's theory Word (about bit vectors) *}

theory MoreWord 

imports    
   "$ISABELLE_HOME/src/HOL/Library/Bit" 
   "$ISABELLE_HOME/src/HOL/Word/Word" 
    MoreList MoreIntDiv

 begin

subsection {* bit *}

lemma bitand_commute: " ((a::bit) AND  b ) = (b AND a )" (* legacy *)
  using Bits_Bit.bit_ops_comm(1)
  by simp

lemma bitor_commute: " ((a::bit) OR b ) = (b OR a )" (* legacy *)
  using Bits_Bit.bit_ops_comm(2)
  by auto

lemma and_one: 
      "map (case_prod op AND) (zip (replicate (length (v)) (1::bit)) v) = v"
  apply (induct v)
  apply auto
done

lemma and_zero: 
     "map (case_prod op AND) (zip (replicate (length (v)) (0::bit)) v) = 
      replicate (length v) (0::bit)"
  apply (induct_tac v)
  apply auto
done

subsection {* bitval *}

primrec bitval :: "bit => nat" where
    "bitval 0 = 0"
  | "bitval 1 = 1"

lemma bitval_pos[simp]: "0 \<le> bitval x"
  using  Nat.le0
  by auto

lemma not_replicate_Zeros_decompos[rule_format]:
      "0 < length wx \<longrightarrow> wx \<noteq> replicate (length wx) (0::bit) \<longrightarrow> 
       (\<exists>xs k. wx = xs @ [(1::bit)] @ replicate k (0::bit))"
apply (induct wx)
 apply simp
apply (intro impI)
apply (case_tac "wx = []")
 apply simp
 apply (case_tac a, simp)
 apply simp
 apply (rule_tac x = "[]" in exI)
 apply (rule_tac x = "0" in exI)
 apply simp
apply (drule mp, simp)
apply (case_tac "wx = replicate (length wx) (0::bit)")
 apply simp
 apply (rule_tac x = "[]" in exI)
 apply (rule_tac x = "length wx" in exI)
 apply simp
 apply (case_tac a, simp)
 apply simp_all
apply (elim exE)
apply (rule_tac x = "a # xs" in exI)
apply (rule_tac x = "k" in exI)
apply simp
using append_Cons
apply metis
done

lemma not_replicate_Zeros_decompos2[rule_format]:
      "0 < length wx \<longrightarrow> wx \<noteq> replicate (length wx) (0::bit) \<longrightarrow> 
       (\<exists>xs k. wx = replicate k (0::bit) @ [(1::bit)] @ xs)"
apply (induct wx)
 apply simp
apply (intro impI)
apply (case_tac "wx = []")
 apply simp
 apply (case_tac a, simp)
 apply simp
 apply (rule_tac x = "[]" in exI)
 apply (rule_tac x = "0" in exI)
 apply simp
apply (drule mp, simp)
apply (case_tac "wx = replicate (length wx) (0::bit)")
 apply simp
 apply (rule_tac x = "wx" in exI)
 apply (rule_tac x = "0" in exI)
 apply simp
 apply (case_tac a, simp)
 apply simp_all
apply (elim exE)
apply (case_tac a)
 apply (rule_tac x = "xs" in exI)
 apply (rule_tac x = "Suc k" in exI)
 apply simp
apply (rule_tac x = "wx" in exI)
apply (rule_tac x = "0" in exI)
apply simp
 apply force
done

subsection {* bv\_not *}

abbreviation 
  "bv_not \<equiv> map (\<lambda> x::bit. NOT x)"

lemma bv_not_append: 
      "bv_not (xs @ ys) = bv_not xs @ bv_not ys"
by (induct xs) simp_all

lemma bv_not_replicate_one: 
      "bv_not (replicate n (1::bit)) = replicate n (0::bit)"
by (induct n) simp_all

lemma bv_not_replicate_zero: "bv_not (replicate n (0::bit)) = replicate n (1::bit)"
  apply (induct n)
  apply simp_all
done
abbreviation 
"bitnot \<equiv> (\<lambda> x::bit. NOT x) "

lemma inj_bitnot: "inj bitnot"
apply (simp add: inj_on_def)
apply (intro allI)
apply (case_tac x)
 apply (case_tac [!] y)
   apply simp_all
done

lemma bv_not_eq[rule_format]: "bv_not xs = bv_not ys \<longrightarrow> xs = ys"
  by (simp add: inj_bitnot)

lemma bv_not_is_replicate_Zero_impl_replicate_One[rule_format]:
      "bv_not wx = replicate (length wx) (0::bit) \<longrightarrow> wx = replicate (length wx) (1::bit)"
apply (induct wx)
 apply simp
apply (rule impI)
apply simp
apply (case_tac a, simp_all)
done

subsection {* norm\_unsigned *}

fun rem_initial :: "bit => bit list => bit list" where
"rem_initial b [] = []"
|"rem_initial b (x#xs) = (if b = x then rem_initial b xs else x#xs)"

abbreviation "norm_unsigned == rem_initial 0"

lemma norm_unsigned_replicate_One: "norm_unsigned (replicate z (1::bit)) = replicate z (1::bit)"
 apply (induct z)
  apply simp
 apply simp
done

lemma norm_unsigned_replicate_Zero: "norm_unsigned (replicate n (0::bit)) = []"
  apply (induct n)
  apply  simp+
done

lemma norm_unsigned_replicate_Zero_append:
    "norm_unsigned (replicate n (0::bit) @ xs) = norm_unsigned xs"
by (induct n, simp+)

lemma norm_unsigned_replicate_zeros[rule_format]: 
      "norm_unsigned (replicate k (0::bit) @ (1::bit) # wx) = (1::bit) # wx"
apply (induct_tac k)
 apply simp
apply simp
done
definition
   bv_extend :: "[nat,bit,bit list]=>bit list" where
  "bv_extend i b w = (replicate (i - length w) b) @ w"

lemma norm_unsigned_bv_extend:
    "norm_unsigned (bv_extend w (0::bit) v) = norm_unsigned v"
by (unfold bv_extend_def, simp add: norm_unsigned_replicate_Zero_append)

lemma bv_extend_norm_unsigned_eq[rule_format]:
 "length a \<le> w \<longrightarrow> bv_extend w (0::bit) a = bv_extend w (0::bit) (norm_unsigned a)"
 apply (induct a)
 apply simp
 apply auto
 unfolding bv_extend_def
proof -
  fix a2 :: "bit list"
  assume a1: "replicate (w - length a2) 0 @ a2 = replicate (w - length (norm_unsigned a2)) 0 @ norm_unsigned a2"
  assume "Suc (length a2) \<le> w"
  then have "(0::bit) # replicate (w - length a2 - 1) 0 = replicate (w - length a2) 0"
    by (meson Cons_replicate_eq Suc_le_lessD zero_less_diff)
  then have "0 # replicate (w - length (0 # a2)) 0 @ a2 = replicate (w - length a2) 0 @ a2"
    by force
  then show "replicate (w - length (0 # a2)) 0 @ 0 # a2 = replicate (w - length (norm_unsigned a2)) 0 @ norm_unsigned a2"
    using a1 by (simp add: replicate_app_Cons_same)
qed


lemma bv_extend_norm_unsigned2[rule_format]: "length w \<le> n \<longrightarrow> bv_extend n (0::bit) (norm_unsigned w) = bv_extend n (0::bit) w"
apply (induct_tac w)
 apply simp
apply clarsimp
unfolding bv_extend_def
proof -
  fix list :: "bit list"
  assume "Suc (length list) \<le> n"
  then have f1: "0 < n - length list"
    by (metis Suc_le_lessD zero_less_diff)
  have "n - length (0 # list) = n - length list - 1"
    by simp
  then show "replicate (n - length list) 0 @ list = replicate (n - length (0 # list)) 0 @ 0 # list"
    using f1 by (metis (no_types) Cons_eq_appendI Cons_replicate_eq replicate_app_Cons_same)
qed



definition
  bv_to_nat :: "bit list => nat" where (*bl_to_bin*)
  "bv_to_nat = foldl (%bn b. 2 * bn + bitval b) 0"

lemma bit_list_induct:
  assumes empty: "P []"
  and     zero:  "!!bs. P bs ==> P ((0::bit)#bs)"
  and     one:   "!!bs. P bs ==> P ((1::bit)#bs)"
  shows   "P w"
proof (induct w, simp_all add: empty)
  fix b bs
  assume "P bs"
  then show "P (b#bs)"
    by (cases b) (auto intro!: zero one)
qed

lemma bv_to_nat_type [simp]: "bv_to_nat (norm_unsigned w) = bv_to_nat w"
  by (rule bit_list_induct, simp_all add:  bv_to_nat_def)     



lemma bv_to_nat_norm_unsigned_eq[rule_format]: 
     "norm_unsigned v = norm_unsigned w \<longrightarrow> bv_to_nat v = bv_to_nat w"
  by (subst bv_to_nat_type[symmetric],  clarsimp)

lemma norm_unsigned_is_empty_impl_replicate_zeros[rule_format]:
      "norm_unsigned wx = [] \<longrightarrow> wx = replicate (length wx) (0::bit)"
apply (induct wx)
 apply simp
apply (intro impI)
apply simp
apply (case_tac a, simp_all)
done

definition
  bv_chop :: "bit list \<Rightarrow> nat \<Rightarrow> bit list * bit list" where
  "bv_chop w i = (let len = length w in (take (len - i) w,drop (len - i) w))"

lemma bv_to_nat_fst_bv_chop_norm_unsigned:
  shows "bv_to_nat (fst (bv_chop (norm_unsigned y) z)) = bv_to_nat (fst (bv_chop y z))"
proof (induct y)
  case Nil
  show ?case by simp
next
  case (Cons x xs)
  show ?case proof (cases x)
    case one
    thus ?thesis unfolding bv_chop_def by simp 
  next
    case zero
    hence "bv_to_nat (fst (bv_chop (norm_unsigned (x # xs)) z)) = 
           bv_to_nat (fst (bv_chop (norm_unsigned xs) z))"
      unfolding bv_chop_def by simp
    also from Cons
    have "\<dots> = bv_to_nat (fst (bv_chop xs z))" by simp
    also from zero
    have "\<dots> = bv_to_nat (fst (bv_chop (x # xs) z))"
    proof (cases "Suc (length xs) > z")
      case False
      thus ?thesis unfolding bv_chop_def Let_def by simp
    next
      case True
      hence "Suc (length xs) - z = Suc (length xs - z)"
	by arith
      hence "take (Suc (length xs) - z) (x # xs) = x # take (length xs - z) xs"
       	by simp
      with zero and True show ?thesis
      unfolding bv_chop_def Let_def bv_to_nat_def
	    by simp 
    qed
    finally show ?thesis .
  qed
qed

subsection {* norm\_signed *}

primrec norm_signed :: "bit list => bit list" (*rbl_succ or rbl_pred??*)
where
  norm_signed_Nil: "norm_signed [] = []"
 | norm_signed_Cons: "norm_signed (b#bs) =
    (case b of 1 => b #rem_initial b bs  
    |  0 => if norm_unsigned bs = [] then [] else b#norm_unsigned bs)"  

lemma norm_signed_replicate_Zero: 
  "norm_signed (replicate n (0::bit) ) = []"
  apply (induct n)
  apply  simp_all
  apply (case_tac "n") 
  apply  simp_all
  using norm_unsigned_replicate_Zero
  apply fast
done

lemma norm_signed_replicate_zeros_append[rule_format]: 
      "norm_signed (replicate k (0::bit) @ (0::bit) # xs) = 
       norm_signed ((0::bit) # xs)"
apply (induct_tac k)
 apply simp
apply simp
apply (case_tac n)
 apply simp
apply (erule subst)
apply (simp add: norm_unsigned_replicate_Zero_append)
done

lemma norm_signed_01_is_01 [rule_format]:
"z > 0 \<longrightarrow> norm_signed ((0::bit) # replicate z (1::bit)) = (0::bit) # replicate z (1::bit)"
 apply (induct z)
  apply simp
 apply simp
done

definition
  bv_msb :: "bit list => bit" where
  "bv_msb w = (if w = [] then 0 else hd w)"

lemma norm_signed_bv_msb:
    "norm_signed ((bv_msb xs) # xs) = norm_signed xs"
  apply (unfold bv_msb_def)
  apply (simp split: if_split)
  apply (cases xs, clarsimp+)
done
thm bit.split
lemma norm_signed_replicate_bv_msb:
    "norm_signed (replicate n (bv_msb xs) @ xs) = norm_signed xs"
  apply (induct n, simp+)
  apply (erule subst)
  apply (subgoal_tac "EX ys. replicate n (bv_msb xs) @ xs = ys")
  prefer 2
  apply  simp
  apply (erule exE)
  apply simp
  apply (subgoal_tac "bv_msb xs = bv_msb (replicate n (bv_msb xs) @ xs)")
  apply  (simp add: norm_signed_bv_msb)+
  apply (drule sym)
  apply (unfold bv_msb_def, simp)
  apply (rule conjI)
  apply  clarsimp
  apply  (case_tac n)
  apply   simp+
  apply (case_tac n)
  apply  (simp_all split: list.split bit.split list.split_asm bit.split_asm)
proof -
  fix na :: nat and ys :: "bit list"
  { assume "\<exists>bs bsa. (bs::bit list) \<noteq> bsa"
    { assume "hd xs \<noteq> 1"
      have "(case hd xs of 0 \<Rightarrow> 
                  if norm_unsigned xs = [] 
                  then [] 
                  else hd xs # norm_unsigned xs 
             | 1 \<Rightarrow> hd xs # rem_initial (hd xs) xs) = norm_signed xs \<longrightarrow> 
                    (hd xs = 0 \<longrightarrow> xs \<noteq> [] \<longrightarrow> (norm_unsigned xs = [] \<longrightarrow> 
                     [] = norm_signed xs) \<and> (norm_unsigned xs \<noteq> [] \<longrightarrow> 
                     0 # norm_unsigned xs = norm_signed xs)) \<and> (hd xs = 1 \<longrightarrow> xs \<noteq> [] \<longrightarrow> 
                     1 # rem_initial 1 xs = norm_signed xs)"
        by force }
    moreover
    { assume "(case hd xs of 0 \<Rightarrow> 
                    if norm_unsigned xs = [] 
                    then [] 
                    else hd xs # norm_unsigned xs 
                | 1 \<Rightarrow> hd xs # rem_initial (hd xs) xs) \<noteq> norm_signed xs"
      then have "bv_msb xs \<noteq> hd xs"
        by (metis norm_signed_Cons norm_signed_bv_msb)
      then have "(hd xs = 0 \<longrightarrow> xs \<noteq> [] \<longrightarrow> (norm_unsigned xs = [] \<longrightarrow> [] = norm_signed xs) \<and> 
                 (norm_unsigned xs \<noteq> [] \<longrightarrow> 0 # norm_unsigned xs = norm_signed xs)) \<and> 
                 (hd xs = 1 \<longrightarrow> xs \<noteq> [] \<longrightarrow> 1 # rem_initial 1 xs = norm_signed xs)"
        by (metis bv_msb_def) }
    ultimately have "(hd xs = 0 \<longrightarrow> xs \<noteq> [] \<longrightarrow> (norm_unsigned xs = [] \<longrightarrow> [] = norm_signed xs) \<and> 
                     (norm_unsigned xs \<noteq> [] \<longrightarrow> 0 # norm_unsigned xs = norm_signed xs)) \<and> 
                     (hd xs = 1 \<longrightarrow> xs \<noteq> [] \<longrightarrow> 1 # rem_initial 1 xs = norm_signed xs)"
      by fastforce }
  then show "(hd xs = 0 \<longrightarrow> xs \<noteq> [] \<longrightarrow> (norm_unsigned xs = [] \<longrightarrow> [] = norm_signed xs) \<and> 
             (norm_unsigned xs \<noteq> [] \<longrightarrow> 0 # norm_unsigned xs = norm_signed xs)) \<and> 
             (hd xs = 1 \<longrightarrow> xs \<noteq> [] \<longrightarrow> 1 # rem_initial 1 xs = norm_signed xs)"
    by blast
next
  show "\<And>n ys nat.
       (if xs = [] then 0 else hd xs) =
       (if ys = [] then 0 else hd ys) \<Longrightarrow>
       ys =
       (if ys = [] then 0 else hd ys) #
       replicate nat (if ys = [] then 0 else hd ys) @
       xs \<Longrightarrow>
       n = Suc nat \<Longrightarrow>
       (hd xs = 0 \<longrightarrow>
        (hd ys = 0 \<longrightarrow>
         xs \<noteq> [] \<longrightarrow>
         ys \<noteq> [] \<longrightarrow>
         (norm_unsigned ys = [] \<longrightarrow> [] = norm_signed ys) \<and>
         (norm_unsigned ys \<noteq> [] \<longrightarrow>
          0 # norm_unsigned (replicate nat 0 @ xs) =
          norm_signed ys)) \<and>
        (hd ys = 1 \<longrightarrow>
         xs \<noteq> [] \<longrightarrow>
         ys \<noteq> [] \<longrightarrow>
         0 # norm_unsigned (replicate nat 0 @ xs) =
         norm_signed ys)) \<and>
       (hd xs = 1 \<longrightarrow>
        (hd ys = 0 \<longrightarrow>
         xs \<noteq> [] \<longrightarrow>
         ys \<noteq> [] \<longrightarrow>
         (norm_unsigned ys = [] \<longrightarrow> [] = norm_signed ys) \<and>
         (norm_unsigned ys \<noteq> [] \<longrightarrow>
          1 # 1 # replicate nat 1 @ xs = norm_signed ys)) \<and>
        (hd ys = 1 \<longrightarrow>
         xs \<noteq> [] \<longrightarrow>
         ys \<noteq> [] \<longrightarrow>
         1 # rem_initial 1 (replicate nat 1 @ xs) =
         norm_signed ys))"
     by auto
next
  show "\<And>n ys.
       replicate n (if xs = [] then 0 else hd xs) @ xs =
       ys \<Longrightarrow>
       (xs = [] \<longrightarrow> ys \<noteq> [] \<longrightarrow> hd ys = 0) \<and>
       (xs \<noteq> [] \<longrightarrow>
        (ys = [] \<longrightarrow> hd xs = 0) \<and>
        (ys \<noteq> [] \<longrightarrow> hd xs = hd ys))"
proof -
  fix na :: nat and ys :: "bit list"
  assume a1: "replicate na (if xs = [] then 0 else hd xs) @ xs = ys"
  have f2: "\<forall>bs bsa. if bs = [] then hd (bs @ bsa) = (hd bsa::bit) else hd (bs @ bsa) = hd bs"
    by fastforce
  { assume "hd xs \<noteq> hd ys"
    then have "hd xs \<noteq> hd (replicate na (if xs = [] then 0 else hd xs) @ xs)"
     by (simp add: a1)
    then have "hd (replicate na (if xs = [] then 0 else hd xs) @ xs) \<noteq> 
               hd (replicate na (if xs = [] then 0 else hd xs)) \<or> 
               hd xs \<noteq> hd (replicate na (if xs = [] then 0 else hd xs))"
      by metis
    moreover
    { assume "hd xs \<noteq> hd (replicate na (if xs = [] then 0 else hd xs))"
      { assume "hd xs \<noteq> hd (replicate na (if xs = [] then 0 else hd xs) @ 
                [if xs = [] then 0 else hd xs])"
        then have "hd xs \<noteq> hd ((if xs = [] then 0 else hd xs) # 
                   replicate na (if xs = [] then 0 else hd xs))"
          by (simp add: replicate_append_same)
        then have "xs = []"
          using list.sel(1) by fastforce }
      then have "hd (replicate na (if xs = [] then 0 else hd xs) @ xs) = hd xs \<or> xs = []"
        using f2 by (metis (no_types)) }
    moreover
    { assume "hd (replicate na (if xs = [] then 0 else hd xs) @ xs) = hd xs"
      then have "ys = [] \<or> hd xs = hd ys"
       using \<open>hd xs \<noteq> hd (replicate na (if xs = [] then 0 else hd xs) @ xs)\<close> by auto
    }
    ultimately have "(ys = [] \<or> hd xs = hd ys) \<or> xs = []"
      using f2
      proof -
        { assume "xs \<noteq> []"
          { assume "replicate na (hd xs) \<noteq> [] \<and> xs \<noteq> []"
            moreover
            { assume "hd (replicate na (hd xs)) = hd xs \<and> replicate na (hd xs) \<noteq> [] \<and> xs \<noteq> []"
              then have "hd (replicate na (if xs = [] then 0 else hd xs) @ xs) = hd xs"
                using \<open>\<forall>bs bsa. if bs = [] then hd (bs @ bsa) = 
                       hd bsa else hd (bs @ bsa) = hd bs\<close> by presburger }
            ultimately have "hd (replicate na (if xs = [] then 0 else hd xs) @ xs) = 
                             hd xs \<or> (ys = [] \<or> hd xs = hd ys) \<or> xs = []"
              by force }
          then have ?thesis
            using \<open>hd (replicate na (if xs = [] then 0 else hd xs) @ xs) = hd xs \<Longrightarrow> 
                   ys = [] \<or> hd xs = hd ys\<close> by fastforce }
        then show ?thesis
          by metis
      qed }
  moreover
  { assume "xs = []"
    moreover
    { assume "xs = [] \<and> hd ys \<noteq> (if xs = [] then 0 else hd xs)"
      moreover
      { assume "xs = [] \<and> hd ys \<noteq> hd (replicate na (if xs = [] then 0 else hd xs))"
        then have "xs = [] \<and> hd (replicate na (if xs = [] then 0 else hd xs) @ xs) \<noteq> 
                  hd (replicate na (if xs = [] then 0 else hd xs))"
        using a1 by auto 
        then have "xs = [] \<and> replicate na (if xs = [] then 0 else hd xs) = [] \<and> xs = []"
          using f2 by meson }
      ultimately have "xs = [] \<and> replicate na (if xs = [] then 0 else hd xs) @ xs = []"
        using list.sel(1) by fastforce
      then have "(xs \<noteq> [] \<or> ys = [] \<or> hd ys = 0) \<and> (xs = [] \<or> (ys \<noteq> [] \<or> hd xs = 0) \<and> 
                 (ys = [] \<or> hd xs = hd ys))"
       using a1 by auto
       }
    ultimately have "(xs \<noteq> [] \<or> ys = [] \<or> hd ys = 0) \<and> (xs = [] \<or> 
                     (ys \<noteq> [] \<or> hd xs = 0) \<and> (ys = [] \<or> hd xs = hd ys))"
      by meson }
  ultimately show "(xs = [] \<longrightarrow> ys \<noteq> [] \<longrightarrow> hd ys = 0) \<and> 
                   (xs \<noteq> [] \<longrightarrow> (ys = [] \<longrightarrow> hd xs = 0) \<and> (ys \<noteq> [] \<longrightarrow> hd xs = hd ys))"
    using a1 by (metis (no_types) append_is_Nil_conv)
qed
qed

lemma norm_signed_bv_extend_bv_msb:
    "norm_signed (bv_extend w (bv_msb v) v) = norm_signed v"
by (unfold bv_extend_def, simp add: norm_signed_replicate_bv_msb)

lemma norm_signed_is_empty_impl_replicate_Zero[rule_format]:
  "norm_signed bx = [] \<longrightarrow> bx = replicate (length bx) (0::bit)"
apply (induct bx)
 apply (simp_all split: bit.split)
apply (intro impI)
apply (case_tac a)
 apply simp
 apply (drule mp)
  apply simp_all
 apply (case_tac [!] bx)
   apply simp_all
 apply (case_tac [!] aa)
   apply simp_all
done

lemma bv_msb_norm_signed[rule_format]: 
      "norm_signed (a # bx) \<noteq> [] \<longrightarrow> bv_msb (norm_signed (a # bx)) = a"
apply (simp add: bv_msb_def)
apply (case_tac a)
 apply (induct_tac [!] bx)
   apply simp_all
 apply (case_tac [!] aa)
done

lemma bv_via_norm_signed_decompose_sym [rule_format]:
      "! n. norm_signed bx \<noteq> [] \<longrightarrow>  length bx = n \<longrightarrow>  
       (replicate (n - length (norm_signed bx)) (bv_msb (norm_signed bx))) @ (norm_signed bx) = bx"
apply (simp add: bv_msb_def)
apply (induct bx)
 apply clarsimp
apply (rule impI)
apply (case_tac bx)
 apply simp
 apply (case_tac [!] a)
   apply simp_all
 apply (case_tac [!] "norm_signed (aa # list) = []")
   apply auto
proof -
  fix list :: "bit list"
  assume a1: "replicate (length list - length (norm_unsigned list)) 0 @ 0 # norm_unsigned list = 
               0 # list"
  { assume "0 # list \<noteq> 0 # norm_unsigned list"
    then have "length (norm_unsigned list) \<le> length list"
      using a1 by force }
  then have "length (norm_unsigned list) \<le> length list"
    by force
  then have "replicate (Suc (length list) - length (norm_unsigned list)) (0::bit) = 
             0 # replicate (length list - length (norm_unsigned list)) 0"
    by (metis (no_types) Suc_diff_le replicate_Suc' replicate_append_same)
  then have "replicate (Suc (length list) - length (norm_unsigned list)) (0::bit) = 
             [] \<and> 0 # norm_unsigned list = 0 # 0 # list \<or> 
             (\<exists>bs. replicate (Suc (length list) - length (norm_unsigned list)) 0 = 
                   0 # bs \<and> bs @ 0 # norm_unsigned list = 0 # list)"
       by (simp add: a1)
  then show "replicate (Suc (length list) - length (norm_unsigned list)) 0 @ 
             0 # norm_unsigned list = 0 # 0 # list"
    by (simp add: append_eq_Cons_conv)
next
  show "\<And>list.
       replicate (length list - length (rem_initial 1 list))
        1 @
       1 # rem_initial 1 list =
       1 # list \<Longrightarrow>
       replicate
        (Suc (length list) - length (rem_initial 1 list))
        1 @
       1 # rem_initial 1 list =
       1 # 1 # list"
proof -
  fix list :: "bit list"
  assume a1: "replicate (length list - length (rem_initial 1 list)) 1 @ 
              1 # rem_initial 1 list = 1 # list"
  have "\<not> length list - length (rem_initial 1 list) < 0"
    by (metis not_less0)
  then have "length (rem_initial 1 list) \<le> length list"
    using a1 by (metis le_eq_less_or_eq length_Cons linorder_neqE_nat 
                       replicate_empty self_append_conv2 size_Cons_lem_eq zero_less_diff)
  then show "replicate (Suc (length list) - length (rem_initial 1 list)) 1 @ 1 # rem_initial 1 list = 1 # 1 # list"
    using a1 Suc_diff_le by force
qed
qed


subsection {* bv\_extend *}

lemma bv_extend_Suc: 
   "bv_extend (Suc w) a (a#v) = a#bv_extend w a v"
  apply (simp add: bv_extend_def)
  apply (induct "w-length v")
  apply  (simp_all add:replicate_append_same)
done

lemma bv_extend_Nil: 
      "(bv_extend n b x = []) = (n=0 \<and> x=[])"
apply (case_tac "n = 0 \<and> x = []")
 apply simp
apply clarsimp
 apply (simp_all add: bv_extend_def)
 apply auto
done

lemma bv_msb_map_zip_bv_extend:
  "bv_msb (map (case_prod f)
               (zip (bv_extend (Suc l) (bv_msb v) v)
                    (bv_extend (Suc l) (bv_msb w) w)))
   = f (bv_msb v) (bv_msb w)"
  unfolding  bv_extend_def bv_msb_def
  apply simp
  apply (case_tac "Suc l-length v", simp)
  apply  (case_tac "Suc l-length w", simp)
  apply   (case_tac v, simp)
  apply   (case_tac w, simp+)
  apply  (case_tac "Suc l-length w", simp+)
  apply  (case_tac v, clarsimp+)
  apply (case_tac "Suc l-length w", simp+)
  apply  (case_tac w, simp+)
done

lemma  bv_extend_is_not_empty_1 :  " w \<noteq> [] \<Longrightarrow> bv_extend i b w \<noteq> [] "
by (simp add: bv_extend_def)

lemma  bv_extend_is_not_empty_2 :  " 0 < i - length w  \<Longrightarrow> bv_extend i b w \<noteq> [] "
apply (simp add: bv_extend_def replicate_not_empty)
done

lemma length_bv_extend: "length (bv_extend i b w) = max i (length w)"
  unfolding max_def bv_extend_def
  by simp

lemma take_bv_extend:
      "take (max (length v) l - n) (bv_extend l (0::bit) v) = 
       bv_extend (l - n) (0::bit) (take (length v - n) v)"
apply (simp  add: bv_extend_def)
apply (simp add: min_def max_def)
done

lemma drop_bv_extend_less[rule_format]:
      "n < length v \<longrightarrow> drop (l - n) (bv_extend l b v) = drop (min (length v) l - n) v"
apply clarsimp
apply (simp add: bv_extend_def)
apply (simp add: min_def)
done

lemma drop_bv_extend_ge_aux: 
      "length v \<le> n \<longrightarrow> n < l \<longrightarrow> drop (l - n) (bv_extend l b v) = bv_extend n b v"
apply clarsimp
apply (simp add: bv_extend_def)
done

lemma drop_bv_extend_ge: "length v \<le> n \<longrightarrow> drop (l - n) (bv_extend l b v) = bv_extend (min l n) b v"
apply clarsimp
apply (case_tac "n < l")
 apply (subst drop_bv_extend_ge_aux, simp, simp)
 apply (simp add: min_def)
apply (simp add: min_def)
done

lemma bv_extend_max:"bv_extend (max (length a) l) b a = bv_extend l b a"
  unfolding bv_extend_def
  by simp

lemma bv_extend_bv_extend: "bv_extend l b (bv_extend l' b v) = bv_extend (max l l') b v" 
apply (simp add: bv_extend_def)
apply (simp add: max_def)
apply (case_tac "l' \<le> length v")
 apply simp
apply clarsimp
apply (simp add: replicate_add[symmetric])
done

lemma bv_extend_bv_extend2: "l \<le> l' \<longrightarrow> bv_extend l' b v = bv_extend l' b (bv_extend l b v)"
apply clarsimp
apply (simp add: bv_extend_bv_extend)
apply (simp add: max_def)
done

lemma bv_msb_bv_extend_bv_msb: "bv_msb (bv_extend k (bv_msb wx) wx) = bv_msb wx"
apply (simp add: bv_extend_def)
apply (simp only: bv_msb_def)
apply (case_tac k, simp)
apply (erule ssubst)
apply (case_tac "wx")
 apply (erule_tac [!] ssubst)
 apply simp_all
apply (case_tac "nat - length list", simp_all)
done

subsection {* rem\_initial *}

lemma remove_b_empty[rule_format]:"rem_initial b list = [] \<longrightarrow> list = replicate (length list) b "
apply (induct_tac "list")
 apply simp
apply simp
apply clarify
done

lemma remove_b_empty_not_b[rule_format]:
      "rem_initial b list = [] \<longrightarrow> rem_initial (NOT b) list = list"
apply (induct_tac list)
 apply simp
apply clarify
apply simp
apply (case_tac "b=a")
 apply simp
 apply (case_tac a)
  apply simp+
done
lemma rem_initial_length: "length (rem_initial b w) \<le>  length w"
  apply (rule bit_list_induct [of _ w]) 
  apply (simp_all (no_asm),safe,simp_all)
done
lemma repl_remove[rule_format]:"(length list) = l \<longrightarrow> replicate (l - (length (rem_initial b list))) b @ rem_initial b list = list "
apply clarify
apply (induct_tac list)
 apply simp
apply simp
apply (case_tac "b=a")
 apply simp
 apply (frule replicate_suc)
 apply (subgoal_tac "(Suc (length list - length (rem_initial a list))) = (Suc (length list) - length (rem_initial a list))")
  apply simp
 apply (subgoal_tac "length (rem_initial a list) \<le> length list")
  apply (frule Suc_diff_le)
  apply simp_all
 apply (simp_all add:rem_initial_length)
 using Suc_diff_le rem_initial_length 
 apply auto[1]
 using Suc_diff_le rem_initial_length 
 apply auto
done

lemma rem_initial_hd [rule_format] : "a = hd l \<longrightarrow> l \<noteq> [] \<longrightarrow> rem_initial a l \<noteq> l"
apply clarify
apply (case_tac l)
apply simp
apply simp
apply (cut_tac b = a and w = list in rem_initial_length)
apply simp
done
 
lemma rem_initial_hd_inv [rule_format] : "rem_initial a l \<noteq> l \<longrightarrow> a = hd l"
by (induct l) simp_all

lemma rem_initial_bv_msb [rule_format] : "rem_initial a l \<noteq> l \<longrightarrow> a = bv_msb l"
apply clarify
apply (case_tac l)
apply simp
apply (drule rem_initial_hd_inv)
apply (simp add: bv_msb_def)
done

lemma rem_initial_not_hd_same [rule_format] : "rem_initial a l = l \<longrightarrow> l \<noteq> [] \<longrightarrow> hd l \<noteq> a"
apply clarify
apply (case_tac l)
apply simp
apply simp
apply (cut_tac b = a and w = list in rem_initial_length)
apply simp
done

lemma remove_replicate_b_empty [rule_format] : "rem_initial b (replicate n b) = []"
apply (induct n)
apply simp+
done

lemma rem_initial_cons [rule_format] : "rem_initial a l = x # xs \<longrightarrow> x \<noteq> a"
apply (induct l)
apply simp
apply clarify
apply simp
apply (case_tac " a = aa")
 apply simp
apply simp
done

subsection {* bv\_to\_nat and nat\_to\_bv *}

fun
  nat_to_bv_helper :: "nat => bit list => bit list"
where
  Zeroo:"nat_to_bv_helper 0 bs = bs"
|  Succ:"nat_to_bv_helper (Suc n) bs = 
          (nat_to_bv_helper (Suc n div 2) ((if Suc n mod 2 = 0 then (0::bit) 
                                    else (1::bit))#bs))"

definition
  nat_to_bv :: "nat => bit list" where
  "nat_to_bv n = nat_to_bv_helper n []"


lemma n_div_2_cases:
  assumes zero: "(n::nat) = 0 ==> R"
  and     div : "[| n div 2 < n ; 0 < n |] ==> R"
  shows         "R"
proof (cases "n = 0")
  assume "n = 0"
  thus R by (rule zero)
next
  assume "n ~= 0"
  hence "0 < n" by simp
  hence "n div 2 < n" by arith
  from this and `0 < n` show R by (rule div)
qed

lemma unfold_nat_to_bv_helper:
  "nat_to_bv_helper b l = nat_to_bv_helper b [] @ l"
proof -
  have "\<forall>l. nat_to_bv_helper b l = nat_to_bv_helper b [] @ l"
  proof (induct b rule: less_induct)
    fix n
    assume ind: "!!j. j < n ==> \<forall> l. nat_to_bv_helper j l = nat_to_bv_helper j [] @ l"
    show "\<forall>l. nat_to_bv_helper n l = nat_to_bv_helper n [] @ l"
    proof
      fix l
      show "nat_to_bv_helper n l = nat_to_bv_helper n [] @ l"
      proof (cases "n < 0")
        assume "n < 0"
        thus ?thesis
          by simp
      next
        assume "~n < 0"
        show ?thesis
        proof (rule n_div_2_cases [of n])
          assume [simp]: "n = 0"
          show ?thesis
            apply simp
            done
        next
          assume n2n: "n div 2 < n"
          assume [simp]: "0 < n"
          hence n20: "0 \<le> n div 2"
            by arith
          from ind [of "n div 2"] and n2n n20
          have ind': "\<forall>l. nat_to_bv_helper (n div 2) l = nat_to_bv_helper (n div 2) [] @ l"
            by blast
          show ?thesis
            apply (cases n)
            apply simp_all
            apply (metis Cons_eq_appendI append_eq_appendI  ind'  self_append_conv2)
            done
        qed
      qed
    qed
  qed
  thus ?thesis ..
qed

lemma nat_to_bv_non0 [simp]:
   "n\<noteq>0 ==> nat_to_bv n = nat_to_bv (n div 2) @ [if n mod 2 = 0 then 0 else 1]"
proof -
  assume n: "n\<noteq>0"
  show ?thesis
  proof -
    have "Suc (n - Suc 0) = n"
      by (metis Suc_pred n n_div_2_cases)
    then show ?thesis
      using MoreWord.Succ nat_to_bv_def unfold_nat_to_bv_helper
      by  metis
  qed
qed

lemma nat_to_bv_one: 
      "nat_to_bv 1 = [(1::bit)]"
  unfolding nat_to_bv_def
  by simp

lemma nat_to_bv_Suc_0_eq_One: 
      "nat_to_bv (Suc 0) = [(1::bit)]"
  unfolding nat_to_bv_def
  by simp

lemma bv_to_nat_Nil [simp]: "bv_to_nat [] = 0"
  by (simp add: bv_to_nat_def)

lemma bv_to_nat_helper [simp]: "bv_to_nat (b # bs) = bitval b * 2 ^ length bs + bv_to_nat bs"
proof -
  let ?bv_to_nat' = "foldl (\<lambda>bn b. 2 * bn + bitval b)"
  have helper: "!!base. ?bv_to_nat' base bs = base * 2 ^ length bs + ?bv_to_nat' 0 bs"
  proof (induct bs)
    case Nil
    show ?case by simp
  next
    case (Cons x xs base)
    show ?case
      apply (simp only: foldl_Cons)
      apply (subst Cons [of "2 * base + bitval x"])
      apply simp
      apply (subst Cons [of "bitval x"])
      apply (simp add: add_mult_distrib)
      done
  qed
  show ?thesis by (simp add: bv_to_nat_def) (rule helper)
qed

lemma bv_to_nat0 [simp]: 
     "bv_to_nat (0#bs) = bv_to_nat bs"
  by (simp add: bv_to_nat_def) 

lemma bv_to_nat1 [simp]: "bv_to_nat (1#bs) = 2 ^ length bs + bv_to_nat bs"
  by (simp)

lemma bv_to_nat_upper_range: "bv_to_nat w < 2 ^ length w" 
proof (induct w, simp_all)
  fix b bs
  assume "bv_to_nat bs < 2 ^ length bs"
  show "bitval b * 2 ^ length bs + bv_to_nat bs < 2 * 2 ^ length bs"
  proof (cases b, simp_all)
    have "bv_to_nat bs < 2 ^ length bs" by fact
    also have "... < 2 * 2 ^ length bs" by auto
    finally show "bv_to_nat bs < 2 * 2 ^ length bs" by simp
  next
    have "bv_to_nat bs < 2 ^ length bs" by fact
    hence "2 ^ length bs + bv_to_nat bs < 2 ^ length bs + 2 ^ length bs" by arith
    also have "... = 2 * (2 ^ length bs)" by simp
    finally show "bv_to_nat bs < 2 ^ length bs" by simp
  qed
qed

lemma bv_to_nat_less_power: "length v \<le> a \<Longrightarrow> bv_to_nat v < 2 ^ a"
apply (insert bv_to_nat_upper_range[of v])
apply (frule power_increasing[of "length v" a "2::nat"])
 apply simp
apply (simp (no_asm_simp))
done

(* TODO: Is not "bv_msb list = (1::bit)" more succinct then "list \<noteq> []" and
         "(hd list) = (1::bit)"? -- see lemma Word.bv_msb_one *)
lemma bit_list_cases:
  assumes empty: "w = [] ==> P w"
  and     zero:  "!!bs. w = (0::bit) # bs ==> P w"
  and     one:   "!!bs. w = (1::bit) # bs ==> P w"
  shows   "P w"
proof (cases w)
  assume "w = []"
  thus ?thesis by (rule empty)
next
  fix b bs
  assume [simp]: "w = b # bs"
  show "P w"
  proof (cases b)
    assume "b = (0::bit)"
    hence "w = (0::bit) # bs" by simp
    thus ?thesis by (rule zero)
  next
    assume "b = (1::bit)"
    hence "w = (1::bit) # bs" by simp
    thus ?thesis by (rule one)
  qed
qed

definition BitN :: "nat \<Rightarrow> bit \<Rightarrow> nat" (infixl "BITN" 90) where
  "k BITN b = bitval b + k + k"

primrec bv_to_nat_aux :: " nat  \<Rightarrow>  bit list \<Rightarrow> nat" where
  Nil: "bv_to_nat_aux w  []  = w"
  | Cons: "bv_to_nat_aux  w (b # bs)  = 
      bv_to_nat_aux  (w BITN (if b = (1::bit) then 1 else 0)) bs"

lemma bla41: 
   "bv_to_nat_aux base bs = base * 2 ^ length bs + bv_to_nat_aux 0 bs"
proof -
  have bla1: "\<forall>a b. b BITN a = bitval a + b + b"
    by (simp add: BitN_def)
  have bla4: "\<forall>a b. (b BITN a) = (2::nat) * b + bitval a"
    by (simp add: bla1)
  show ?thesis
  proof (induct bs arbitrary: base)               
    case Nil
    then show ?case by simp 
  next
   case (Cons x xs)
   show ?case 
    apply (simp only: bv_to_nat_aux.simps )
    apply (simp add: bla4)
    apply  (smt Cons.hyps One_nat_def Suc_eq_plus1 combine_common_factor mult.assoc mult.commute)
    done
  qed
qed

lemma bv_to_nat_rew_msb: 
  "bv_msb w = (1::bit) \<Longrightarrow>  bv_to_nat w = 2 ^ (length w - 1) + bv_to_nat (tl w)"
  apply (rule bit_list_cases [of w])
  apply (simp add: bv_msb_def  BitN_def)+
  done


lemma bv_msb_one: "bv_msb w = (1::bit) \<Longrightarrow>   bv_to_nat w \<noteq> (0::nat)"
  by (cases w, simp_all add: bv_msb_def)

lemma bv_to_nat_non_zero:
  assumes "list \<noteq> []" and "(hd list) = (1::bit)"
  shows "(bv_to_nat list \<noteq> 0)"
proof -
  from assms have "bv_msb list = (1::bit)" by (cases list, simp_all add: bv_msb_def)
  thus ?thesis by (simp add: bv_msb_one bv_msb_def)
qed

lemma bv_to_nat_zero_eq: "(bv_to_nat xs = 0) = (\<forall>x\<in>set xs. x=(0::bit))"
proof (induct xs)
  case (Cons x xs) thus ?case
    apply (cases "bv_msb (x#xs) = (1::bit)")
    apply  (simp add: bv_msb_one)
    apply (cases x, simp_all add: bv_msb_def)
    done
qed simp

lemma bv_to_nat_pos_eq: "(0<bv_to_nat xs) = ((1::bit)\<in>set xs)"
proof (induct xs)
  case (Cons x xs) show ?case
  proof (cases "bv_msb (x#xs) = (1::bit)")
    case True thus ?thesis by (simp add: bv_msb_one bv_msb_def)
  next
    case False with Cons show ?thesis by (cases x) simp_all
  qed
qed simp

lemma nat_to_bv_of_neg_is_Nil: 
      "n \<le> 0 \<Longrightarrow> nat_to_bv n = Nil"
  by (simp add: nat_to_bv_def)

text {* The following lemma is a variation of
 lemma @{text length_nat_to_bv_upper_limit}, which can be found in the Word
 library.  However, the latter lemma is not so easy to use.  Thus, we thought
 about replacing the lemma by the following one.  Hence, the following proof
 does not use the original lemma @{text length_nat_to_bv_upper_limit}.
*}
lemmas [simp del] = nat_to_bv_non0

lemma bv_to_nat_dist_append:
  "bv_to_nat (l1 @ l2) = bv_to_nat l1 * 2 ^ length l2 + bv_to_nat l2"
proof -
  have "\<forall>l2. bv_to_nat (l1 @ l2) = bv_to_nat l1 * 2 ^ length l2 + bv_to_nat l2"
  proof (induct l1, simp_all)
    fix x xs
    assume ind: "\<forall>l2. bv_to_nat (xs @ l2) = bv_to_nat xs * 2 ^ length l2 + bv_to_nat l2"
    show "\<forall>l2::bit list. bitval x * 2 ^ (length xs + length l2) + bv_to_nat xs * 2 ^ length l2 = (bitval x * 2 ^ length xs + bv_to_nat xs) * 2 ^ length l2"
    proof
      fix l2
      show "bitval x * 2 ^ (length xs + length l2) + bv_to_nat xs * 2 ^ length l2 = (bitval x * 2 ^ length xs + bv_to_nat xs) * 2 ^ length l2"
      proof -
        have "(2::nat) ^ (length xs + length l2) = 2 ^ length xs * 2 ^ length l2"
          by (induct ("length xs")) simp_all
        hence "bitval x * 2 ^ (length xs + length l2) + bv_to_nat xs * 2 ^ length l2 =
          bitval x * 2 ^ length xs * 2 ^ length l2 + bv_to_nat xs * 2 ^ length l2"
          by simp
        also have "... = (bitval x * 2 ^ length xs + bv_to_nat xs) * 2 ^ length l2"
          by (simp add: ring_distribs)
        finally show ?thesis by simp
      qed
    qed
  qed
  thus ?thesis ..
qed


lemma bv_nat_bv [simp]: "bv_to_nat (nat_to_bv n) = n"
proof (induct n rule: less_induct)
  fix n
  assume ind: "!!j. j < n ==> bv_to_nat (nat_to_bv j) = j"
  show "bv_to_nat (nat_to_bv n) = n"
  proof (rule n_div_2_cases [of n])
    assume "n = 0" then show ?thesis by (simp add: nat_to_bv_def)
  next
    assume nn: "n div 2 < n"
    assume n0: "0 < n"
    from ind and nn
    have ind': "bv_to_nat (nat_to_bv (n div 2)) = n div 2" by blast
    from n0 have n0': "n \<noteq> 0" by simp
    show ?thesis
      apply (subst nat_to_bv_def)
      apply (cases n)
      apply (simp_all only: nat_to_bv_helper.simps )
      apply (simp only: n0' if_False)
      apply (subst unfold_nat_to_bv_helper)
      apply (subst bv_to_nat_dist_append)
      apply (fold nat_to_bv_def)
      apply (simp_all add: ind' split del: if_split)
      apply (cases "n mod 2 = 0")
      using ind' apply force
      proof -
        fix nat :: nat
        assume a1: "n = Suc nat"
        assume a2: "n mod 2 \<noteq> 0"
        then have "2 * (n div 2) + 1 = n"
          by (metis (no_types) mult_div_mod_eq not_mod_2_eq_0_eq_1)
        then show "bv_to_nat (nat_to_bv (Suc nat div 2)) * 2 + 
                   bitval (if Suc nat mod 2 = 0 then 0 else 1) = Suc nat"
          using a2 a1 ind' by force
      qed
  qed
qed

lemma length_norm_unsigned_le [simp]: "length (norm_unsigned w) \<le> length w"
  by (rule bit_list_induct) simp_all

lemma norm_unsigned_result: "norm_unsigned xs = [] \<or> bv_msb (norm_unsigned xs) = 1"
proof (rule length_induct [of _ xs])
  fix xs :: "bit list"
  assume ind: "\<forall>ys. length ys < length xs --> norm_unsigned ys = [] \<or> bv_msb (norm_unsigned ys) = 1"
  show "norm_unsigned xs = [] \<or> bv_msb (norm_unsigned xs) = 1"
  proof (rule bit_list_cases [of xs],simp_all add: )
    fix bs
    assume [simp]: "xs = 0#bs"
    from ind
    have "length bs < length xs --> norm_unsigned bs = [] \<or> bv_msb (norm_unsigned bs) = 1" ..
    thus "norm_unsigned bs = [] \<or> bv_msb (norm_unsigned bs) = 1" by simp
  next
    show " \<And>bs. xs = 1 # bs \<Longrightarrow> bv_msb (1 # bs) = 1"
    by (simp add: bv_msb_def)
  qed
qed

lemma rem_initial_append1:
  assumes "rem_initial b xs ~= []"
  shows   "rem_initial b (xs @ ys) = rem_initial b xs @ ys"
  using assms by (induct xs) auto

lemma rem_initial_append2:
  assumes "rem_initial b xs = []"
  shows   "rem_initial b (xs @ ys) = rem_initial b ys"
  using assms by (induct xs) auto

lemma norm_unsigned_length [intro!]:
     "length (norm_unsigned w) \<le> length w"
by (simp add: rem_initial_length)

lemma norm_unsigned_equal:
  "length (norm_unsigned w) = length w ==> norm_unsigned w = w"
by (metis bv_extend_def bv_extend_norm_unsigned2 le_refl repl_remove)

lemma bv_extend_norm_unsigned: 
     "bv_extend (length w) 0 (norm_unsigned w) = w"
by (simp add: bv_extend_def repl_remove)

lemma norm_unsigned_append1 [simp]:
  "norm_unsigned xs \<noteq> [] ==> norm_unsigned (xs @ ys) = norm_unsigned xs @ ys"
  by (simp add: rem_initial_append1)

lemma norm_unsigned_append2 [simp]:
  "norm_unsigned xs = [] ==> norm_unsigned (xs @ ys) = norm_unsigned ys"
by (simp add:rem_initial_append2)

lemma bv_to_nat_zero_imp_empty:
  "bv_to_nat w = 0 ==> norm_unsigned w = []"
by (atomize (full), induct w rule: bit_list_induct) simp_all

lemma bv_to_nat_nzero_imp_nempty:
  "bv_to_nat w \<noteq> 0 ==> norm_unsigned w \<noteq> []"
by (induct w rule: bit_list_induct) simp_all

lemma norm_empty_bv_to_nat_zero:
  assumes nw: "norm_unsigned w = []"
  shows       "bv_to_nat w = 0"
proof -
  have "bv_to_nat w = bv_to_nat (norm_unsigned w)" by simp
  also have "... = bv_to_nat []" by (subst nw) (rule refl)
  also have "... = 0" by simp
  finally show ?thesis .
qed

lemma bv_to_nat_lower_limit:
  assumes w0: "0 < bv_to_nat w"
  shows "2 ^ (length (norm_unsigned w) - 1) \<le> bv_to_nat w"
proof -
  from w0 and norm_unsigned_result [of w]
  have msbw: "bv_msb (norm_unsigned w) = 1"
    by (auto simp add: norm_empty_bv_to_nat_zero bv_msb_def)
  have "2 ^ (length (norm_unsigned w) - 1) \<le> bv_to_nat (norm_unsigned w)"
    by (subst bv_to_nat_rew_msb [OF msbw],simp)
  thus ?thesis by simp
qed

lemma nat_helper1:
  assumes ass: "nat_to_bv (bv_to_nat w) = norm_unsigned w"
  shows        "nat_to_bv (2 * bv_to_nat w + bitval x) = norm_unsigned (w @ [x])"
proof (cases x)
  assume [simp]: "x = 1"
  have "nat_to_bv (Suc (2 * bv_to_nat w) div 2) @ [1] =
      nat_to_bv ((1 + 2 * bv_to_nat w) div 2) @ [1]"
    by (simp add: add.commute)
  also have "... = nat_to_bv (bv_to_nat w) @ [1]"
    by (subst div_add1_eq) simp
  also have "... = norm_unsigned w @ [1]"
    by (subst ass) (rule refl)
  also have "... = norm_unsigned (w @ [1])"
              apply (cases "norm_unsigned w") 
              apply simp_all 
              done
  finally have "nat_to_bv (Suc (2 * bv_to_nat w) div 2) @ [1] = norm_unsigned (w @ [1])" .
  then show ?thesis by (simp add: nat_to_bv_non0)
next
  assume [simp]: "x = 0"
  show ?thesis
  proof (cases "bv_to_nat w = 0")
    assume "bv_to_nat w = 0"
    thus ?thesis
      by (simp add: bv_to_nat_zero_imp_empty nat_to_bv_def)
  next
    assume "bv_to_nat w \<noteq> 0"
    thus ?thesis
      apply simp
      apply (subst nat_to_bv_non0)
      apply simp
      apply auto
      apply (subst ass)
      apply (cases "norm_unsigned w")
      apply (simp_all add: norm_empty_bv_to_nat_zero)
      done
  qed
qed

lemma nat_helper2: "nat_to_bv (2 ^ length xs + bv_to_nat xs) = 1 # xs"
proof -
  have "\<forall>xs. nat_to_bv (2 ^ length (rev xs) + bv_to_nat (rev xs)) = 1 # (rev xs)" (is "\<forall>xs. ?P xs")
  proof
    fix xs
    show "?P xs"
    proof (rule length_induct [of _ xs])
      fix xs :: "bit list"
      assume ind: "\<forall>ys. length ys < length xs --> ?P ys"
      show "?P xs"
      proof (cases xs)
        assume "xs = []"
        then show ?thesis by (simp add: nat_to_bv_non0 nat_to_bv_def)
      next
        fix y ys
        assume [simp]: "xs = y # ys"
        show ?thesis
          apply simp
          apply (subst bv_to_nat_dist_append)
          apply simp
        proof -
          have "nat_to_bv (2 * 2 ^ length ys + (bv_to_nat (rev ys) * 2 + bitval y)) =
            nat_to_bv (2 * (2 ^ length ys + bv_to_nat (rev ys)) + bitval y)"
            by (simp add: add_ac mult_ac)
          also have "... = nat_to_bv (2 * (bv_to_nat (1#rev ys)) + bitval y)"
            by simp
          also have "... = norm_unsigned (1#rev ys) @ [y]"
          proof -
            from ind
            have "nat_to_bv (2 ^ length (rev ys) + bv_to_nat (rev ys)) = 1# rev ys"
              by auto
            hence [simp]: "nat_to_bv (2 ^ length ys + bv_to_nat (rev ys)) = 1 # rev ys"
              by simp
            show ?thesis
              apply (subst nat_helper1)
              apply simp_all
              done
          qed
          also have "... = (1#rev ys) @ [y]"
            by simp
          also have "... = 1 # rev ys @ [y]"
            by simp
          finally show "nat_to_bv (2 * 2 ^ length ys + (bv_to_nat (rev ys) * 2 + bitval y)) =
                         1 # rev ys @ [y]" .
        qed
      qed
    qed
  qed
  hence "nat_to_bv (2 ^ length (rev (rev xs)) + bv_to_nat (rev (rev xs))) =
          1 # rev (rev xs)" ..
  thus ?thesis by simp
qed

lemma nat_bv_nat [simp]: "nat_to_bv (bv_to_nat w) = norm_unsigned w"
proof (rule bit_list_induct [of _ w],simp_all add: )
  fix xs
  assume "nat_to_bv (bv_to_nat xs) = norm_unsigned xs"
  have "bv_to_nat xs = bv_to_nat (norm_unsigned xs)" by simp
  have "bv_to_nat xs < 2 ^ length xs"
    by (rule bv_to_nat_upper_range)
  show "nat_to_bv (2 ^ length xs + bv_to_nat xs) = 1 # xs"
    by (rule nat_helper2)
 next
   show "nat_to_bv 0 = []"
   by (simp add: nat_to_bv_of_neg_is_Nil) 
qed


lemma norm_unsigned_nat_to_bv [simp]:
  "norm_unsigned (nat_to_bv n) = nat_to_bv n"
proof -
  have "norm_unsigned (nat_to_bv n) = nat_to_bv (bv_to_nat (norm_unsigned (nat_to_bv n)))"
    apply (subst nat_bv_nat , simp add: nat_to_bv_def)
    using bv_to_nat_type nat_bv_nat
    apply metis
    done
  also have "... = nat_to_bv n" by simp
  finally show ?thesis .
qed

lemma nat_upper_limit_impl_length_nat_to_bv_limit:
  assumes nk: "n < 2 ^ k"
  shows       "length (nat_to_bv n) \<le> k"
proof (cases "n = 0")
  case True
  thus ?thesis
    by (simp add: nat_to_bv_def )
next
  case False
  hence n0: "0 < n" by simp
  show ?thesis
  proof (rule ccontr)
    assume "~ length (nat_to_bv n) \<le> k"
    hence "k < length (nat_to_bv n)"
      by simp
    hence "k \<le> length (nat_to_bv n) - 1"
      by arith
    hence "(2::nat) ^ k \<le> 2 ^ (length (nat_to_bv n) - 1)"
      by simp
    also have "... = 2 ^ (length (norm_unsigned (nat_to_bv n)) - 1)"
      apply (simp only: nat_to_bv_def)
      using nat_to_bv_def norm_unsigned_nat_to_bv
      apply auto
      done 
    also have "... \<le> bv_to_nat (nat_to_bv n)"
      by (rule bv_to_nat_lower_limit,simp add: n0)
    also have "... = n"
      by simp
    finally have "2 ^ k \<le> n" .
    with n0
    have "2 ^ k - 1 < n"
      by arith
    with nk
    show False
      by arith
  qed
qed

lemma length_nat_to_bv_upper_limit_impl_nat_limit:
  "length (nat_to_bv n) \<le> k \<Longrightarrow> n < 2 ^ k"
by (frule bv_to_nat_less_power, simp)


lemma length_nat_to_bv_lower_limit:
  assumes nk: "2 ^ k \<le> n"
  shows       "k < length (nat_to_bv n)"
proof (rule ccontr)
  assume "~ k < length (nat_to_bv n)"
  hence lnk: "length (nat_to_bv n) \<le> k" by simp
  have "n = bv_to_nat (nat_to_bv n)" by simp
  also have "... < 2 ^ length (nat_to_bv n)"
    by (rule bv_to_nat_upper_range)
  also from lnk have "... \<le> 2 ^ k" by simp
  finally have "n < 2 ^ k" .
  with nk show False by simp
qed


lemma length_nat_to_bv_lower_limit_2: 
      "k < length (nat_to_bv n) \<Longrightarrow> 2 ^ k \<le> n"
  using nat_upper_limit_impl_length_nat_to_bv_limit not_le 
  by blast


lemma bv_to_nat_replicate_Zero_append:
    "bv_to_nat (replicate n (0::bit) @ xs) = bv_to_nat xs"
by (induct n, simp+)

lemma bv_to_nat_replicate_Zero: "bv_to_nat (replicate w (0::bit)) = 0"
by (rule bv_to_nat_replicate_Zero_append[where xs=Nil, simplified])

lemma bv_to_nat_and_one_replicate_zero:
      "length wx \<le> Suc n  \<Longrightarrow> 
       bv_to_nat (map (\<lambda>(x, y). x AND y) (zip (bv_extend (length wx) (0::bit) 
       ((1::bit) # replicate n (0::bit))) (bv_extend (Suc n) (0::bit) wx))) = 
       bitval (hd (replicate (Suc n - length wx) (0::bit) @ wx)) * 2 ^ n"
apply (simp add: bv_extend_def)
apply (case_tac "replicate (Suc n - length wx) (0::bit) @ wx")
 apply simp
 apply (erule conjE)
 apply simp
apply simp
apply (subgoal_tac "length list = n")
 prefer 2
 apply (subgoal_tac "length (replicate (Suc n - length wx) (0::bit) @ wx) = Suc n")

apply fastforce
apply (metis add.commute le_add_diff_inverse length_append length_replicate)
using and_zero bv_to_nat_replicate_Zero 
apply auto
done

lemma bv_to_nat_is_zero_impl_replicate_zeros[rule_format]: 
     "bv_to_nat wx = 0 \<longrightarrow> wx = replicate (length wx) (0::bit)"
apply (induct wx)
 apply simp
apply (rule impI)
apply simp
apply (case_tac a, simp_all)
done

lemma bv_to_nat_replicate_One: "bv_to_nat (replicate n (1::bit)) = 2^n - 1"
  by (induct_tac "n", simp_all)

definition
  bv_to_int :: "bit list => int" where
  "bv_to_int w =
    (case bv_msb w of 0 => int (bv_to_nat w)
    | 1 => - int (bv_to_nat (bv_not w) + 1))"

lemma bv_to_int_replicate_One_Zero:
  "bv_to_int (replicate (Suc m) (1::bit) @ replicate n (0::bit)) = - (2^n)"
  apply (simp add: bv_to_int_def)
  apply (simp add: bv_msb_def)
  apply (subgoal_tac "bv_to_nat (replicate m (0::bit) @ replicate n (1::bit)) = 2^n - 1")
  apply  simp
  apply  (subgoal_tac "int (2^n - Suc 0) = 2^n - 1", simp)
  apply  (simp add: of_nat_diff)
  apply (induct m)
  apply  simp_all
  apply (simp add: bv_to_nat_replicate_One)
done

lemma nat_to_bv_inj: "nat_to_bv x = nat_to_bv y \<Longrightarrow> x = y"
apply (insert bv_nat_bv[of x])
apply (insert bv_nat_bv[of y])
apply (rotate_tac -2)
apply (erule subst)
apply simp
done

lemma bv_via_nat_bv_nat_decompose_sym: 
      "replicate (length bs - length (nat_to_bv (bv_to_nat bs))) 
       (0::bit) @ nat_to_bv (bv_to_nat bs) = bs"
apply (induct bs)
 apply (simp add: nat_to_bv_def)
apply (case_tac a)
 apply simp
using Suc_diff_le apply auto[1]
apply (simp add: nat_helper2)
done

lemmas bv_via_norm_unsigned_decompose_sym = bv_via_nat_bv_nat_decompose_sym [simplified]

lemma nat_to_bv_is_Nil_impl_nat_is_0: "nat_to_bv n = [] \<Longrightarrow> n = 0"
apply (insert bv_nat_bv[of n])
apply (rotate_tac -1, erule subst)
apply (erule ssubst)
apply simp
done

lemma nat_to_bv_is_Zero_impl_False:
      "nat_to_bv n = [(0::bit)] \<Longrightarrow> False"
using bv_nat_bv bv_to_nat0 list.distinct(1) nat_bv_nat rem_initial.simps(1)
by  metis

lemma nat_to_bv_Cons_impl_head_is_One_ind[rule_format]:
  "! b. rev (nat_to_bv b) = xs @ [x] \<longrightarrow> x = (1::bit)"
apply (induct xs)
 apply (intro allI)
 apply (cases x)
  apply clarsimp
  apply (rule nat_to_bv_is_Zero_impl_False, simp)
 apply simp
apply (intro impI allI)
apply (erule_tac x = "b div 2" in allE)
apply simp
apply (drule mp)
prefer 2
 apply simp
apply (case_tac "b=0")
apply  simp
apply (simp_all add: nat_to_bv_non0 nat_to_bv_def)
using nat_to_bv_def nat_to_bv_non0 
apply auto
done

lemma nat_to_bv_Cons_impl_head_is_One: 
      "nat_to_bv b = x # xs \<Longrightarrow> x = (1::bit)"
apply (insert nat_to_bv_Cons_impl_head_is_One_ind[of b "rev xs" x])
apply simp
done

lemma nat_to_bv_non0_impl_hd_one[rule_format]:
      "0<b \<longrightarrow>  (hd (nat_to_bv b)) = (1::bit)"
apply clarsimp
apply (case_tac "nat_to_bv b ")
apply (simp add: nat_to_bv_non0)
 apply (frule_tac x = "a" and  xs = "list" in nat_to_bv_Cons_impl_head_is_One)
apply simp 
done

lemma nat_to_bv_pos_not_nil [rule_format] : 
      "a > 0 \<longrightarrow> (\<exists> ls. nat_to_bv a = (1::bit) # ls)"
apply clarify
apply (case_tac "nat_to_bv a")
 apply (frule nat_to_bv_is_Nil_impl_nat_is_0)
 apply simp
apply (frule nat_to_bv_Cons_impl_head_is_One)
apply simp
done

lemma norm_signed_Zero_nat_to_bv:
      "0 < m \<Longrightarrow> 
       norm_signed ((0::bit) # nat_to_bv m) = (0::bit) # nat_to_bv m"
apply (case_tac "nat_to_bv m")
 apply simp
 apply (drule nat_to_bv_is_Nil_impl_nat_is_0)
 apply simp
apply (frule nat_to_bv_Cons_impl_head_is_One)
apply simp
done

lemma norm_signed_zero_nat_to_bv: 
     "nat_to_bv wx \<noteq> [] \<Longrightarrow> 
      norm_signed ((0::bit) # nat_to_bv wx) = (0::bit) # nat_to_bv wx"
apply (case_tac "nat_to_bv wx")
 apply simp
apply (frule nat_to_bv_Cons_impl_head_is_One)
apply (erule ssubst)
apply (erule ssubst)
apply simp
done

lemma norm_signed_One_bv_not_nat_to_bv:
      "norm_signed ((1::bit) # bv_not (nat_to_bv m)) = 
       (1::bit) # bv_not (nat_to_bv m)"
apply (case_tac "nat_to_bv m")
 apply simp
apply (frule nat_to_bv_Cons_impl_head_is_One)
apply simp
done

lemma add_bv_to_nat_is_bv_to_nat_append: 
      "length bx = k \<Longrightarrow> 
       bv_to_nat (ax @ replicate k (0::bit)) + bv_to_nat bx = 
       bv_to_nat (ax @ bx)"
apply (subst bv_to_nat_dist_append)
apply (subst bv_to_nat_dist_append)
apply simp
apply (rule bv_to_nat_replicate_Zero)
done

lemma nat_to_bv_is_replicate_Zero_impl_zero:
  "nat_to_bv k = replicate n (0::bit) \<Longrightarrow> k = 0"
  -- "simplified version of the former lemma @{text replicate_null_replicate}"
apply (case_tac "nat_to_bv k")
 apply (erule nat_to_bv_is_Nil_impl_nat_is_0)
apply (subgoal_tac "a = (1::bit)")
 apply simp
 apply (case_tac n)
  apply simp
 apply simp
apply (erule nat_to_bv_Cons_impl_head_is_One)
done

lemma nat_to_bv_without_bv_msb_decompose_sym:
   "nat_to_bv k = b # bs \<Longrightarrow>
      replicate (length bs - length (nat_to_bv (k - 2 ^ (length bs)))) (0::bit) @ 
      nat_to_bv (k - 2 ^ (length bs)) = bs"
apply (frule nat_to_bv_Cons_impl_head_is_One)
apply (subgoal_tac "k = bv_to_nat ([(1::bit)] @ bs)")
 prefer 2
 apply clarsimp
 apply (insert bv_nat_bv[of k])
 apply (simp del: bv_nat_bv)
apply (simp only: bv_to_nat_dist_append)
apply simp
apply (rule bv_via_norm_unsigned_decompose_sym)
done

lemma bv_to_nat_as_complement:
  "bv_to_nat xs = 2 ^ (length xs) - bv_to_nat (bv_not xs) - 1"
apply (induct xs)
 apply simp
apply simp
apply (subgoal_tac "bv_to_nat (a # xs) = bv_to_nat [a] * 2 ^ length xs + bv_to_nat xs")
 apply (rotate_tac 1)
 apply (erule ssubst)
 apply (erule ssubst)
 apply (case_tac "a")
  apply simp
  apply (subgoal_tac "bv_to_nat ((1::bit) # bv_not xs) = bv_to_nat [(1::bit)] * 2 ^ length (bv_not xs) + bv_to_nat (bv_not xs)")
   apply (rotate_tac -1)
   apply (erule ssubst)
   apply simp
  apply (subgoal_tac "(1::bit) # bv_not xs = [(1::bit)] @ bv_not xs")
   apply (rotate_tac -1)
   apply (erule ssubst)
 apply clarsimp
 apply (subgoal_tac "2 ^ length xs \<ge> Suc (bv_to_nat (bv_not xs))")
  apply arith
 apply (simp only: Suc_le_eq)
 apply (subgoal_tac "length xs = length (bv_not xs)")
 apply  (simp only: bv_to_nat_upper_range)
 apply simp
apply (subgoal_tac "a # xs = [a] @ xs")
 apply (rotate_tac -1)
 apply (erule ssubst)
apply simp_all
done

lemma complement_bv_eq:
  "-1 - int(bv_to_nat (bv_not xs)) = int(bv_to_nat xs) - 2 ^ (length xs)"
apply (subst bv_to_nat_as_complement [of xs])
apply (subgoal_tac "int ((2::nat) ^ length xs - bv_to_nat (bv_not xs) - (1::nat))
                  = int ((2::nat) ^ length xs) - int(bv_to_nat (bv_not xs))- 1")
apply simp
apply (subgoal_tac "2 ^ length xs \<ge> Suc (bv_to_nat (bv_not xs))")
apply  arith
apply (rule Suc_leI)
apply (subgoal_tac "length xs = length (bv_not xs)")
 apply (simp only: bv_to_nat_upper_range)
apply simp
done

lemma nat_to_bv_helper_mult_power2[rule_format]: 
     " 0 < x \<longrightarrow> nat_to_bv_helper (2^n * x) xs = 
           nat_to_bv_helper x (replicate n (0::bit) @ xs)"
proof (induct n, auto, cases xs, hypsubst)
  fix na :: nat
  assume a1: "0 < x"
  assume a2: "nat_to_bv_helper (2 ^ na * x) [] = nat_to_bv_helper x (replicate na 0 @ [])"
  have f3: "0 < 2 * 2 ^ na * x"
    using a1 by fastforce
  then have f4: "Suc (2 * 2 ^ na * x - Suc 0) = 2 * (2 ^ na * x)"
    by simp
  then have "Suc (2 * 2 ^ na * x - Suc 0) mod 2 = 0"
    by (metis mod_mult_self1_is_0)
  then have "nat_to_bv_helper (Suc (2 * 2 ^ na * x - Suc 0)) [] = 
             nat_to_bv_helper (Suc (2 * 2 ^ na * x - Suc 0) div 2) [0]"
    using MoreWord.Succ by presburger
  then show "nat_to_bv_helper (2 * 2 ^ na * x) [] = nat_to_bv_helper x (0 # replicate na 0 @ [])"
    using f4 f3 a2 
    by (metis (no_types) Suc_pred append_assoc append_self_conv 
                         nonzero_mult_div_cancel_left replicate_app_Cons_same 
                         unfold_nat_to_bv_helper zero_not_eq_two)
next
   have *: "2^n \<noteq> (0::nat)" by simp
  show "\<And>n a list.
       0 < x \<Longrightarrow>
       nat_to_bv_helper (2 ^ n * x) xs =
       nat_to_bv_helper x (replicate n 0 @ xs) \<Longrightarrow>
       xs = a # list \<Longrightarrow>
       nat_to_bv_helper (2 * 2 ^ n * x) xs =
       nat_to_bv_helper x (0 # replicate n 0 @ xs)"
      apply hypsubst
      using *
      proof -
        fix na::nat
        fix a list
        assume a1: "0 < x"
        assume a2: "nat_to_bv_helper (2 ^ na * x) (a # list) =
                     nat_to_bv_helper x (replicate na 0 @ (a # list))"
        have f3: "0 < 2 * 2 ^ na * x"
          using a1 by fastforce
        then have f4: "Suc (2 * 2 ^ na * x - Suc 0) = 2 * (2 ^ na * x)"
          by simp
        then have "Suc (2 * 2 ^ na * x - Suc 0) mod 2 = 0"
          by (metis mod_mult_self1_is_0)
        then have "nat_to_bv_helper (Suc (2 * 2 ^ na * x - Suc 0))  (a # list) = 
                   nat_to_bv_helper (Suc (2 * 2 ^ na * x - Suc 0) div 2) (0 #a # list)"
          using MoreWord.Succ by presburger
        then show "nat_to_bv_helper (2 * 2 ^ na * x) (a # list) = 
                   nat_to_bv_helper x (0 # replicate na 0 @ (a # list))"
        using f4 f3 a2 
          apply auto
          proof -
            assume a1: "nat_to_bv_helper (2 ^ na * x) (a # list) = 
                        nat_to_bv_helper x (replicate na 0 @ a # list)"
            assume a2: "nat_to_bv_helper (2 * (2 ^ na * x)) (a # list) = 
                        nat_to_bv_helper (2 ^ na * x) (0 # a # list)"
            have "nat_to_bv_helper x (0 # replicate na 0 @ a # list) = 
                 nat_to_bv_helper x [] @ replicate na 0 @ 0 # a # list"
              by (metis replicate_app_Cons_same unfold_nat_to_bv_helper)
            then show ?thesis
              using a2 a1 by (metis (no_types) Suc_pred append_assoc 
                                    append_same_eq f3 f4 unfold_nat_to_bv_helper)
          qed
       qed
qed
lemma nat_to_bv_mult_power[rule_format]:
      "0 < m \<longrightarrow> nat_to_bv (m * 2 ^ k) = nat_to_bv m @ replicate k (0::bit)"
apply (induct k)
 apply simp
apply (rule impI)
apply (drule mp, assumption)
apply (subst replicate_Suc'[THEN sym])
apply (subst append_assoc[THEN sym])
apply (erule subst)
apply (subst nat_to_bv_non0)
 apply simp
apply simp
done

lemma nat_to_bv_mult_power2[rule_format]: 
      "0 < x \<longrightarrow> nat_to_bv (2^n * x) = nat_to_bv x @ replicate n (0::bit)"
apply clarsimp
apply (simp add: nat_to_bv_def)
apply (subst nat_to_bv_helper_mult_power2, simp)
apply simp
apply (subst unfold_nat_to_bv_helper)
apply simp
done

lemma nat_to_bv_power2[rule_format]: 
      "nat_to_bv (2^n) = (1::bit) # replicate n (0::bit)"
apply (insert nat_to_bv_mult_power2[where x="1" and n="n"])
apply simp
apply (simp add: nat_to_bv_Suc_0_eq_One)
done

lemma nat_to_bv_mult_power_minus[rule_format]:
      "m < 0 \<longrightarrow> nat_to_bv (nat (- (m * 2 ^ k) - 1)) = 
       nat_to_bv (nat (- m - 1)) @ replicate k (1::bit)"
apply (induct k)
 apply simp
apply (rule impI)
apply (drule mp, assumption)
apply (subst replicate_Suc'[THEN sym])
apply (subst append_assoc[THEN sym])
apply (erule subst)
apply (subgoal_tac "m * 2 ^ k < 0")
 prefer 2
 apply (erule i_mult_neg_pos_is_neg)
 apply (rule zero_less_power)
 apply simp
apply (subst nat_to_bv_non0)
 apply simp
apply (subgoal_tac "nat (- (m * 2 ^ Suc k) - 1) mod 2 = 1")
 prefer 2
 apply (subst int_int_eq[THEN sym])
 apply (subst int_mod)
 apply simp
 apply (subgoal_tac "- (m * (2 * 2 ^ k)) - 1 = - (m * 2 ^ Suc k + 1)")
  prefer 2
  apply simp
 apply (rotate_tac -1, erule ssubst)
 apply (subst zmod_zminus1_eq_if)
 apply simp
 apply (subst Divides.semiring_div_class.mod_add_left_eq)
 apply simp+
 apply (simp add: nat_to_bv_def )
apply (rotate_tac -1, erule ssubst)
apply (subgoal_tac "nat (- (m * 2 ^ Suc k) - 1) div 2 = nat (- (m * 2 ^ k) - 1)")
 prefer 2
 apply (subst int_int_eq[THEN sym])
 apply (subst int_div)
 apply simp+
done

lemma nat_to_bv_helper_power2_minus1: 
     "\<forall> xs. nat_to_bv_helper (2 ^ n - Suc 0) xs = replicate n (1::bit) @ xs"
  using One_nat_def bv_to_nat_replicate_One nat_bv_nat nat_to_bv_def 
        norm_unsigned_replicate_One unfold_nat_to_bv_helper
  by metis
 
lemma nat_to_bv_power2_minus1: 
     "nat_to_bv (2^n - Suc 0) = replicate n (1::bit)"
apply (simp add: nat_to_bv_def)
apply (simp add: nat_to_bv_helper_power2_minus1)
done

lemma nat_to_bv_div_2_is_butlast2: 
      "nat_to_bv (n div 2) = butlast (nat_to_bv n)"
apply (case_tac "n")
 apply (simp add: nat_to_bv_def)
apply (subst nat_to_bv_non0[where n="n"])
 apply simp
apply clarsimp
done

lemma nat_to_bv_non_Nil[rule_format]: 
      "nat_to_bv a \<noteq> [] \<longrightarrow> 0 < a"
apply (case_tac a)
apply (auto simp: nat_to_bv_def)
done

lemma nat_to_bv_mod_power2_trivial[rule_format]: 
      "length (nat_to_bv a) \<le> n \<longrightarrow> nat_to_bv (a mod 2^n) = nat_to_bv a"
apply clarsimp
apply (subgoal_tac "a < 2^n")
 apply simp
apply (case_tac "2^n \<le> a")
 apply (frule length_nat_to_bv_upper_limit_impl_nat_limit)
 apply simp
apply simp
done

lemma nat_to_bv_mod_2_last[rule_format]: 
      "0 < a \<longrightarrow> nat_to_bv (a mod 2) = norm_unsigned [last (nat_to_bv a)]"
  using nat_to_bv_non0 nat_to_bv_one 
  by auto

lemma bv_to_nat_take_append_replicate[rule_format]:
  "\<forall>m. bv_to_nat (take (length bv - m) bv @ replicate m (0::bit)) = 
       bv_to_nat bv - bv_to_nat bv mod 2 ^ m"
 apply (induct_tac bv)
  apply (simp_all add: bv_to_nat_replicate_Zero)
 apply (rule allI)
 apply (case_tac "length list < m")
  apply simp
  apply (simp add: bv_to_nat_replicate_Zero)
  apply (subgoal_tac " bv_to_nat (a # list) < 2 ^ m")
   apply simp
  apply (rule_tac y = " 2 ^ length(a # list)" in less_le_trans)
   apply (rule bv_to_nat_upper_range)
  apply (rule power_increasing)
   apply simp
  apply simp
 apply (subgoal_tac "m \<le> length list")
  apply simp
  apply (subgoal_tac "Suc (length list) - m = Suc ( (length list) - m )")
   apply (rotate_tac -1, erule ssubst)
   apply simp
   apply (simp_all add:  )
   apply (case_tac "m = 0")
    apply simp
   apply (subgoal_tac "\<not> length list \<le> length list - m")
    apply simp
    apply (subgoal_tac "(bitval a * 2 ^ length list + bv_to_nat list)mod 2 ^ m = ( bv_to_nat list + (bitval a *  2 ^ (length list - m))*2 ^ m) mod 2 ^ m")
     apply (rotate_tac -1, erule ssubst)
     apply (subst mod_mult_self1)
     apply (subgoal_tac " bv_to_nat list \<ge>  bv_to_nat list mod 2 ^ m")
      apply simp
     apply (rule mod_le)
    apply (subgoal_tac "bitval a * (2::nat) ^ (length list - m) * 2 ^ m =  bitval a * 2 ^ length list")
     apply (rotate_tac -1, erule ssubst)
     apply (simp add: add.commute)
    apply (subst mult.assoc)
    apply (subst power_add[THEN sym])
    apply simp
 apply simp
done
 
lemma bv_to_nat_take_drop_append_replicate[rule_format]:
  "\<forall> k m.  length bv > k + m \<longrightarrow>
   bv_to_nat
   (take k (drop (length bv - (k + m)) bv) @ replicate m (0::bit)) =
    bv_to_nat bv mod 2 ^ (k + m) - bv_to_nat bv mod 2 ^ m"
 apply (induct_tac bv)
  apply simp
  apply (simp add: bv_to_nat_replicate_Zero)
 apply (intro allI impI)
 apply (subgoal_tac "Suc (length list) - (k + m) = Suc (length list - (k + m))")
  apply (rotate_tac -1, erule ssubst)
  apply simp
  apply (case_tac "length list = k + m")
   apply simp
   apply (subgoal_tac "take k list = take (length list - m) list")
    apply (rotate_tac -1, erule ssubst)
    apply (subst bv_to_nat_take_append_replicate)
    apply simp_all
    apply (subgoal_tac "bitval a * 2 ^ (k + m) + bv_to_nat list =
                         bv_to_nat list + bitval a * 2 ^ (k + m)")
     apply (rotate_tac -1, erule ssubst)
     apply (subgoal_tac "bv_to_nat list + bitval a * 2 ^ (k + m) = 
                         bv_to_nat list + (bitval a * 2 ^ k) * 2^m")
      apply (rotate_tac -1, erule ssubst)  
       apply (subst mod_mult_self1)
      apply (rule sym)
      apply (subst mod_less)
       apply (erule subst)
       apply (rule bv_to_nat_upper_range)
      apply simp
     apply (simp add: power_add)
    apply simp
  apply (subgoal_tac "(bitval a * 2 ^ length list + bv_to_nat list) mod 2 ^ (k + m) = 
                       (bv_to_nat list + (bitval a * 2 ^ (length list - (k + m))) * 
                        2 ^ (k + m))mod 2 ^ (k + m) ")
   apply (rotate_tac -1, erule ssubst)  
   apply (subst mod_mult_self1)
   apply (subgoal_tac "(bitval a * 2 ^ length list + bv_to_nat list) mod 2 ^ m = 
                       (bv_to_nat list + (bitval a * 2 ^ (length list - m) )* 2^m )mod 2^m")
    apply (rotate_tac -1, erule ssubst)  
    apply (subst mod_mult_self1)  
    apply simp
   apply (subst mult.assoc)
   apply (subst power_add[THEN sym])
   apply simp
   apply (simp add: add.commute)
  apply (subst mult.assoc)
  apply (subst power_add[THEN sym])
  apply (simp add: add.commute)
done

lemma nat_to_bv_length_mono [rule_format] : 
      "length (nat_to_bv n) < length (nat_to_bv m) \<longrightarrow> n < m"
apply clarify
apply (case_tac "m = 0")
 apply simp
apply (case_tac "n = 0")
 apply simp
apply (cut_tac w = "nat_to_bv n" in bv_to_nat_upper_range) 
apply (cut_tac w = "(nat_to_bv m)" in bv_to_nat_lower_limit)
  apply simp
apply (subgoal_tac " (2::nat) ^ length (nat_to_bv n) \<le> 2 ^ (length (nat_to_bv m) - Suc 0)")
  prefer 2
  apply (subgoal_tac "length (nat_to_bv n) \<le> (length (nat_to_bv m) - Suc 0)")
    prefer 2
    apply arith
  apply (cut_tac n = "length (nat_to_bv n)" and a = "2::nat" and 
                 N = "length (nat_to_bv m) - Suc 0" in power_increasing)
     apply simp
    apply simp
  apply simp
apply (simp add: nat_to_bv_of_neg_is_Nil)
apply simp
using length_nat_to_bv_lower_limit_2 
      length_nat_to_bv_lower_limit less_irrefl_nat not_less order_trans
apply (auto)
using bv_to_nat_upper_range less_le_trans 
apply fastforce 
done

subsection {* arithmetic operation with bit vector length *}

lemma mult_bv_to_nat_is_bv_to_nat_append:
      "bv_to_nat ax * 2 ^ k = bv_to_nat (ax @ replicate k (0::bit))"
apply (subst bv_to_nat_dist_append)
apply simp
apply (rule bv_to_nat_replicate_Zero)
done

lemma bv_to_nat_div_power_length:
      "(bv_to_nat bs) div 2 ^ length bs = 0"
by (insert bv_to_nat_upper_range, simp)

lemma div_power_length_nat_to_bv: 
      "b div 2 ^ length (nat_to_bv b) = 0"
  apply (insert bv_nat_bv[of b])
  using bv_to_nat_div_power_length
  apply metis
done

lemma bv_to_nat_append_div_length:
      "bv_to_nat (xa @ ya) div (2 ^ length ya) = bv_to_nat xa"
apply (subst bv_to_nat_dist_append)
apply (subst div_add1_eq)
apply simp
apply (rule div_less)
apply (rule bv_to_nat_less_power)
apply simp
done

lemma bv_to_nat_mod_power_length: 
      "(bv_to_nat bs) mod 2 ^ length bs = bv_to_nat bs"
by (insert bv_to_nat_upper_range, simp)

lemma mod_power_length_nat_to_bv: "b mod 2 ^ length (nat_to_bv b) = b"
  apply (insert bv_nat_bv[of b])
  using bv_to_nat_mod_power_length
  apply metis
done

lemma bv_to_nat_append_mod_length:
      "bv_to_nat (xa @ ya) mod (2 ^ length ya) = bv_to_nat ya"
  apply (subst bv_to_nat_dist_append)
  apply simp
  apply (rule mod_less)
  apply (rule bv_to_nat_less_power)
  apply simp
done

lemma nat_to_bv_div_power_tail:
  "nat_to_bv b = x # xs \<Longrightarrow> b div 2 ^ length xs = bv_to_nat [x]"
apply (insert bv_nat_bv[of b])
apply (rotate_tac -1, erule subst)
apply (erule ssubst)
apply (subgoal_tac "x # xs = [x] @ xs")
 apply (erule ssubst)
 apply (simp only: bv_to_nat_dist_append)
 apply (subst div_add1_eq)
 apply simp
 apply (rule bv_to_nat_div_power_length)
apply simp
done

lemma bitval_hd_eq_div:
      "length (nat_to_bv a) \<le> Suc n \<Longrightarrow>
       bitval (hd (replicate (Suc n - length (nat_to_bv a)) (0::bit) @ nat_to_bv a)) = 
       a div 2 ^ n"
apply (case_tac "length (nat_to_bv a) = Suc n")
 apply simp
 apply (case_tac "nat_to_bv a")
  apply simp
 apply (frule nat_to_bv_div_power_tail)
 apply (case_tac aa, simp_all)
apply (rule div_less)
apply (rule length_nat_to_bv_upper_limit_impl_nat_limit)
apply simp
done

lemma bv_to_nat_and_one_replicate_zero_nat_to_bv:
      "length (nat_to_bv a) \<le> Suc n \<Longrightarrow>
       bv_to_nat (map (\<lambda>(x, y). x AND y) (zip (bv_extend (length (nat_to_bv a)) 
       (0::bit) ((1::bit) # replicate n (0::bit))) (bv_extend (Suc n) (0::bit) (nat_to_bv a)))) =
       a div 2 ^ n * 2 ^ n"
apply (subst bv_to_nat_and_one_replicate_zero, assumption)
apply (drule bitval_hd_eq_div)
apply simp
done

lemma nat_to_bv_div_power_k: 
      "\<lbrakk>nat_to_bv b = xs @ ys; 0 \<le> b\<rbrakk> \<Longrightarrow> b div 2 ^ length ys = bv_to_nat xs"     
apply (insert bv_nat_bv[of b])
apply (rotate_tac -1, erule subst)
apply (erule ssubst)
 apply (simp only: bv_to_nat_dist_append)
 apply (subst div_add1_eq)
 apply simp
 apply (rule bv_to_nat_div_power_length)
done

lemma nat_to_bv_div_aux: 
     "\<lbrakk>nat_to_bv b = xs @ ys; 0 < b ;xs \<noteq> []\<rbrakk> \<Longrightarrow> (nat_to_bv (b div  2 ^ length ys)) = xs" 
apply (subgoal_tac "0\<le> b") 
apply (frule nat_to_bv_div_power_k)
apply simp
apply (frule_tac nat_to_bv_non0_impl_hd_one)
apply (case_tac "xs")
apply simp 
apply (simp_all)
using nat_helper2 
apply auto
done

lemma div_n_mod_2 [rule_format]:
      "0 < x \<longrightarrow> (x div (2^(length (nat_to_bv x) - 1))) = 1"
apply (clarsimp)
apply (case_tac "(nat_to_bv x)")
apply (simp add: nat_to_bv_non0)
apply simp 
apply (simp add: nat_to_bv_div_power_tail)
apply (frule_tac x ="a" and xs = "list" in  nat_to_bv_Cons_impl_head_is_One)
apply simp
done

lemma nat_to_bv_mod_power_tail_decompose:
  "nat_to_bv b = x # xs \<Longrightarrow> b mod 2 ^ length xs + 2 ^ length xs = b"
apply (frule nat_to_bv_Cons_impl_head_is_One)
apply (insert bv_nat_bv[of b])
apply (rotate_tac -1, erule subst)
apply (erule ssubst)
apply (erule ssubst)
apply (simp only: bv_to_nat1)
apply simp
apply (rule bv_to_nat_mod_power_length)
done

subsection {* bit vector div and mod operations for odd and even *}

subsubsection {* odd *}

lemma nat_to_bv_odd_is_pos: "nat_to_bv n = xs @ [(1::bit)] \<Longrightarrow> 0 < n"
by (cases "n = 0", simp_all add:nat_to_bv_def)

lemma nat_to_bv_odd_mod_two: 
      "nat_to_bv n = xs @ [(1::bit)] \<Longrightarrow> n mod 2 = 1"
proof -
  assume a1: "nat_to_bv n = xs @ [1]"
  then have "0 < n"
    by (metis nat_to_bv_odd_is_pos)
  then have f2: "nat_to_bv 1 = nat_to_bv (n mod 2)"
    using a1 nat_to_bv_mod_2_last nat_to_bv_one by auto
  have "nat_to_bv 0 = []"
    using less_numeral_extra(3) nat_to_bv_non_Nil
    by fast
  then show ?thesis
    using f2 nat_to_bv_is_Nil_impl_nat_is_0 parity_cases
    by (metis (full_types))
qed


lemma nat_to_bv_odd_div_mult_eq:
  "nat_to_bv n = xs @ [(1::bit)] \<Longrightarrow> 2 * (n div 2) + 1 = n"
apply (drule nat_to_bv_odd_mod_two)
apply (insert div_mult_mod_eq[of n 2])
apply simp
done

subsubsection {* even *}

lemma nat_to_bv_even_ge_two: "nat_to_bv n = xs @ [(0::bit)] \<Longrightarrow> 2 \<le> n"
apply (case_tac "n = 0")
 apply simp
apply (case_tac "n = 1")
 apply (simp_all add: nat_to_bv_Suc_0_eq_One nat_to_bv_def)
using dual_order.antisym last_snoc nat_to_bv_non_Nil not_less_eq_eq 
apply fastforce
done

lemma nat_to_bv_even_is_pos: 
      "nat_to_bv n = xs @ [(0::bit)] \<Longrightarrow> 0 < n"
apply (case_tac "n = 0")
 apply (simp_all add: nat_to_bv_def)
done

lemma nat_to_bv_even_mod_two: 
      "nat_to_bv n = xs @ [(0::bit)] \<Longrightarrow> n mod 2 = 0"
proof (frule nat_to_bv_even_is_pos)
  assume a1: "0 < n"
  assume a2: "nat_to_bv n = xs @ [0]"
  have "\<forall>x0. [if (x0::nat) mod 2 = 0 then 0::bit else 1] = (if x0 mod 2 = 0 then [0] else [1])"
    by auto
  then show ?thesis
    using a2 a1 append1_eq_conv less_not_refl2 nat_to_bv_non0 one_neq_zero
    by (metis (no_types))
qed

subsubsection {* odd \& even *}

lemma nat_to_bv_is_pos: "nat_to_bv n = xs @ [x] \<Longrightarrow> 0 < n"
apply (case_tac x)
 apply (simp add: nat_to_bv_even_is_pos)
apply (simp add: nat_to_bv_odd_is_pos)
done

lemma nat_to_bv_div_2_is_butlast:
  "nat_to_bv n = xs @ [x] \<Longrightarrow> nat_to_bv (n div 2) = xs"
  by (simp add: nat_to_bv_div_2_is_butlast2)

lemma nat_to_bv_append_div_drop: 
     "\<lbrakk>0 < n \<rbrakk> \<Longrightarrow> (nat_to_bv n) = 
                  (nat_to_bv (n div 2^k))@(drop((length (nat_to_bv n)) - k) (nat_to_bv n))"
  apply (subgoal_tac "(nat_to_bv n \<noteq> [])")
  apply (induct "k")
  apply simp
  prefer 2
  using nat_to_bv_is_Nil_impl_nat_is_0 apply auto[1]
  apply simp 
  apply (case_tac "((length (nat_to_bv n)) - (Suc k)) = 0")
  apply simp 
  apply (frule_tac n = "n " and k = "(Suc k)" in  length_nat_to_bv_upper_limit_impl_nat_limit)
  apply simp
  
  apply (erule ssubst)
  apply simp_all
  apply (simp add: nat_to_bv_of_neg_is_Nil)
  apply (subgoal_tac "0 \<le> (n div ((2::nat) ^ k))")
  prefer 2
  apply (subgoal_tac "0 \<le>n")
  apply (frule_tac m = "0" and n = "n" and k = "((2::nat) ^ k)" in div_le_mono)
  apply simp+
  apply (subgoal_tac "((2::nat) * ((2::nat) ^ k)) = (((2::nat) ^ k)* 2)")
  apply (erule ssubst)
  apply (case_tac "((0::nat) = (n div ((2::nat) ^ k)))")
  apply simp 
  apply (simp_all add: div_mult2_eq)
apply (simp add: div_eq_0_iff nat_upper_limit_impl_length_nat_to_bv_limit numeral_2_eq_2)
  apply (subgoal_tac "(nat_to_bv (n div ((2::nat) ^ k))) \<noteq>[]")
  apply (frule_tac xs = "(nat_to_bv (n div ((2::nat) ^ k)))" in drop_is_last)
  apply simp
  proof -
    fix ka :: nat
    assume a1: "nat_to_bv (n div 2 ^ ka) \<noteq> []"
    then have "nat_to_bv (n div 2 ^ ka div 2) = butlast (nat_to_bv (n div 2 ^ ka))"
      by (metis (no_types) append_butlast_last_id nat_to_bv_div_2_is_butlast)
    then have "nat_to_bv (n div 2 div 2 ^ ka) = butlast (nat_to_bv (n div 2 ^ ka))"
      by (metis (no_types) Divides.div_mult2_eq mult.commute)
    then show "nat_to_bv (n div 2 ^ ka) = 
               nat_to_bv (n div 2 div 2 ^ ka) @ [last (nat_to_bv (n div 2 ^ ka))]"
      using a1 by force
  next 
    show "\<And>k. 0 < n \<Longrightarrow>
         nat_to_bv n \<noteq> [] \<Longrightarrow>
         \<not> length (nat_to_bv n) \<le> Suc k \<Longrightarrow>
         0 < n div 2 ^ k \<Longrightarrow> nat_to_bv (n div 2 ^ k) \<noteq> []"
  using nat_to_bv_is_Nil_impl_nat_is_0 
  by fastforce
qed

subsection{* int\_to\_bv and bv\_to\_int *}


lemma norm_signed0 [simp]: 
  "norm_signed [0] = []"
  by simp

lemma norm_signed1 [simp]: 
  "norm_signed [1] = [1]"
  by simp

lemma norm_signed01 [simp]: 
  "norm_signed (0#1#xs) = 0#1#xs"
  by simp

lemma norm_signed00 [simp]:
  "norm_signed (0#0#xs) = norm_signed (0#xs)"
  by simp

lemma norm_signed10 [simp]: 
  "norm_signed (1#0#xs) = 1#0#xs"
  by simp

lemma norm_signed11 [simp]: 
  "norm_signed (1#1#xs) = norm_signed (1#xs)"
  by simp

lemmas [simp del] = norm_signed_Cons

definition
  int_to_bv :: "int => bit list" where
  "int_to_bv n = (if 0 \<le> n
                 then norm_signed (0#nat_to_bv (nat n))
                 else norm_signed (bv_not (0#nat_to_bv (nat (-n- 1)))))"

lemma int_to_bv_ge0 [simp]: 
      "0 \<le> n ==> int_to_bv n = norm_signed (0# nat_to_bv (nat n))"
  by (simp add: int_to_bv_def)

lemma int_to_bv_lt0 [simp]:
    "n < 0 ==> int_to_bv n = norm_signed (bv_not (0#nat_to_bv (nat (-n- 1))))"
  by (simp add: int_to_bv_def)

lemma norm_signed_idem [simp]: 
      "norm_signed (norm_signed w) = norm_signed w"
  using  bv_extend_def bv_via_norm_signed_decompose_sym norm_signed_Nil 
         norm_signed_bv_extend_bv_msb
  by metis

lemma norm_signed_result: 
      "norm_signed w = [] \<or> norm_signed w = 
       [1] \<or> bv_msb (norm_signed w) \<noteq> bv_msb (tl (norm_signed w))"
  apply (rule bit_list_cases [of w],simp_all add: norm_signed_Cons)
  using bv_msb_def norm_unsigned_result  norm_signed_Cons
  apply fastforce
  using bv_msb_def list.sel(1) neq_Nil_conv rem_initial_cons 
  apply metis
  done
lemma bv_to_int_Nil [simp]: "bv_to_int [] = 0"
  by (simp add: bv_to_int_def bv_msb_def)

lemma bv_to_int_Cons0 [simp]: "bv_to_int (0#bs) = int (bv_to_nat bs)"
  by (simp add: bv_to_int_def bv_msb_def)

lemma bv_to_int_Cons1 [simp]: "bv_to_int (1#bs) = - int (bv_to_nat (bv_not bs) + 1)"
  by (simp add: bv_to_int_def bv_msb_def)

lemma bv_to_int_type [simp]: "bv_to_int (norm_signed w) = bv_to_int w"
proof (rule bit_list_induct [of _ w], simp_all add: norm_signed_Cons)
  fix xs
  assume ind: "bv_to_int (norm_signed xs) = bv_to_int xs"
  show " norm_unsigned xs = [] \<longrightarrow> bv_to_nat xs = 0"
  proof (rule bit_list_cases [of xs], simp_all)
    fix ys
    assume [simp]: "xs = 0#ys"
    from ind
    show "norm_unsigned ys = [] \<longrightarrow> bv_to_nat ys = 0"
      by (simp add: norm_signed_Cons split: if_split_asm)
  qed
next
  fix xs
  assume ind: "bv_to_int (norm_signed xs) = bv_to_int xs"
  show "bv_to_nat (bv_not (rem_initial 1 xs)) =
        bv_to_nat (bv_not xs)"
  proof (rule bit_list_cases [of xs], simp_all)
    fix ys
    assume [simp]: "xs = 1#ys"
    from ind
    show "bv_to_nat (bv_not (rem_initial 1 ys)) =
          bv_to_nat (bv_not ys)"
      by (simp add: norm_signed_Cons)
  qed
qed

lemma int_bv_int [simp]: "int_to_bv (bv_to_int w) = norm_signed w"
proof (rule bit_list_cases [of w],simp add: int_to_bv_def bv_to_int_def bv_msb_def nat_to_bv_def)
  fix xs
  assume [simp]: "w = 0#xs"
  show ?thesis
    apply simp
    using norm_unsigned_result [of xs]
    apply safe
    apply (rule bit_list_cases [of "norm_unsigned xs"])
    apply (simp_all add: int_to_bv_def bv_to_int_def  bv_msb_def norm_signed_Cons)
    using bv_to_nat_type nat_bv_nat
    apply metis
    done
next
  fix xs
  assume [simp]: "w = 1#xs"
  show ?thesis
    apply (simp del: int_to_bv_lt0)
    apply (rule bit_list_induct [of _ xs])
    apply (simp add: int_to_bv_def bv_to_int_def  bv_msb_def nat_to_bv_def)
    apply (subst int_to_bv_lt0)
    apply (subgoal_tac "- int (bv_to_nat (bv_not (0 # bs))) + -1 < 0 + 0")
    apply simp
    apply (rule add_le_less_mono)
    apply linarith
    apply simp
    apply simp
    prefer 2
    apply (simp del: bv_to_nat1 bv_to_nat_helper)
    using Nat_Transfer.transfer_nat_int_functions(1) bit.simps(4) bitNOT_bit.simps(2)
           bv_not_replicate_zero length_map list.inject list.sel(3) map_append map_eq_Cons_conv
         nat_bv_nat nat_eq_iff nat_helper2 nat_int nat_pow2_eq_pow2 negative_zle_0
          norm_signed.simps(2) norm_signed_One_bv_not_nat_to_bv power_not_zero
           repl_remove zero_not_eq_two
   proof ( simp split: bit.split_asm if_split_asm)
     fix bs :: "bit list"
     assume a1: "rem_initial 1 (bv_not (norm_unsigned (bv_not bs))) = rem_initial 1 bs"
     assume a2: "\<And>x y. \<lbrakk>0 \<le> x; 0 \<le> y\<rbrakk> \<Longrightarrow> nat x + nat y = nat (x + y)"
     assume "\<And>w m. (nat w = m) = (if 0 \<le> w then w = int m else m = 0)"
     assume a3: "\<And>xs. nat_to_bv (2 ^ length xs + bv_to_nat xs) = 1 # xs"
     assume a4: "\<And>m. rem_initial 1 (bv_not (nat_to_bv m)) = bv_not (nat_to_bv m)"
     assume a5: "\<And>list l b. length list = l \<Longrightarrow> 
                 replicate (l - length (rem_initial b list)) b @ rem_initial b list = list"
     have f6: "\<forall>n na. n + na = nat (int n + int na)"
       using a2 by (metis (no_types) int_eq_iff)
     { assume "\<exists>n. (0::nat) \<noteq> n"
       then have "(\<exists>n. 0 # bs = bv_not (nat_to_bv (Suc 1 ^ length bs + bv_to_nat (bv_not bs))) \<and> 
                   (0::nat) \<noteq> n) \<or> (\<exists>f bs. 1 # map f (bs::bit list) \<noteq> 
                  nat_to_bv (Suc 1 ^ length bs + bv_to_nat (map f bs)))"
         using a5 a4 a1 
         by (metis (no_types) bitNOT_bit.simps(2) bv_not_replicate_zero length_map list.simps(9) 
                             map_append nat_bv_nat)
       moreover
       { assume "\<exists>f bs. 1 # map f (bs::bit list) \<noteq> 
                        nat_to_bv (Suc 1 ^ length bs + bv_to_nat (map f bs))"
         then have "Suc 1 \<noteq> 2"
           using a3 by (metis (no_types) length_map)
         then have "bv_not (nat_to_bv (nat (2 ^ length bs + int (bv_to_nat (bv_not bs))))) = 
                    0 # bs"
           by linarith }
       ultimately have "bv_not (nat_to_bv (nat (2 ^ length bs + int (bv_to_nat (bv_not bs))))) = 
                        0 # bs"
         using f6 by fastforce }
     then show "bv_not (nat_to_bv (nat (2 ^ length bs + int (bv_to_nat (bv_not bs))))) = 0 # bs"
       by blast
   qed
qed

lemma bv_int_bv [simp]: "bv_to_int (int_to_bv i) = i"
  apply (cases "0 \<le> i" , simp_all)
  using bv_nat_bv complement_bv_eq int_eq_iff length_map list.map_comp
  apply (smt )
done  

lemma bv_msb_norm [simp]: "bv_msb (norm_signed w) = bv_msb w"
  by (rule bit_list_cases [of w]) (simp_all add: norm_signed_Cons bv_msb_def)

lemma bv_to_int_msb1: "bv_to_int w1 < 0 ==> bv_msb w1 = 1"
  by (rule bit_list_cases,simp_all add: bv_msb_def bv_to_int_def)
lemma int_to_bv_returntype [simp]: "norm_signed (int_to_bv w) = int_to_bv w"
proof -
  have "\<forall>bs. norm_signed bs = norm_signed (norm_signed bs) \<or> [] = norm_signed bs"
    by (metis (no_types) bv_via_norm_signed_decompose_sym norm_signed_replicate_bv_msb)
  then show ?thesis
    by (metis int_to_bv_def norm_signed_Nil)
qed


lemma bv_to_int_upper_limit_lem1:
  assumes w0: "bv_to_int w < -1"
  shows       "bv_to_int w < - (2 ^ (length (norm_signed w) - 2))"
proof -
  from w0
  have "bv_to_int w < 0" by simp
  hence msbw [simp]: "bv_msb w = 1"
    by (rule bv_to_int_msb1)
  have "bv_to_int w = bv_to_int (norm_signed w)" by (simp)
  also from norm_signed_result [of w]
  have "... < - (2 ^ (length (norm_signed w) - 2))"
  proof safe
    assume "norm_signed w = []"
    hence "bv_to_int (norm_signed w) = 0" by simp
    with w0 show ?thesis by simp
  next
    assume "norm_signed w = [1]"
    hence "bv_to_int (norm_signed w) = -1" by simp
    with w0 show ?thesis by simp
  next
    assume "bv_msb (norm_signed w) \<noteq> bv_msb (tl (norm_signed w))"
    hence msb_tl: "1 \<noteq> bv_msb (tl (norm_signed w))" by simp
    show "bv_to_int (norm_signed w) < - (2 ^ (length (norm_signed w) - 2))"
    proof (rule bit_list_cases [of "norm_signed w"])
      assume "norm_signed w = []"
      hence "bv_to_int (norm_signed w) = 0" by simp
      with w0 show ?thesis by simp
    next
      fix w'
      assume nw: "norm_signed w =0 # w'"
      from msbw have "bv_msb (norm_signed w) = 1" by simp
      with nw show ?thesis by (simp add: bv_msb_def)
    next
      fix w'
      assume weq: "norm_signed w = 1 # w'"
      show ?thesis
      proof (rule bit_list_cases [of w'])
        assume w'eq: "w' = []"
        from w0 have "bv_to_int (norm_signed w) < -1" by simp
        with w'eq and weq show ?thesis by simp
      next
        fix w''
        assume w'eq: "w' = 0 # w''"
        show ?thesis
          by (simp add: weq w'eq)
      next
        fix w''
        assume w'eq: "w' = 1 # w''"
        with weq and msb_tl show ?thesis by (simp add: bv_msb_def)
      qed
    qed
  qed
  finally show ?thesis .
qed

lemma length_int_to_bv_upper_limit_lem1:
  assumes w1: "i < -1"
  and     wk: "- (2 ^ (k - 1)) \<le> i"
  shows       "length (int_to_bv i) \<le> k"
proof (rule ccontr)
  from w1 wk
  have k1: "1 < k" by (cases "k - 1") simp_all
  assume "~ length (int_to_bv i) \<le> k"
  hence "k < length (int_to_bv i)" by simp
  hence "k \<le> length (int_to_bv i) - 1" by arith
  hence a: "k - 1 \<le> length (int_to_bv i) - 2" by arith
  have "i < - (2 ^ (length (int_to_bv i) - 2))"
  proof -
    have "i = bv_to_int (int_to_bv i)"
      by simp
    also have "... < - (2 ^ (length (norm_signed (int_to_bv i)) - 2))"
      by (rule bv_to_int_upper_limit_lem1,simp,rule w1)
    finally show ?thesis by simp
  qed
  also have "... \<le> -(2 ^ (k - 1))"
  proof -
    have "(2::int) ^ (k - 1) \<le> 2 ^ (length (int_to_bv i) - 2)" using a by simp
    thus ?thesis by simp
  qed
  finally have "i < -(2 ^ (k - 1))" .
  with wk show False by simp
qed

lemma bv_to_int_msb0: "0 \<le> bv_to_int w1 ==> bv_msb w1 = 0"
  by (rule bit_list_cases,simp_all add: bv_msb_def)

lemma int_nat_two_exp: "2 ^ k = int (2 ^ k)"
  by simp

lemma bv_to_int_lower_limit_gt0:
  assumes w0: "0 < bv_to_int w"
  shows       "2 ^ (length (norm_signed w) - 2) \<le> bv_to_int w"
proof -
  from w0
  have "0 \<le> bv_to_int w" by simp
  hence [simp]: "bv_msb w = 0" by (rule bv_to_int_msb0)
  have "2 ^ (length (norm_signed w) - 2) \<le> bv_to_int (norm_signed w)"
  proof (rule bit_list_cases [of w])
    assume "w = []"
    with w0 show ?thesis by simp
  next
    fix w'
    assume weq: "w = 0 # w'"
    thus ?thesis
    proof (simp add: norm_signed_Cons,safe)
      assume "norm_unsigned w' = []"
      with weq and w0 show False
        by (simp add: norm_empty_bv_to_nat_zero)
    next
      assume w'0: "norm_unsigned w' \<noteq> []"
      have "0 < bv_to_nat w'"
      proof (rule ccontr)
        assume "~ (0 < bv_to_nat w')"
        hence "bv_to_nat w' = 0"
          by arith
        hence "norm_unsigned w' = []"
          by (simp add: bv_to_nat_zero_imp_empty)
        with w'0
        show False by simp
      qed
      with bv_to_nat_lower_limit [of w']
      show "2 ^ (length (norm_unsigned w') - Suc 0) \<le> int (bv_to_nat w')"
        apply (simp only: int_nat_two_exp )
        using One_nat_def 
        apply presburger
        done
    qed
  next
    fix w'
    assume weq: "w = 1 # w'"
    from w0 have "bv_msb w =0" by simp
    with weq show ?thesis by (simp add: bv_msb_def)
  qed
  also have "...  = bv_to_int w" by simp
  finally show ?thesis .
qed


lemma length_int_to_bv_upper_limit_gt0:
  assumes w0: "0 < i"
  and     wk: "i \<le> 2 ^ (k - 1) - 1"
  shows       "length (int_to_bv i) \<le> k"
proof (rule ccontr)
  from w0 wk
  have k1: "1 < k"
    by (cases "k - 1",simp_all)
  assume "~ length (int_to_bv i) \<le> k"
  hence "k < length (int_to_bv i)" by simp
  hence "k \<le> length (int_to_bv i) - 1" by arith
  hence a: "k - 1 \<le> length (int_to_bv i) - 2" by arith
  hence "(2::int) ^ (k - 1) \<le> 2 ^ (length (int_to_bv i) - 2)" by simp
  also have "... \<le> i"
  proof -
    have "2 ^ (length (norm_signed (int_to_bv i)) - 2) \<le> bv_to_int (int_to_bv i)"
    proof (rule bv_to_int_lower_limit_gt0)
      from w0 show "0 < bv_to_int (int_to_bv i)" by simp
    qed
    thus ?thesis by simp
  qed
  finally have "2 ^ (k - 1) \<le> i" .
  with wk show False by simp
qed

lemma length_bounded_int_to_bv:
  assumes lb: "lb = - ub"
  assumes ub: "ub = 2^(w - 1)"
  assumes w: "0 < w"
  assumes i_bounded: "lb \<le> i" "i < ub"
  shows "length (int_to_bv i) \<le> w"
using lb ub w i_bounded
apply (cases "i=0")
apply (simp add: nat_to_bv_def)
apply (cases "0 < i")
apply  (rule length_int_to_bv_upper_limit_gt0)
apply   assumption
apply  simp
apply (cases "i=-1")
apply (simp add: nat_to_bv_def)
apply (cases "i < -1")
apply  (rule length_int_to_bv_upper_limit_lem1)
apply   assumption
apply  simp
apply simp
done

lemma int_to_bv_are_not_eq: 
      "i1 \<noteq> i2 \<Longrightarrow> int_to_bv i1 \<noteq> int_to_bv i2"
apply (insert bv_int_bv[of i1])
apply (insert bv_int_bv[of i2])
apply force
done

lemma norm_unsigned_int_to_bv_neg:
  "x < 0 \<Longrightarrow> norm_unsigned (int_to_bv x) = int_to_bv x"
  by (simp add: norm_signed_Cons)

lemma int_to_bv_is_not_Zero: "int_to_bv i \<noteq> [(0::bit)]"
apply (case_tac "0 \<le> i")
 apply simp
 apply (case_tac "nat_to_bv (nat i)")
  apply simp
 apply (frule nat_to_bv_Cons_impl_head_is_One)
 apply simp
apply simp
apply (case_tac "nat_to_bv (nat (- i - 1))")
 apply simp
apply (frule nat_to_bv_Cons_impl_head_is_One)
apply simp
done

lemma bv_extend_norm_unsigned_neg: "p < 0 \<Longrightarrow>     
      bv_extend i (bv_msb (norm_unsigned (int_to_bv p))) (norm_unsigned (int_to_bv  p))
      = bv_extend i (bv_msb (int_to_bv p)) (int_to_bv p)"
  by (simp only: norm_unsigned_int_to_bv_neg)

lemma bv_to_int_replicate_Zero: "bv_to_int (replicate n (0::bit)) = 0"
  apply (induct n)
  apply (simp_all add: bv_to_nat_replicate_Zero)
done
lemma bv_to_int_replicate_One:
          "0 < n \<Longrightarrow> bv_to_int (replicate n (1::bit)) = -1"
  by (case_tac n, simp+, simp add:  bv_to_nat_replicate_Zero)

lemma bv_to_int_zero_zero [rule_format] : 
     "bv_to_int l = 0 \<longrightarrow> l = replicate (length l) (0::bit)"
proof (clarify ,insert bv_to_int_replicate_Zero[of "length l"])
  assume a1: "bv_to_int l = 0"
  then have "0 = bv_msb l"
    by (metis bv_to_int_msb0 less_eq_int_code(1))
  then show "l = replicate (length l) 0"
    using a1 by (simp add: bv_to_int_def bv_to_nat_is_zero_impl_replicate_zeros)
qed


lemma bv_to_int_is_zero_impl_replicate_zeros[rule_format]: 
      "bv_to_int wx = 0 \<longrightarrow> wx = replicate (length wx) (0::bit)" 
  by (simp add: bv_to_int_zero_zero)

lemma norm_unsigned_equal_int_to_bv_neg [rule_format]: 
      "norm_unsigned (int_to_bv x) = int_to_bv x \<longrightarrow> x \<noteq> 0 \<longrightarrow> x < 0"
apply clarify
apply (case_tac "x \<ge> 0")
  apply (frule int_to_bv_ge0)
  apply (case_tac "nat_to_bv (nat x)")
    apply (frule nat_to_bv_is_Nil_impl_nat_is_0)
    apply clarsimp
  apply (frule_tac b = "nat x" in nat_to_bv_Cons_impl_head_is_One)
  apply simp
apply simp
done

lemma norm_unsigned_not_equal [rule_format] : 
      "norm_unsigned w \<noteq> w \<longrightarrow> bv_msb w = (0::bit)"
  apply clarify
  apply (frule rem_initial_bv_msb)
  apply simp
done

lemma bv_msb_extend_same [simp]: 
      "bv_msb w = b ==> bv_msb (bv_extend n b w) = b"
  apply (simp add: bv_extend_def bv_msb_def split: if_split_asm)
  apply (cases "n - length w")
   apply simp_all
  done

lemma norm_unsigned_extend_not_equal [rule_format] : 
      "(norm_unsigned (bv_extend n (bv_msb w) w)) \<noteq> 
       (bv_extend n (bv_msb w) w) \<longrightarrow> w \<noteq> [] \<longrightarrow> norm_unsigned w \<noteq> w"
apply (clarify)
apply (drule norm_unsigned_not_equal)
apply (cut_tac b = "(bv_msb w)" in bv_msb_extend_same)
  apply simp
apply simp
apply (simp add: bv_msb_def)
apply (case_tac w)
 apply simp
apply simp
apply (cut_tac b = "(0::bit)" and w = "list" in rem_initial_length)
apply simp
done

lemma length_norm_unsigned_int_to_bv_same [rule_format] : 
      "length (norm_unsigned (int_to_bv x)) = length (int_to_bv x) \<longrightarrow> x \<le> 0"
apply (rule impI)
apply (drule norm_unsigned_equal)
apply (case_tac "x = 0")
  apply simp
apply (frule norm_unsigned_equal_int_to_bv_neg)
  apply assumption
apply simp
done

lemma fist_bits_of_int_to_bv_are_not_eq:
      "int_to_bv i = a # b # cs \<Longrightarrow> a \<noteq> b"
apply (case_tac "0 \<le> i")
 apply simp
 apply (case_tac "nat_to_bv (nat i)")
  apply simp
 apply (frule nat_to_bv_Cons_impl_head_is_One)
 apply simp
apply simp
apply (case_tac "nat_to_bv (nat (- i - 1))")
 apply simp
apply (frule nat_to_bv_Cons_impl_head_is_One)
apply simp
done

lemma norm_unsigned_cons [rule_format] : 
      "norm_unsigned l = x # xs \<longrightarrow> x = (1::bit)"
  apply clarify
  apply (frule rem_initial_cons)
  apply (case_tac x)
  apply simp+
done

lemma bv_to_nat_replicate_One_append[rule_format]:
      "bv_to_nat ((replicate n (1::bit) ) @ xs) =
       (2^(n + (length xs))) - 2^(length xs) + (bv_to_nat xs)"
  apply (simp add: bv_to_nat_dist_append)
  apply (simp add: bv_to_nat_replicate_One)
  apply (simp add: power_add)
  apply (simp add: diff_mult_distrib)
done

lemma bv_to_int_replicate_Zero_append_One:
  "0 < n \<Longrightarrow>  bv_to_int (replicate n (0::bit) @ [ (1::bit)]) = 1"
  apply (simp add: bv_to_int_def bv_msb_def head_is_0th nth_append)
  apply (simp add: bv_to_nat_dist_append bv_to_nat_replicate_Zero)
done

lemma bv_to_in_replicate_Zero_append_OneI:
  "\<lbrakk> bv = replicate n (0::bit) @ [ (1::bit)] ; 0 < n \<rbrakk> \<Longrightarrow>  bv_to_int bv = 1"
  by (simp add: bv_to_int_replicate_Zero_append_One)

lemma int_to_bv_not_zero_is_not_empty: " k \<noteq> 0 \<Longrightarrow> int_to_bv k \<noteq> []"
proof (subgoal_tac "length (int_to_bv k) \<noteq> 0", fast)
  assume "k \<noteq> 0"
  then have "k \<noteq> 0"
    by metis
  then show "length (int_to_bv k) \<noteq> 0"
    by (metis (full_types) bv_int_bv bv_to_int_Nil list_exhaust_size_eq0)
qed

lemma bv_to_int_replicate_Zero_append_bv_to_nat_eq:
  "0 < i \<Longrightarrow> bv_to_int (replicate i (0::bit) @ w) = int (bv_to_nat w)"
  by (case_tac i, simp+, simp add: bv_to_nat_replicate_Zero_append)

lemmas zmult_int = 
      of_nat_mult [where 'a=int, symmetric]
lemma int_power:
      "int (m ^ n) = int m ^ n"
using Power.semiring_1_class.of_nat_power
by simp

lemmas zdiff_zmult_distrib = left_diff_distrib [of "z1::int" "z2" "w"]
lemma bv_to_int_append:
  "as \<noteq> [] \<Longrightarrow> bv_to_int (as @ bs)
              = bv_to_int as * 2 ^ length bs + int (bv_to_nat bs)"
apply (case_tac as, simp_all)
apply (simp add: bv_to_int_def bv_msb_def split: bit.split)
apply (case_tac a)
 apply clarsimp
 apply (subst bv_to_nat_dist_append)
 apply simp
 apply (subgoal_tac "2 ^ length bs = int (2 ^ length bs)")
  apply (cases bs)
  apply (simp add: zmult_int bv_to_nat_def)
  apply (simp add: zmult_int )
prefer 2
apply clarsimp
apply (rename_tac l)
apply (subst complement_bv_eq)
apply(subgoal_tac "bv_not list @ bitnot aa # bv_not l = bv_not(list @ [aa] @ l)")
apply(simp only:)
apply (subst complement_bv_eq)
apply clarsimp
apply (simp add: zdiff_zmult_distrib power_add)
apply (simp add: bv_to_nat_dist_append)
apply (simp add: left_diff_distrib)
apply simp
done

lemma bv_to_int_Cons_bv_msb: 
      "bv_to_int (bv_msb v # v) = bv_to_int v"
  by (simp add: bv_to_int_def bv_msb_def split: bit.split)

lemma int_to_bv_power2[rule_format]: 
      "int_to_bv (2^n) = (0::bit) # (1::bit) # replicate n (0::bit)"
apply (simp add: int_to_bv_def)
apply (subgoal_tac "(0::int) \<le> 2^n")
 apply clarsimp
 apply (subgoal_tac "nat (2^n) = 2^n")
  apply simp
  apply (subst nat_to_bv_power2)
  apply clarsimp
 apply (simp_all add: nat_power_eq)
done

lemma int_to_bv_power2_minus1: 
      "0 < n \<longrightarrow> int_to_bv (2^n - 1) = (0::bit) # replicate n (1::bit)"
apply (simp add: int_to_bv_def)
apply (subgoal_tac "(0::int) \<le> 2^n")
 apply clarsimp
 apply (subgoal_tac "nat (2^n - 1) = 2^n - Suc 0")
  apply simp
  apply (subst nat_to_bv_power2_minus1)
  apply (case_tac n, simp)
  apply simp
 apply (subst nat_diff_distrib, simp, simp)
 apply simp
 apply (simp_all add: nat_power_eq)
done

lemma int_to_bv_power2_neg: 
      "int_to_bv (-(2^n)) = (1::bit) # replicate n (0::bit)"
apply (subst int_to_bv_lt0)
 apply simp
 apply simp
apply (subgoal_tac "nat (2 ^ n - 1) = 2 ^ n - 1")
 apply clarsimp
 apply (subst nat_to_bv_power2_minus1)
 apply (case_tac n, simp)
 apply simp
apply clarsimp
apply (simp add: nat_diff_distrib)
apply (simp add: nat_power_eq)
done

lemma int_to_bv_mult_power:
      "m \<noteq> 0 \<Longrightarrow> int_to_bv (m * 2 ^ k) = int_to_bv m @ replicate k (0::bit)"
apply (simp add: int_to_bv_def)
apply (intro conjI impI)
   apply (subst norm_signed_Zero_nat_to_bv)
    apply simp
   apply (subst norm_signed_Zero_nat_to_bv)
    apply simp
   apply (subst nat_mult_distrib, assumption)
   apply (subst nat_power_eq, simp)
   apply simp
   apply (rule nat_to_bv_mult_power)
   apply simp
  apply (rotate_tac -1)
  apply (erule notE)
  apply simp
 apply (subgoal_tac "m * 2 ^ k < 0")
  apply simp
 apply (rule i_mult_neg_pos_is_neg)
  apply simp
 apply (rule zero_less_power)
 apply simp
apply (subst norm_signed_One_bv_not_nat_to_bv)
apply (subst norm_signed_One_bv_not_nat_to_bv)
apply simp
apply (subst nat_to_bv_mult_power_minus)
 apply simp
apply (subst bv_not_append)
apply (subst bv_not_replicate_one)
apply simp
done

lemma bv_to_int_qinj:
  assumes one: "bv_to_int xs = bv_to_int ys"
  and     len: "length xs = length ys"
  shows        "xs = ys"
proof -
  from one
  have "int_to_bv (bv_to_int xs) = int_to_bv (bv_to_int ys)" by simp
  hence xsys: "norm_signed xs = norm_signed ys" by simp
  hence xsys': "bv_msb xs = bv_msb ys"
  proof -
    have "bv_msb xs = bv_msb (norm_signed xs)" by simp
    also have "... = bv_msb (norm_signed ys)" by (simp add: xsys)
    also have "... = bv_msb ys" by simp
    finally show ?thesis .
  qed
  have "xs = bv_extend (length xs) (bv_msb xs) (norm_signed xs)"
    proof -
      { assume "norm_signed xs = []"
        { assume "bv_msb xs \<noteq> 0"
          then have "norm_signed xs \<noteq> []"
            by (metis bv_msb_def bv_msb_norm) }
        then have "norm_signed xs = [] \<longrightarrow> 
                   replicate (length xs - length (norm_signed xs)) 
                             (bv_msb xs) @ norm_signed xs = xs"
          using nat_to_bv_non_Nil norm_signed_is_empty_impl_replicate_Zero by fastforce }
      then show ?thesis
        using bv_extend_def bv_msb_norm bv_via_norm_signed_decompose_sym
        by fastforce
    qed
  also have "... = bv_extend (length ys) (bv_msb ys) (norm_signed ys)"
    by (simp add: xsys xsys' len)
  also have "... = ys"
       proof -
         have f1: "\<forall>bs. norm_signed bs \<noteq> [] \<or> bs = replicate (length bs) 0"
           by (metis norm_signed_is_empty_impl_replicate_Zero)
         { assume "bv_extend (length ys) (bv_msb ys) (norm_signed ys) \<noteq> ys"
           then have "norm_unsigned ys \<noteq> norm_signed ys \<or> 0 \<noteq> bv_msb ys"
             by (metis (no_types) bv_extend_norm_unsigned)
           then have ?thesis
             using f1 bv_extend_def bv_msb_def bv_msb_norm bv_via_norm_signed_decompose_sym 
                   remove_replicate_b_empty
             by (metis (no_types)) }
         then show ?thesis
           by metis
       qed
  finally show ?thesis .
qed
lemma bv_to_int_append_equality : 
    "\<lbrakk>bv_to_int ( xs @ ys) = a ; bv_to_int ( xs @ zs) = a ; length ys = length zs\<rbrakk> \<Longrightarrow> 
     ys = zs"
  apply (subgoal_tac "bv_to_int ( xs @ ys) = bv_to_int ( xs @ zs) ")
  apply (drule bv_to_int_qinj)
  apply simp_all
done

lemma norm_unsigned_int_to_bv_length_mono [rule_format] : 
     "a > 0 \<longrightarrow> b > 0 \<longrightarrow> length (norm_unsigned (int_to_bv a)) < 
                          length (norm_unsigned (int_to_bv b)) \<longrightarrow> a < b"
apply clarify
apply simp
apply (cut_tac a = "nat a" in nat_to_bv_pos_not_nil)
 apply arith
apply (cut_tac a = "nat b" in nat_to_bv_pos_not_nil)
 apply arith
apply clarsimp
apply (case_tac "length (nat_to_bv (nat b)) > length (nat_to_bv (nat a))")
 apply (frule nat_to_bv_length_mono)
 apply simp
apply simp
done

subsection {* int and nat together *}

lemma bv_to_nat_int_to_bv_pos: 
      "0 \<le> val \<Longrightarrow> bv_to_nat (int_to_bv val) = nat val"
  apply simp
  apply (simp add: norm_signed_Cons)
  apply (rule impI)
  using nat_to_bv_is_Nil_impl_nat_is_0 
  apply force
done

lemma bv_to_int_upper_range: "bv_to_int w < 2 ^ (length w - 1)"
proof (rule bit_list_cases [of w],simp_all)
  fix bs
  from bv_to_nat_upper_range
  show "int (bv_to_nat bs) < 2 ^ length bs"
       proof -
         show ?thesis
           using bv_to_nat_upper_range of_nat_less_iff of_nat_numeral of_nat_power
           by (metis (no_types) )
       qed
next
  fix bs
  have "-1 - int (bv_to_nat (bv_not bs)) \<le> 0" by simp
  also have "... < 2 ^ length bs" by (induct bs) simp_all
  finally show "-1 - int (bv_to_nat (bv_not bs)) < 2 ^ length bs" .
qed

lemma bv_to_int_lower_range: "- (2 ^ (length w - 1)) \<le> bv_to_int w"
proof (rule bit_list_cases [of w],simp_all)
  fix bs :: "bit list"
  have "- (2 ^ length bs) \<le> (0::int)" by (induct bs) simp_all
  also have "... \<le> int (bv_to_nat bs)" by simp
  finally show "- (2 ^ length bs) \<le> int (bv_to_nat bs)" .
next
  fix bs
  from bv_to_nat_upper_range [of "bv_not bs"]
  show "- (2 ^ length bs) \<le> -1 - int (bv_to_nat (bv_not bs))"
  using complement_bv_eq by auto 
qed

lemma int_to_bv_range[rule_format]: 
     "0 < bw \<longrightarrow> length (int_to_bv i) \<le> bw \<longrightarrow> -(2^(bw - Suc 0)) \<le> i \<and> i < 2^(bw - Suc 0)"
apply clarsimp
apply (insert bv_to_int_upper_range[where w="int_to_bv i"])
apply (insert bv_to_int_lower_range[where w="int_to_bv i"])
apply simp
apply (rule conjI)
 apply (insert i_le_trans[where i="- (2 ^ (bw - Suc 0))" and 
                                j="- (2 ^ (length (int_to_bv i) - Suc 0))" and k="i"])
 apply simp
 apply (subgoal_tac "length (int_to_bv i) - Suc 0 \<le> bw - Suc 0")
  apply simp
apply (insert i_less_le_trans[where i="i" and j="2 ^ (length (int_to_bv i) - Suc 0)" and 
                                    k="2 ^ (bw - Suc 0)"])
apply simp
apply (subgoal_tac "length (int_to_bv i) - Suc 0 \<le> bw - Suc 0")
 apply simp
apply arith
done

lemma int_to_bv_g_0[rule_format]: 
      "0 < n \<longrightarrow> int_to_bv n = ((0::bit)#nat_to_bv (nat n))"
apply clarsimp
apply (case_tac "nat_to_bv (nat n)")
 apply (frule nat_to_bv_is_Nil_impl_nat_is_0)
 apply simp
apply (frule nat_to_bv_Cons_impl_head_is_One) 
apply simp
done

lemma int_to_bv_l_0[rule_format]:
      "n < 0 \<longrightarrow> int_to_bv n = (bv_not ((0::bit)#nat_to_bv (nat (-n- 1))))"
  apply clarsimp
  apply (case_tac "nat_to_bv (nat (-n- 1))")
   apply (frule nat_to_bv_is_Nil_impl_nat_is_0)
   apply simp
  apply simp
  apply (frule nat_to_bv_Cons_impl_head_is_One) 
  apply simp
done

lemma int_to_bv_e_0[rule_format]:
      "n = 0 \<longrightarrow> int_to_bv n = []"
  by(simp add:nat_to_bv_def)

lemma bv_to_int_bv_to_nat_eq_one[rule_format]:
      " length ((1::bit) # bv) = l \<longrightarrow> (bv_to_int ((1::bit) # bv)) + 2 ^ l = 
        int (bv_to_nat ((1::bit) # bv))"
  using bv_msb_def complement_bv_eq 
  by auto


(*norm_unsigned_lemma but uses int_to_bv_l_0*)
lemma length_norm_unsigned_int_to_bv_less [rule_format] : 
     "length (norm_unsigned (int_to_bv x)) < length (int_to_bv x) \<longrightarrow> x > 0 "
apply (rule impI)
apply (cut_tac w = "int_to_bv x" in norm_unsigned_not_equal)
  apply clarsimp
apply (case_tac "x < 0")
  apply (frule int_to_bv_l_0)
  apply simp
apply simp
apply (case_tac "x = 0")
  apply (simp add:nat_to_bv_def)
apply simp
done

lemma bv_to_nat_extend_int_to_bv_neg:
  "\<lbrakk>x<0; (length (int_to_bv x)) \<le> w \<rbrakk> \<Longrightarrow> 
    int (bv_to_nat (bv_extend w (1::bit)  (int_to_bv x))) =  (2^w +  x)"
 apply (simp only: int_to_bv_l_0)
   apply simp
   apply (induct x)
   apply  simp
   apply simp
   apply (simp add: bv_extend_def)
   apply (simp add: bv_to_nat_dist_append)
   apply (simp add: bv_to_nat_replicate_One)
   apply (cases w)
   apply simp
   apply (simp add: diff_mult_distrib)
   apply (subgoal_tac "(((2::nat) ^ (w - (Suc (length (nat_to_bv n))))) *
             ((2::nat) * ((2::nat) ^ (length (nat_to_bv n))))) = 2^w")
   prefer 2
   apply (subgoal_tac "((2::nat) ^ ((w - (Suc (length (nat_to_bv n)))) +
                       (Suc (length (nat_to_bv n))))) =
                       ((2::nat) ^ (w - (Suc (length (nat_to_bv n))))) *
                       ((2::nat) ^ (Suc (length (nat_to_bv n))))  ")
   prefer 2
   apply (rule_tac a = "2" and m = "(w - (Suc (length (nat_to_bv n))))" and 
                   n ="(Suc (length (nat_to_bv n)))" in power_add)
   apply simp 
   apply (subgoal_tac "(bv_to_nat (bv_not (0 # (nat_to_bv n)))) = 
                       ((((2::nat) ^ (length (0# (nat_to_bv n)))) - 
                          (bv_to_nat (0 # (nat_to_bv n)))) -  (1::nat))")
   prefer 2
   apply (subgoal_tac "bv_to_nat (0#(nat_to_bv n)) = 
                       2 ^ (length (0#(nat_to_bv n))) - bv_to_nat (bv_not (0#(nat_to_bv n))) - 1")
   prefer 2
   apply (rule_tac xs ="(0#(nat_to_bv n))" in bv_to_nat_as_complement)
   apply (erule ssubst)+
   apply (subgoal_tac "(bv_to_nat (bv_not (0 # (nat_to_bv n)))) < 
                       ((2::nat) ^ (length (0 # (nat_to_bv n))))")
   apply (subgoal_tac "(bv_to_nat (0# (nat_to_bv n))) < ((2::nat) ^ (length (0# (nat_to_bv n))))")
   apply arith
   apply (simp only: bv_to_nat_upper_range)
   apply (subgoal_tac "((2::nat) ^ (length (0 # (nat_to_bv n)))) = 
                       ((2::nat) ^ (length (bv_not (0 # (nat_to_bv n)))))")
   apply (simp only:  bv_to_nat_upper_range)
   apply simp 
   apply (subgoal_tac "(bv_to_nat (1 # (bv_not (nat_to_bv n)))) =
                        ((((2::nat) ^ (length (0# (nat_to_bv n)))) - 
                           (bv_to_nat (0 # (nat_to_bv n)))) - (1::nat)) ")
  apply (erule ssubst)+
(* ================== rev. 12634 ======================
   apply (simp)
   apply (subgoal_tac "(int (((2::nat) ^ w) - ((2::nat) * ((2::nat) ^ (length (nat_to_bv n)))))) =
                       ((int ((2::nat) ^ w)) - (int ((2::nat) * ((2::nat) ^ (length (nat_to_bv n)))))) ")
   prefer 2
   apply (frule_tac n = "(Suc (length (nat_to_bv n)))" and N = "w" and a = "(2::nat)"in power_increasing)
   apply simp 
   apply simp 
   apply (frule_tac m = "((2::nat) ^ w)" and 
                    n = "((2::nat) * ((2::nat) ^ (length (nat_to_bv n))))" in of_nat_diff)
   apply simp 
   apply simp
     apply (simp add: int_mult int_power)
     apply (subgoal_tac "(int (((2::nat) * ((2::nat) ^ (length (nat_to_bv n)))) - (Suc n))) =
                         ((int ((2::nat) * ((2::nat) ^ (length (nat_to_bv n)))) - (int (Suc n)))) ")
       prefer 2
       apply (subgoal_tac "(Suc n) \<le> ((2::nat) * ((2::nat) ^ (length (nat_to_bv n)))) ")
apply (frule_tac m = "((2::nat) * ((2::nat) ^ (length (nat_to_bv n))))" and 
                 n = "(Suc n)" in of_nat_diff)
   apply simp 
   apply (subgoal_tac "(length (nat_to_bv n)) \<le> (length (nat_to_bv n))")
   apply (frule_tac n = "n" and k = "(length (nat_to_bv n))"  in 
                   length_nat_to_bv_upper_limit_impl_nat_limit)
   apply arith
   apply simp 
   apply simp 
      apply (simp add: int_mult int_power)
      apply simp
   ================== rev. 12634 ====================== *)
sorry

declare int_to_bv_lt0 [simp del]

lemma bv_to_int_neg_eq_two_complement [rule_format]:
      "x<0 \<longrightarrow> xs \<noteq>[] \<longrightarrow>x = bv_to_int xs \<longrightarrow> int (bv_to_nat xs) = (2^(length xs) + x)"
  apply clarsimp
  apply (subgoal_tac "(bv_msb xs) = (1::bit)")
  apply (simp add: bv_to_int_def)
  apply (subgoal_tac "bv_to_nat xs = 2 ^ (length xs) - bv_to_nat (bv_not xs) - 1")
  prefer 2
  apply (rule  bv_to_nat_as_complement)
  apply simp
  apply (subgoal_tac "(int (((2::nat) ^ (length xs)) - (Suc (bv_to_nat (bv_not xs))))) = 
                      ((int ((2::nat) ^ (length xs))) - (int (Suc (bv_to_nat (bv_not xs)))))") 
  apply (simp add:int_power)
  apply (subgoal_tac "(Suc (bv_to_nat (bv_not xs))) \<le> ((2::nat) ^ (length xs))")
  apply (frule_tac m = "((2::nat) ^ (length xs))" and 
                   n = "(Suc (bv_to_nat (bv_not xs)))" in of_nat_diff)
  apply simp
  apply (subgoal_tac "length xs = length (bv_not xs)")
  apply (erule ssubst)+
  apply (insert bv_to_nat_upper_range [of "(bv_not xs)" ])
  apply arith
  apply simp 
  apply (simp add: bv_to_int_msb1)
done

subsection {* Wrap-around modulo integer arithmetic *}

definition
  modwrap :: "[int, int] \<Rightarrow> int"  (infixl "modwrap" 70)
where
  modwrap_def: "a modwrap b == ((a + b) mod (2*b)) - b"

lemma modwrap_id_bounded: "\<lbrakk> -b \<le> a; a < b \<rbrakk> \<Longrightarrow> a modwrap b = a"
by (simp add: modwrap_def mod_pos_pos_trivial)

-- "sanity check"
lemma "int_to_bv ( (bv_to_int bv) modwrap (2^(length bv - 1))) = norm_signed bv"
  apply (simp only: modwrap_id_bounded [OF bv_to_int_lower_range bv_to_int_upper_range])
  apply simp
done

lemma modwrap_upper_bound: "0 < b \<Longrightarrow> a modwrap b < b"
by (simp add: modwrap_def mod_pos_pos_trivial)

lemma modwrap_lower_bound: "0 < b \<Longrightarrow> -b \<le> a modwrap b"
by (simp add: modwrap_def mod_pos_pos_trivial)

lemma mod_mult_pos_factor: "1 < n  \<Longrightarrow> (a::int) mod (n * a) = a"
apply (insert linorder_less_linear [of a 0])
apply (elim disjE)

  -- {* @{term "a < (0::int)"} *}
apply (rule mod_neg_neg_trivial [where b="n*a"]) apply simp
apply (subgoal_tac "n * a < 1 * a") apply simp
apply (rule mult_strict_right_mono_neg) apply assumption+
-- {* @{term "(0::int) = a"} *}
apply simp
  -- {* @{term "(0::int) < a"} *}
apply (rule mod_pos_pos_trivial) 
 apply force
apply (frule mult_strict_right_mono) apply assumption apply simp
done

lemma modwrap_zero [simp]: "0 modwrap b = 0"
by (simp add: modwrap_def mod_mult_pos_factor)

lemma modwrap_distrib_add_aux: "((a::int) + b) mod (2 * b) = (a + (- b)) mod (2 * b)"
proof (subgoal_tac "- b mod (2 * b) = b mod (2 * b)", 
       clarsimp simp add: zmod_zminus1_eq_if mod_mult_pos_factor)
  have f1: "2 * b + (a + - 1 * b) = a + b"
    by simp
  have "a - b = a + - 1 * b"
    by auto
  then show "(a + b) mod (2 * b) = (a - b) mod (2 * b)"
    using f1 by (metis mod_add_self1)
next
  show "- b mod (2 * b) = b mod (2 * b) "
  proof -
    have f1: "b + - 2 * b = - 1 * b"
      by auto
    have f2: "- 1 * (2 * b) = - 2 * b"
      by auto
    have f3: "\<forall>x0 x1. (x1::int) - x0 = x1 + - 1 * x0"
      by simp
    have "- b = - 1 * b"
      by auto
    then show ?thesis
      using f3 f2 f1 by (metis (no_types) zmod_zdiff_self2)
  qed
qed

lemma modwrap_distrib_add [simp]: 
  "( a modwrap c +  b modwrap c) modwrap c =  (a + b) modwrap c"
unfolding modwrap_def
proof (simp)
  have f1: "\<And>i ia. (i::int) + (ia - ia) = i"
    by presburger
  have f2: "\<And>i ia ib. (i::int) - ia + ib = i + (ib - ia)"
    by linarith
  then have f3: "\<And>i ia ib ic. ((i::int) + (ia mod ib - ic)) mod ib = (i - ic + ia) mod ib"
    by (metis (full_types) zmod_simps(2))
  have "\<And>i ia ib. (i::int) + (ia + ib) = ia + (i + ib)"
    by linarith
  then have "((a + c) mod (2 * c) + ((b + c) mod (2 * c) - c)) mod (2 * c) = 
             (c + (a + b)) mod (2 * c)"
    using f3 f2 f1 by presburger
  then show "((a + c) mod (2 * c) + (b + c) mod (2 * c) - c) mod (2 * c) = 
             (a + b + c) mod (2 * c)"
    by (simp add: add.commute add_diff_eq)
qed


lemma modwrap_add_self1[rule_format]: 
      "0 < b \<longrightarrow> (a + 2^b) modwrap 2^(b - 1) = a modwrap 2^(b - 1)"
apply clarsimp
apply (simp add: modwrap_def)
apply (subgoal_tac "(2::int) * 2^(b - Suc 0) = 2^b")
 apply clarsimp
 apply (subst add.commute)
 apply (subst add.assoc)
 apply simp
apply (case_tac b)
 apply simp
apply simp
done

lemma modwrap_smod_equal[rule_format]: 
      "0 < b \<longrightarrow> a modwrap 2^(b - 1) = a smod b"
apply clarsimp
apply (simp add: modwrap_def smod_def)
apply (simp add: Let_def)
apply (subgoal_tac "(2::int) * 2 ^ (b - Suc 0) = 2^b")
 apply clarsimp
 apply (rule conjI)
  apply clarsimp
  apply (insert mod_add_eq[where a="a" and b="2^(b - Suc 0)" and c="2^b"])
  apply clarsimp
  apply (subgoal_tac "a mod 2 ^ b + 2 ^ (b - Suc 0) mod 2 ^ b = a mod 2^b + 2^(b - Suc 0)")
   apply (simp (no_asm_simp))
	apply clarsimp
	apply (insert mod_pos_pos_trivial[where a="a mod 2 ^ b + 2 ^ (b - Suc 0)" and b="2^b"])
	apply clarsimp
	apply (subgoal_tac "(0::int) \<le> a mod 2 ^ b + 2 ^ (b - Suc 0)")
	 apply simp
	apply (subgoal_tac "(0::int) \<le> a mod 2^b \<and> (0::int) \<le> 2^(b - Suc 0)")
	 apply clarsimp
	apply (insert pos_mod_conj[where a="a" and b="2 ^ b"])
	apply (subgoal_tac "(0::int) < 2^b")
	 apply simp
  apply (simp add: int_mod_eq')
	apply (simp add: zero_less_power)
  apply clarsimp
  apply (insert mod_pos_pos_trivial[where a="2 ^ (b - Suc 0)" and b="2^b"])
  apply clarsimp
 apply clarsimp
 apply (subgoal_tac "(a mod 2 ^ b + 2 ^ (b - Suc 0)) mod 2 ^ b = a mod 2^b - 2^(b - Suc 0)")
  apply clarsimp
 apply (subgoal_tac "2 ^ (b - Suc 0) \<le> a mod 2 ^ b")
  apply clarsimp
  apply (subgoal_tac "a mod 2^b < 2^b")
   apply clarsimp
   apply (smt int_mod_eq' m2pths(2) zmod_zdiff_self2)
	apply (insert mod_add_self2 [where a="2^b" and b="a mod 2 ^ b + 2 ^ (b - Suc 0) - 2^b"])
	apply clarsimp
	apply (subgoal_tac "(a mod 2 ^ b + 2 ^ (b - Suc 0) - 2 ^ b) mod 2 ^ b = (a mod 2 ^ b - 2 ^ (b - Suc 0)) mod 2^b")
	 apply clarsimp
	apply (subgoal_tac "a mod 2 ^ b + 2 ^ (b - Suc 0) - 2 ^ b= a mod 2 ^ b - 2 ^ (b - Suc 0)")
	 apply (simp (no_asm_simp))
	apply clarsimp
  apply clarsimp
  using Suc_pred power_Suc
  apply metis
done  

subsection{*drop mod*}

lemma mult_less_mult: "(a::nat)<(b::nat) \<longrightarrow> b*c<(d::nat) \<longrightarrow> c>0 \<longrightarrow> a*c<d"
  apply (rule impI)+
  apply (insert less_trans[of "a*c" "b*c" "d"] )
  apply simp
done

lemma power_add_2: "2^a*2^b=(2::nat)^((a::nat)+b)"   (* legacy *)
  by (rule Semiring_Normalization.comm_semiring_1_class.semiring_normalization_rules(26))

lemma drop_is_mod: 
  "\<forall>bv. bv_to_nat (drop a bv)= bv_to_nat bv mod 2^(length bv - a)"
apply (induct_tac a)
 apply (simp add: bv_to_nat_upper_range)
apply (rule allI)+
apply (erule_tac x="tl bv" in allE)
apply (case_tac "bv=hd bv # tl bv")
 prefer 2
 apply (case_tac "bv=[]")
  apply simp
 apply simp 
apply simp
apply (rotate_tac -1, erule ssubst)
apply simp
apply (case_tac "bitval (hd bv) * 2 ^ (length bv - Suc 0) + bv_to_nat (tl bv)=
                 bv_to_nat (tl bv) + bitval (hd bv) * 2 ^ (length bv - Suc 0)")
 prefer 2
 apply simp
apply (rotate_tac -1, erule ssubst)
apply (case_tac "hd bv")
 apply simp
apply simp
apply (case_tac "(2::nat) ^ (length bv - Suc 0)=2^n*2 ^ (length bv - Suc n)")
 prefer 2
 apply (case_tac "length bv - Suc 0=n + length bv - Suc n")
  prefer 2
  apply (simp add: power_add)
 apply (rotate_tac -1, erule ssubst)
 apply (simp add: power_add_2)
 apply (case_tac "length bv<Suc n")
  apply simp
 apply simp
done

lemma drop_is_mod2: "bv_to_nat (drop (length bv - a) bv)= bv_to_nat bv mod 2^a"
apply (simp add: drop_is_mod)
apply (case_tac "length bv < a")
 prefer 2
 apply simp
apply (simp add: bv_to_nat_upper_range)
apply (case_tac "bv_to_nat bv<2 ^ a")
 apply simp 
apply (case_tac "bv_to_nat bv < 2 ^ length bv")
 apply (insert less_trans[of "bv_to_nat bv" "2 ^ length bv" "2^a"] )
 apply simp
apply (simp add: bv_to_nat_upper_range)
done

lemma drop_is_mod3: 
     "\<not> length bv < a \<longrightarrow> bv_to_nat (drop (b + (length bv - a)) bv) * 2^b= 
      bv_to_nat bv * 2^b mod 2^a"
apply (rule impI)+
apply (simp add: drop_is_mod)
apply (simp add: mult_mod_left)
apply (case_tac "a < b")
 prefer 2
apply (case_tac "(2::nat)^b = 2^(b-a) * 2^a")
 prefer 2
 apply (simp add: power_add_2)
using leI le_add_diff_inverse mult.commute mult_mod_right power_add
apply smt 
apply simp
apply (insert mult.assoc[of "bv_to_nat bv" "2 ^ (b - a)" "2 ^ a"])
using diff_is_0_eq' le_add_diff_inverse less_imp_le_nat mod_mult_self2_is_0 mult.commute
      mult_mod_right mult_numeral_1_right numeral_code(1) power_0 power_add
apply smt
done

lemma drop_is_mod4: 
      "length bv < a \<longrightarrow>\<not> b + length bv < a \<longrightarrow> 
       bv_to_nat (drop (b + length bv - a) bv) * 2^b = 
       bv_to_nat bv * 2^b mod 2^a"
apply (rule impI)+
apply (simp add: drop_is_mod)
apply (simp add: mult_mod_left)
apply (case_tac "a<b")
 apply simp
 prefer 2
apply (case_tac "(2::nat)^b = 2^(b-a) * 2^a")
 prefer 2
 apply (simp add: power_add_2)
using leI le_add_diff_inverse mult.commute mult_mod_right power_add
apply smt 
apply simp
apply (insert mult.assoc[of "bv_to_nat bv" "2 ^ (b - a)" "2 ^ a"])
using diff_is_0_eq' le_add_diff_inverse less_imp_le_nat mod_mult_self2_is_0 mult.commute
      mult_mod_right mult_numeral_1_right numeral_code(1) power_0 power_add
apply smt
done


subsection {* decomposition of @{text "nat_to_bv(x)"} by mod/div on x *}

declare Let_def[simp]

lemma nat_to_bv_div_fst_bv_chop: 
      "nat_to_bv (a div 2^n) = fst (bv_chop (nat_to_bv a) n)"
apply (induct_tac n)
 apply simp
 apply (simp add: bv_chop_def)
apply clarsimp
apply (simp add: bv_chop_def)
apply (subgoal_tac "a div (2 * 2^n ) = (a div 2^n) div 2")
 apply clarsimp
 apply (simp add: nat_to_bv_div_2_is_butlast2)
 apply (case_tac "n < length (nat_to_bv a)")
  apply (subgoal_tac "length (nat_to_bv a) - n = Suc (length (nat_to_bv a) - Suc n)")
   apply clarsimp
   apply (subst butlast_take)
    apply arith
   apply simp
  apply arith
 apply clarsimp
apply (subgoal_tac "a div (2^1*2^n) = (a div 2^n) div 2^1")
 apply simp
apply (subst power_div_add_eq)
apply simp
done

lemma nat_to_bv_mod_drop_aux[rule_format]:
     "a = bv_to_nat (norm_unsigned x) \<longrightarrow> nat_to_bv (a mod 2^n) = 
      norm_unsigned (drop (length (nat_to_bv a) - n) (nat_to_bv a))"
apply clarify
apply (subst drop_is_mod2[symmetric])
apply simp
done

lemma nat_to_bv_mod_drop[rule_format]:
     "nat_to_bv (a mod 2^n) = norm_unsigned (drop (length (nat_to_bv a) - n) (nat_to_bv a))"
apply (subgoal_tac "a = bv_to_nat (norm_unsigned (nat_to_bv a))")
 apply (frule_tac x="nat_to_bv a" in nat_to_bv_mod_drop_aux)
 apply simp
apply simp
done

lemma append_bv_chop_id: 
  "fst (bv_chop w l) @ snd (bv_chop w l) = w"
  by (simp add: bv_chop_def)

lemma bv_to_nat_bv_chop_append: 
      "bv_to_nat w = bv_to_nat (fst (bv_chop w n)) * 
                     2^n + bv_to_nat (snd (bv_chop w n))"
apply (subst append_bv_chop_id[symmetric, where l="n"])
apply (subst bv_to_nat_dist_append)
apply simp
apply clarsimp
apply (simp add: bv_chop_def)
using bv_to_nat_Nil diff_diff_cancel diff_is_0_eq gr_implies_not0 nat_le_linear take_0
apply metis 
done

lemma nat_to_bv_mod_snd_bv_chop: 
      "nat_to_bv (a mod 2^n) = norm_unsigned (snd (bv_chop (nat_to_bv a) n))"
  by (simp add: bv_chop_def nat_to_bv_mod_drop)

definition
  bv_slice :: "[bit list,nat*nat] => bit list" where
  "bv_slice w = (\<lambda>(b,e). fst (bv_chop (snd (bv_chop w (b+1))) e))"

lemma bv_to_nat_slice_nat_to_bv_arith:
  "bv_to_nat (bv_slice (nat_to_bv x) (a,b)) = (x mod 2^(Suc a)) div 2^b"
proof -
  have "bv_to_nat (bv_slice (nat_to_bv x) (a,b))
    = bv_to_nat (fst (bv_chop (snd (bv_chop (nat_to_bv x) (Suc a))) b))"
    by (simp add: bv_slice_def)
  also have "\<dots>
    = bv_to_nat (fst (bv_chop (norm_unsigned (snd (bv_chop (nat_to_bv x) (Suc a)))) b))"
    by (rule bv_to_nat_fst_bv_chop_norm_unsigned [symmetric])
  also have "\<dots>
    = bv_to_nat (fst (bv_chop (nat_to_bv (x mod 2^(Suc a))) b))"
    by (simp add: nat_to_bv_mod_snd_bv_chop [symmetric])
  also have "\<dots>
    = bv_to_nat (nat_to_bv ((x mod 2^(Suc a)) div 2^b))"
    by (simp add: nat_to_bv_div_fst_bv_chop)
  finally show ?thesis by simp
qed

lemma bv_to_nat_bv_slice: 
      "bv_to_nat (bv_slice wx (a,b)) = (bv_to_nat wx) mod 2 ^ Suc a div 2 ^ b"
apply (induct wx)
 apply (simp add: bv_slice_def)
 apply (simp add: bv_chop_def)
apply (case_tac "a < length wx")
 apply (subgoal_tac "bv_slice (aa # wx) (a, b) = bv_slice wx (a, b)")
  prefer 2
  apply (simp (no_asm) add: bv_slice_def)
  apply (simp add: bv_chop_def)
  apply (case_tac wx)
   apply simp
  apply simp
  apply (subgoal_tac "Suc (length list) - a = Suc (length list - a)")
   apply (rotate_tac -1, erule ssubst)
   apply simp
  apply (rule Suc_diff_le)
  apply simp
 apply (rotate_tac -1, erule ssubst)
 apply (erule ssubst)
 apply (subgoal_tac "aa # wx = [aa] @ wx")
  prefer 2
  apply simp
 apply (rotate_tac -1, erule ssubst)
 apply (subst bv_to_nat_dist_append)
 apply (subst mod_add_eq)
 apply (subgoal_tac "bv_to_nat [aa] * 2 ^ length wx mod 2 ^ Suc a = 0")
  apply (rotate_tac -1, erule ssubst)
  apply simp
 apply (subst mod_mult_right_eq)
 apply (subst nat_power_mod_cancel)
  apply simp
 apply simp
apply (subst mod_less)
 apply (rule bv_to_nat_less_power)
 apply simp
apply (case_tac "b \<le> length wx")
 apply (subgoal_tac "bv_slice (aa # wx) (a, b) = [aa] @ bv_slice wx (a, b)")
  prefer 2
  apply (simp (no_asm) add: bv_slice_def)
  apply (simp add: bv_chop_def)
  apply (subst Suc_diff_le, assumption)
  apply simp
 apply (rotate_tac -1, erule ssubst)
 apply (subst bv_to_nat_dist_append)
 apply (rotate_tac -1, erule ssubst)
 apply (subst mod_less)
  apply (rule bv_to_nat_less_power)
  apply simp
 apply (subgoal_tac "aa # wx = [aa] @ wx")
  prefer 2
  apply simp
 apply (rotate_tac -1, erule ssubst)
 apply (subst bv_to_nat_dist_append)
 apply (subst div_add1_eq)
 apply (subgoal_tac "bv_to_nat [aa] * 2 ^ length wx mod 2 ^ b = 0")
  prefer 2
  apply (subst mod_mult_right_eq)
  apply (subst nat_power_mod_cancel)
   apply simp
  apply simp
 apply (rotate_tac -1, erule ssubst)
 apply simp
 apply (subgoal_tac "length (bv_slice wx (a, b)) = length wx - b")
  prefer 2
  apply (simp add: bv_slice_def)
  apply (simp add: bv_chop_def)
  apply (simp add: min_def)
 apply (rotate_tac -1, erule ssubst)
 apply (case_tac aa, simp)
 apply simp
 apply (rule nat_power_div[THEN sym])
  apply simp
 apply simp
apply (subst div_less)
 apply (rule bv_to_nat_less_power)
 apply simp
apply (subgoal_tac "bv_slice (aa # wx) (a, b) = []")
 apply simp
apply (simp (no_asm) add: bv_slice_def)
apply (simp add: bv_chop_def)
done
  
definition
  length_nat :: "nat => nat" where
  "length_nat x = (LEAST n. x < 2 ^ n)"

lemma length_nat: 
      "length (nat_to_bv n) = length_nat n"
       apply (simp add: length_nat_def)
  using LeastI bv_nat_bv bv_to_nat_upper_range nat_less_le 
        nat_upper_limit_impl_length_nat_to_bv_limit not_less_Least
  apply metis
done
       
lemma nat_to_bv_mod_div_decompose: 
     "nat_to_bv a = nat_to_bv (a div 2^n) @ 
      bv_extend (min n (length_nat a)) (0::bit) (nat_to_bv (a mod 2^n))"
apply (subst length_nat[symmetric])
apply (subst nat_to_bv_mod_snd_bv_chop)
apply (subst nat_to_bv_div_fst_bv_chop)
apply (subgoal_tac "bv_extend (min n (length (nat_to_bv a))) (0::bit) 
                    (norm_unsigned (snd (bv_chop (nat_to_bv a) n))) = 
                    snd (bv_chop (nat_to_bv a) n)")
 apply simp
 apply (simp_all add: bv_chop_def)
apply (simp add: min_def)
apply (rule conjI)
 apply clarsimp
 apply (subst bv_extend_norm_unsigned2)
  apply (simp add: min_def)
apply (simp add: bv_extend_def)
apply (simp add: bv_extend_def)
done

declare Let_def[simp del]

subsection {*drop from bitvector *}
lemma hd_bv_zero_drop_1[rule_format]:
      "bv \<noteq> [] \<longrightarrow> hd bv = (0::bit) \<longrightarrow> bv_to_nat (drop 1 bv) = bv_to_nat bv"
apply (induct_tac bv)
 apply simp
apply clarsimp
done

lemma hd_bv_one_drop_1[rule_format]: 
      "bv \<noteq> [] \<longrightarrow> hd bv = (1::bit)  \<longrightarrow> bv_to_nat (drop 1 bv) = 
       (bv_to_nat bv - (2 ^(( length bv) - 1)))"
apply (induct_tac bv)
 apply simp
apply clarify
apply (case_tac "list ")
apply clarify
apply (simp add: bv_to_nat_def)
apply clarsimp
done

lemma drop_1_eq_mod_length[rule_format]:
      "bv \<noteq> [] \<longrightarrow> (bv_to_nat (drop 1 bv)) = (bv_to_nat bv) mod ((2::nat)^((length bv )- 1))"
apply simp
apply (case_tac "bv")
 apply simp
apply (case_tac " (hd bv)")
 apply clarify
 apply (frule hd_bv_zero_drop_1)
  apply simp
 apply (subgoal_tac "((bv_to_nat  list) < ((2::nat) ^ (length list)))")
  apply (subgoal_tac "((bv_to_nat (drop (1::nat) (a # list))) = 
                       (bv_to_nat (a # list))) \<longrightarrow> ((bv_to_nat (a # list)) = (bv_to_nat  list))")
   apply clarify
   apply (subgoal_tac "((2::nat) ^ (length list)) = 
                       ((2::nat) ^ ((length (a # list)) - (Suc (0::nat))))")
    apply (subgoal_tac "((hd (a # list)) = (0::bit)) \<longrightarrow> (a = (0::bit))")
     apply clarify
     apply (subgoal_tac "(bv_to_nat list) < ((2::nat) ^ ((length ((0::bit) # list)) - 
                         (Suc (0::nat))))")
      apply (erule  ssubst)+
      apply simp
     apply (subgoal_tac "((length ((0::bit) # list)) - (Suc (0::nat))) = (length list)")
      apply (erule ssubst)+
      apply simp
     apply (erule ssubst)+
     apply simp
    apply (thin_tac "((hd (a # list)) = (0::bit))")
    apply (erule ssubst)+
   apply (simp add: hd_append)
  apply simp
 apply simp
apply (simp add:  bv_to_nat_upper_range )
apply simp
apply (subgoal_tac "  (bv_to_nat list) < ((2::nat)^(length list))")
 apply simp
apply (simp add: bv_to_nat_upper_range)
done

lemma nat_to_bv_drop_1_mod_length [rule_format]:
      "0 \<le> x \<longrightarrow> length (nat_to_bv x) = bw \<longrightarrow> 
       (bv_to_nat (drop 1 ((nat_to_bv x)@[(0::bit)]))) =  (x * 2 mod(2^(bw)))"
apply (induct_tac bw)
 apply clarsimp
 apply (case_tac "x=0")
  apply clarsimp
apply (subgoal_tac "(nat_to_bv x) \<noteq> []")
prefer 2
apply (simp add: nat_to_bv_non0 nat_to_bv_def)
apply (frule_tac bv = "(nat_to_bv x)" in  drop_1_eq_mod_length)
apply simp
apply (simp add: bv_to_nat_dist_append)
apply (subgoal_tac "(((x * 2) mod (((2::nat) ^ n) * 2)) = ((x mod ((2::nat) ^ n)) * 2))")
apply (subgoal_tac "(((2::nat) ^ n) * (2::nat)) = ((2::nat) * ((2::nat) ^ n))")
apply simp_all
using bv_nat_bv bv_to_nat_dist_append drop_is_mod 
apply fastforce 
done

lemma hd_bv_zero_drop_bv_zero_drop_1_int[rule_format]:
      "(drop 1 bv) \<noteq> [] \<longrightarrow> hd bv = (0::bit) \<longrightarrow> ((hd (drop 1 bv)) = (0::bit) ) \<longrightarrow> 
        bv_to_int (drop 1 bv) = bv_to_int  bv"
apply (induct_tac bv)
 apply simp
apply (simp add:  bv_to_int_def bv_msb_def)
done

lemma hd_bv_zero_drop_bv_one_drop_1_int[rule_format]:
      "(drop 1 bv) \<noteq> [] \<longrightarrow> hd bv = (0::bit) \<longrightarrow> ((hd (drop 1 bv)) = (1::bit) ) \<longrightarrow>  
       bv_to_int (drop 1 bv) = bv_to_int  bv - (2^((length bv) - 1)) "
apply (induct_tac bv)
 apply simp
apply simp
apply clarsimp
apply (simp add:  bv_to_int_def bv_msb_def)
apply (subgoal_tac "bv_to_nat list = 2 ^ (length list) - bv_to_nat (bv_not list) - 1")
  prefer 2
  apply (rule bv_to_nat_as_complement)
apply (erule ssubst)+
apply simp 
apply (subgoal_tac "(int (((2::nat) ^ (length list)) - (Suc (bv_to_nat (bv_not list))))) = 
                    ((int ((2::nat) ^ (length list))) - (int (Suc (bv_to_nat (bv_not list)))))")
apply (simp add: int_power)
apply (subgoal_tac "length  list  = length (bv_not list)")
apply (erule ssubst)+
apply (subgoal_tac "(Suc (bv_to_nat (bv_not list))) \<le>((2::nat) ^ (length (bv_not list))) ")
apply (frule_tac m = "((2::nat) ^ (length (bv_not list)))" and 
                 n = "(Suc (bv_to_nat (bv_not list)))" in of_nat_diff)
   apply simp
   apply (subgoal_tac "bv_to_nat (bv_not list) < 2^ (length (bv_not list))")
   apply arith
   apply (simp only: bv_to_nat_upper_range)
   apply simp
done

lemma hd_bv_one_drop_bv_zero_drop_1_int[rule_format]:
      "(drop 1 bv) \<noteq> [] \<longrightarrow> hd bv = (1::bit)  \<longrightarrow> 
       ((hd (drop 1 bv)) = (0::bit) ) \<longrightarrow>  bv_to_int (drop 1 bv) = (bv_to_int  bv) + 
       ((2::int) ^ ((length bv) - (1::nat)))"
apply (induct_tac bv)
 apply simp
apply clarsimp
apply (simp add:  bv_to_int_def bv_msb_def)
apply (subgoal_tac "bv_to_nat list = 2 ^ (length list) - bv_to_nat (bv_not list) - 1")
  prefer 2
  apply (rule bv_to_nat_as_complement)
apply (erule ssubst)+
apply simp 
apply (subgoal_tac "(int (((2::nat) ^ (length list)) - (Suc (bv_to_nat (bv_not list))))) = 
                    ((int ((2::nat) ^ (length list))) - (int (Suc (bv_to_nat (bv_not list)))))")
apply (simp add: int_power)
apply (subgoal_tac "length  list  = length (bv_not list)")
apply (erule ssubst)+
apply (subgoal_tac "(Suc (bv_to_nat (bv_not list))) \<le>((2::nat) ^ (length (bv_not list))) ")
apply (frule_tac m = "((2::nat) ^ (length (bv_not list)))" and 
                 n = "(Suc (bv_to_nat (bv_not list)))" in of_nat_diff)
   apply simp 
   apply (subgoal_tac "bv_to_nat (bv_not list) < 2^ (length (bv_not list))")
   apply arith
   apply (simp only: bv_to_nat_upper_range)
   apply simp
done

lemma hd_bv_one_drop_bv_one_drop_1_int[rule_format]:
     "(drop 1 bv) \<noteq> [] \<longrightarrow> hd bv = (1::bit)  \<longrightarrow> ((hd (drop 1 bv)) = (1::bit)) \<longrightarrow>  
      bv_to_int (drop 1 bv) = (bv_to_int  bv) "
apply (induct_tac bv)
 apply simp
apply clarsimp
apply (case_tac "list")
apply clarify
apply (simp add:  bv_to_int_def bv_msb_def)
done

lemma drop_not_eq_list_not_eq: 
      "(drop 1 bv) \<noteq> [] \<longrightarrow> bv \<noteq> []"
apply (induct "bv")
apply auto
done

declare drop_not_eq_list_not_eq [simp]

lemma drop_1_eq_smod_length[rule_format]:
      "(drop 1 bv)  \<noteq> [] \<longrightarrow> (bv_to_int (drop 1 bv)) = 
                             (bv_to_int bv) smod ((length bv) - 1)"
apply (case_tac "(hd bv)")
 apply (case_tac "(hd (drop 1 bv))")
  apply clarify
  apply (frule_tac  bv = "bv" in hd_bv_zero_drop_bv_zero_drop_1_int)
    apply simp
   apply simp
  apply simp
  apply (subgoal_tac "(bv_to_int bv) < (2 ^ ((length bv) - 1))")
   apply (simp add: bv_to_int_def bv_msb_def)
   apply (simp add: "smod_def" Let_def)
   apply (simp add: mod_pos_pos_trivial)
   apply (case_tac bv)
    apply simp
   apply simp
   apply (case_tac list)
    apply simp
   apply (subgoal_tac "bv_to_nat list < 2^((length list) - 1)")
    prefer 2
    apply (simp add: bv_to_nat_upper_range)
   apply (subgoal_tac "((bv_to_nat list) < ((2::nat) ^ ((length list) - (1::nat)))) =
                       ((int (bv_to_nat list)) < (int((2::nat) ^ ((length list) - (Suc (0::nat))))))")
    apply (simp add: int_power)
   apply (simp add: of_nat_less_iff)
   apply (metis of_nat_numeral of_nat_power of_nat_less_iff)
  apply (frule_tac  w = "bv"  in bv_to_int_upper_range)
(*case (0::bit)#(1::bit)#(drop 2 bv)*)
 apply clarify
 apply (frule_tac  bv = "bv" in hd_bv_zero_drop_bv_one_drop_1_int)
   apply simp
  apply simp
 apply (simp add: "smod_def" Let_def)
 apply (subgoal_tac "(bv_to_int bv) < ((2::int) ^ ((length bv) - (Suc (0::nat))))")
  apply (simp add: bv_to_int_def bv_msb_def)
  apply (simp add: mod_pos_pos_trivial)
  apply (case_tac "bv")
   apply simp
  apply simp
  apply (case_tac "list")
   apply simp
  apply simp
 apply (insert bv_to_int_upper_range [of "bv"])
 apply simp
(*case (1::bit)#bs*)
apply (case_tac "(hd (drop 1 bv))")
(*case (1::bit)#(0::bit)#bs*)
 apply clarify
 apply (frule_tac  bv = "bv" in hd_bv_one_drop_bv_zero_drop_1_int)
   apply simp
  apply simp
 apply simp
 apply (simp add: smod_def Let_def) 
 apply (case_tac "(bv_to_int bv) = (- ((2::int) ^ ((length bv) - (Suc (0::nat)))))")
  apply simp
  apply (insert mod_mult_self2_is_0 [of "-1 " "((2::int) ^ ((length bv) - (Suc (0::nat))))"] )
  apply simp
 apply (subgoal_tac "(bv_to_int bv) < 0")
  prefer 2
  apply (simp add: bv_to_int_def bv_msb_def)
 apply (subgoal_tac "0 \<le> (bv_to_nat (bv_not bv))")
  prefer 2
  apply simp
 apply (frule_tac a = "(bv_to_int bv)" and b = "((2::int) ^ ((length bv) - (Suc (0::nat))))" in 
        negative_mod)
   apply simp
  apply (insert bv_to_int_lower_range [of "bv"])
  apply simp
 apply simp
 apply (simp add: bv_to_int_def bv_msb_def)
 apply (subgoal_tac "bv_to_nat (bv_not bv) = 2^(length bv) - (bv_to_nat bv) - 1")
  apply simp 
  apply (subgoal_tac "(int (((2::nat) ^ (length bv)) - (Suc (bv_to_nat bv)))) = 
                      ((int ((2::nat) ^ (length bv))) - (int (Suc (bv_to_nat bv))))")
   apply (simp add: int_power)
   apply (case_tac "bv")
    apply simp
   apply simp
   apply (case_tac "list")
    apply simp
   apply simp
  apply (subgoal_tac "(Suc (bv_to_nat bv)) \<le>((2::nat) ^ (length bv)) ")
   apply (frule_tac m = "((2::nat) ^ (length bv))" and n = "(Suc (bv_to_nat bv))" in of_nat_diff)
   apply simp 
  apply (subgoal_tac "bv_to_nat bv < 2^ (length bv)")
   apply arith
  apply (simp only: bv_to_nat_upper_range)
 apply (subgoal_tac "bv_to_nat bv = 2 ^ (length bv) - bv_to_nat (bv_not bv) - 1")
  apply (erule ssubst)+
  apply (subgoal_tac "(bv_to_nat (bv_not bv)) < (((2::nat) ^ (length bv)))")
   apply arith
  apply (subgoal_tac "(length bv) = length (bv_not bv)")
   apply (erule ssubst)+
   apply (simp only: bv_to_nat_upper_range)
  apply simp
 apply (rule bv_to_nat_as_complement)
 using One_nat_def Suc_pred add.right_neutral add_Suc_right bv_to_nat_as_complement
       bv_to_nat_upper_range diff_diff_cancel diff_diff_left length_map 
       less_imp_le_nat zero_less_diff 
 apply smt 
(*case (1::bit)#(1::bit)#bs*)
apply clarify
apply (frule_tac  bv = "bv" in hd_bv_one_drop_bv_one_drop_1_int)
  apply simp
 apply simp
apply simp
apply (simp add: smod_def Let_def)
apply (simp add: bv_to_int_def bv_msb_def)
apply (subgoal_tac "bv_to_nat (bv_not bv) = 2^(length bv) - (bv_to_nat bv) - 1")
 apply simp 
 prefer 2
 apply (subgoal_tac "bv_to_nat bv = 2 ^ (length bv) - bv_to_nat (bv_not bv) - 1")
  apply (erule ssubst)+
  apply (subgoal_tac "(bv_to_nat (bv_not bv)) < (((2::nat) ^ (length bv)))")
   apply arith
  apply (subgoal_tac "(length bv) = length (bv_not bv)")
   apply (erule ssubst)+
   apply (simp only: bv_to_nat_upper_range)
  apply simp
 apply (rule bv_to_nat_as_complement)
apply (subgoal_tac "(int (((2::nat) ^ (length bv)) - (Suc (bv_to_nat bv)))) = 
                    ((int ((2::nat) ^ (length bv))) - (int (Suc (bv_to_nat bv))))")
 apply (simp add: int_power)
 apply (subgoal_tac "((- ((2::int) ^ (length bv))) + (int (bv_to_nat bv))) < 0")
  prefer 2
  apply (subgoal_tac "((int(bv_to_nat bv)) < (int ((2::nat) ^ (length bv))))")
   apply (simp add: int_power)
  apply (simp add: of_nat_less_iff)
 apply (frule_tac a = "((- ((2::int) ^ (length bv))) + (int (bv_to_nat bv)))" and 
                  b = "((2::int) ^ ((length bv) - (Suc (0::nat))))" in negative_mod)
   apply simp 
  apply (thin_tac "((- ((2::int) ^ ((length bv) - (Suc (0::nat))))) = 
                   (((2::int) ^ ((length bv) - (Suc (0::nat)))) * q))")
  apply simp
  apply (case_tac "bv")
   apply simp 
  apply simp
  apply (frule_tac list = "list" in  bv_to_nat_non_zero)
   apply simp
  apply (simp add: int_power)
 apply simp
 apply (case_tac "bv")
  apply simp
 apply (thin_tac "((- ((2::int) ^ ((length bv) - (Suc (0::nat))))) = 
                  (((2::int) ^ ((length bv) - (Suc (0::nat)))) * q))")
 apply simp
 apply (frule_tac list = "list" in  bv_to_nat_non_zero)
  apply simp
 apply (subgoal_tac "0 < bv_to_nat list")
  prefer 2
  apply arith
 apply (frule_tac w = "list" in bv_to_nat_lower_limit)
 apply simp
 apply (case_tac "list")
  apply simp+
apply (subgoal_tac "(Suc (bv_to_nat bv)) \<le>((2::nat) ^ (length bv)) ")
 apply (frule_tac m = "((2::nat) ^ (length bv))" and n = "(Suc (bv_to_nat bv))" in of_nat_diff)
 apply simp 
apply (subgoal_tac "bv_to_nat bv < 2^ (length bv)")
 apply arith
apply (simp only: bv_to_nat_upper_range)
done

declare drop_not_eq_list_not_eq [simp del]

lemma int_to_bv_drop1_append_zero_smod_length[rule_format]:
     "length (int_to_bv x) = bw \<longrightarrow> 
      bv_to_int (drop 1 ((int_to_bv x)@[(0::bit)])) = x * 2 smod bw"
apply (induct_tac bw)
 apply clarsimp
 apply (case_tac "x=0")
  apply (clarsimp simp add: nat_to_bv_def smod_def )
 apply (frule int_to_bv_not_zero_is_not_empty)
 apply simp
apply clarsimp
apply (case_tac "n")
apply simp
apply (simp add: smod_def Let_def)
apply simp
apply (subgoal_tac "(drop (Suc (0::nat)) (int_to_bv x)) \<noteq> []")
prefer 2
apply simp
apply (insert drop_1_eq_smod_length [of  "(int_to_bv x)"])
apply simp
apply (simp add: bv_to_int_def bv_msb_def)
apply (subgoal_tac "(Suc nat) = n")
apply (thin_tac "(n = (Suc nat))")
apply simp
apply (case_tac "(hd (drop (Suc (0::nat)) (int_to_bv x)))")
apply simp
apply (simp add: bv_to_nat_dist_append)
apply (subgoal_tac "(((((2::int) ^ (1::nat)) * x) smod ((1::nat) + n)) = 
                    (((2::int) ^ (1::nat)) * (x smod n)))")
apply simp
apply (simp add: mult_ac )
apply (simp add: smod_def Let_def split: if_split_asm)
using One_nat_def Suc_n_not_le_n bv_int_bv bv_to_int_lower_range bv_to_int_upper_range 
      diff_Suc_less int_mod_eq' length_int_to_bv_upper_limit_gt0 
      length_int_to_bv_upper_limit_lem1 mod_add_self1 not_less_eq power_strict_increasing_iff 
      zero_less_Suc
apply smt
apply auto[1]
apply simp 
apply (simp add: bv_to_nat_dist_append smod_def Let_def split: if_split if_split_asm)
apply auto
done

declare int_to_bv_lt0 [simp add]

subsection {* Bit and Bit Vectors for Hardware *}

text{* pretty printing for operations on bitvetctors*}
syntax (xsymbols)
bv_select :: "[bit list,nat] => bit" ("_^\<^sub>b_" [40] 40)

syntax "_bv_slice"
  :: "[bit list, nat, nat] => bit list" ("_^[_,_]" [100,50,50] 100)
translations "x^[y,z]" == "CONST bv_slice x (y, z)"

text{*alias for bit vector*}
type_synonym bv = "bit list"

text {* alias for @{const bv_to_nat} *}
definition bv2nat :: "bv\<Rightarrow>nat"
where     "bv2nat w = (*nat*) (bv_to_nat w)"

text{*alias for @{const nat_to_bv} *}
text{*we changed definition @{const nat_to_bv} for 0 because for
hardware @{term "nat_to_bv 0"} should return @{term "[Zero]"} and not the empty list @{term "[]"}*}
definition nat2bv :: "nat \<Rightarrow> bv"
where      "nat2bv n = (if n = 0 then [0] else nat_to_bv ((*int*) n))"

text {* \textbf{Conversion functions} between bit vectors and numbers. *}
definition
  -- "convert nat into bv of a desired length"
  nat2bvn :: "nat \<Rightarrow> nat \<Rightarrow> bit list"
where  "nat2bvn n a = (let v = (nat_to_bv a) in
        drop (length v - n) (bv_extend n (0::bit) v))"
definition
  -- "convert int into bv of a desired length"
  int2bvn :: "nat \<Rightarrow> int \<Rightarrow> bit list"
where  "int2bvn n a = (let v = (int_to_bv a) in
     drop (length v - n) (bv_extend n (bv_msb v) v))"

   
text{*bit as bool*}
definition bit2bool :: "bit \<Rightarrow> bool"
where "bit2bool a = (if a = 1 then True else False)"

text{*bool as bit*}
definition bool2bit :: "bool \<Rightarrow> bit"
where "bool2bit a = (if a then 1 else (0::bit))"

lemma[simp] : "bv_to_nat [b] = bitval b"
  by (cases b,simp_all)

lemma length_bv_slice: "m < length wx \<Longrightarrow> length (wx^[m,n]) = Suc m - n"
  by (simp add: bv_slice_def bv_chop_def Let_def)

lemma bv_slice_is_empty: "n < m \<Longrightarrow> wx^[n,m] = []"
apply (simp add: bv_slice_def bv_chop_def)
apply (case_tac wx)
 apply simp
apply simp
done

lemma bv_slice_is_not_empty: "\<lbrakk> n \<le> m; n < length xs \<rbrakk> \<Longrightarrow> xs^[m,n] \<noteq> []"
apply (simp add: bv_slice_def bv_chop_def)
apply (case_tac xs, simp)
apply simp
apply arith
done

lemma bv_slice_from_0_is_not_empty: "xs \<noteq> [] \<Longrightarrow> xs^[m,0] \<noteq> []"
apply (rule bv_slice_is_not_empty)
 apply simp
apply simp
done

lemma bv_slice_all: "length ax \<le> Suc k \<Longrightarrow> ax^[k,0] = ax"
  by (simp add: bv_slice_def bv_chop_def)

definition
  bv_select :: "[bit list,nat] => bit" where
  "bv_select w i = w ! (length w - 1 - i)"

lemma bv_msb_bv_slice:
      "\<lbrakk> n \<le> m; m < length wx \<rbrakk> \<Longrightarrow> bv_msb (wx^[m,n]) = ((wx^[m,n])^\<^sub>b(m - n))"
apply (simp add: bv_msb_def)
apply (intro conjI impI)
 apply (simp add: bv_slice_def bv_chop_def Let_def)
apply (simp add: bv_select_def)
apply (case_tac " wx^[m,n]")
 apply simp
apply simp
using Nat.diff_diff_right Suc_diff_le Suc_leI Suc_n_not_le_n diff_is_0_eq' 
      length_Cons length_bv_slice not_less nth_Cons' 
apply metis
done

lemma bv_slice_bv_slice_in: 
      "\<lbrakk>i < length w \<rbrakk> \<Longrightarrow> w^[i,j]^[k,l] = (w^[min i (k+j), l+j])"
apply (simp add: bv_slice_def bv_chop_def Let_def)
apply (subgoal_tac "min (Suc i) (Suc i - j) = Suc i - j")
 prefer 2
 apply arith
apply (rotate_tac -1, erule ssubst)
apply (case_tac "k + j \<le> i")
 apply simp
 apply (subgoal_tac "min i (k + j) = k + j")
  prefer 2
  apply arith
 apply (rotate_tac -1, erule ssubst)
 apply simp
 apply (subgoal_tac "\<exists> a v b c d. w = a @ [v] @ b @ c @ d \<and> length d = j \<and> 
                                  length c = k \<and> length b = i - (k + j)")
  prefer 2
  apply (subgoal_tac "w = take (length w - i) w @ drop (length w - i) w")
   prefer 2
   apply simp
  apply (rotate_tac -1, erule ssubst)
  apply (case_tac "rev (take (length w - i) w)")
   apply simp
  apply (drule rev_Cons)
  apply (erule ssubst)
  apply (rule_tac x = "rev list" in exI)
  apply (rule_tac x = "a" in exI)
  apply (rule_tac x = "take (i - (k + j)) (drop (length w - i) w)" in exI)
  apply (rule_tac x = "take k (drop (i - (k + j)) (drop (length w - i) w))" in exI)
  apply (rule_tac x = "drop k (drop (i - (k + j)) (drop (length w - i) w))" in exI)
  apply (subst append_assoc[THEN sym])
  apply (rule conjI)
   apply (subst append_eq_append_conv)
    apply simp
   apply (rule conjI)
    apply (rule refl)
   apply (subgoal_tac "drop (length w - i) w = 
                       take (i - (k + j)) (drop (length w - i) w) @ 
                       drop (i - (k + j)) (drop (length w - i) w)")
    prefer 2
    apply (rule append_take_drop_id[THEN sym])
   apply (erule ssubst)
   apply (subst append_eq_append_conv)
    apply simp
   apply (rule conjI)
     apply auto[1]
    apply auto[1]
    using add_diff_cancel_left' atd_lem drop_drop le_add1 le_less_trans less_or_eq_imp_le
          ordered_cancel_comm_monoid_diff_class.add_diff_assoc2
          ordered_cancel_comm_monoid_diff_class.diff_diff_right
    apply smt
    apply auto[1]
    apply auto[1]
 oops

lemma bv_is_append_of_two_parts:
      "0 < l \<Longrightarrow> wx = (wx^[length wx - 1, l]) @ (wx^[l - 1, 0])"
  by (simp add: bv_slice_def bv_chop_def Let_def)

lemma bv_slice_2_append: 
      "\<lbrakk> m < length wx; k \<le> m; n \<le> k \<rbrakk> \<Longrightarrow> wx^[m,n] = (wx^[m,k+1]) @ (wx^[k,n])"
apply (simp add: bv_slice_def bv_chop_def Let_def)
apply (subst take_2_append_take[of "Suc m - k" "Suc m - n"])
 apply arith
apply simp
apply (subst Cons_nth_drop_Suc[of "length wx - Suc k", THEN sym])
 apply arith
apply (subst Suc_diff_le[THEN sym])
 apply simp
apply simp
apply (rule sym)
apply (subst Suc_diff_le, assumption)
apply simp
apply (subst Suc_diff_le, assumption)
apply (subst take_Suc_conv_app_nth)
 apply simp
apply simp
done

lemma bv_slice_2_bv_select_append_bv_slice:
      "\<lbrakk> Suc m < length wx; n \<le> m \<rbrakk> \<Longrightarrow> wx^[Suc m,n] = (wx^\<^sub>b(Suc m)) # (wx^[m,n])"
apply (frule_tac k = "m" and n = "n" in  bv_slice_2_append)
  apply simp
 apply assumption
apply (rotate_tac -1, erule ssubst)
apply (simp add: bv_slice_def bv_chop_def bv_select_def Let_def)
apply (subst take_Suc_conv_app_nth)
 apply simp
apply simp
done

lemma bv_to_nat_mod_is_bv_to_nat_bv_slice:
      "\<lbrakk> 0 < l; l \<le> length wx \<rbrakk> \<Longrightarrow> bv_to_nat wx mod 2 ^ l = bv_to_nat (wx^[l - 1,0])"
apply (frule_tac wx = "wx" in bv_is_append_of_two_parts)
apply (erule_tac P = "\<lambda>q. bv_to_nat q mod _ = _" in ssubst)
apply (subgoal_tac "2 ^ l = 2 ^ length (wx^[l - 1,0])")
 apply (erule ssubst)
 apply (rule bv_to_nat_append_mod_length)
apply (subst length_bv_slice)
 apply arith
apply simp
done

lemma bv2nat_bv_slice_less_power: 
      "n < length wx \<Longrightarrow> bv2nat (wx^[n+m,n]) < 2^(Suc m)"
apply (simp only: bv2nat_def)
apply (rule bv_to_nat_less_power)
apply (simp add: bv_slice_def bv_chop_def Let_def)
done

lemma bv2nat_bv_slice_from_zero_less_power: 
      "bv2nat (wx^[m,0]) < 2^(Suc m)"
apply (case_tac "wx = []")
 apply (simp add: bv_slice_def bv_chop_def)
 apply (simp add: bv2nat_def)
apply (rule_tac y = "bv2nat (wx^[0+m,0])" in le_less_trans)
 apply simp
apply (rule bv2nat_bv_slice_less_power)
apply simp
done

lemma bv_select_eq_bv_slice: "i < length wx \<Longrightarrow> [wx^\<^sub>bi] = wx^[i,i]"
apply (simp add: bv_select_def bv_slice_def bv_chop_def)
apply (subgoal_tac "\<exists> xs a ys. length ys = i \<and> length a = 1 \<and> xs @ a @ ys = wx")
 apply (elim exE conjE)
 apply (rotate_tac -1, erule subst)
 apply simp
 apply (subst nth_append, simp)
 apply (subst nth_append, simp)
 apply (case_tac a, simp)
 apply simp
apply (rule_tac x = "take (length wx - 1 - i) (take (length wx - i) wx)" in exI)
apply (rule_tac x = "drop (length wx - 1 - i) (take (length wx - i) wx)" in exI)
apply (rule_tac x = "drop (length wx - i) wx" in exI)
apply (intro conjI)
  apply simp
 apply simp
apply (subst append_assoc[THEN sym])
apply (subst append_take_drop_id)
apply (rule append_take_drop_id)
done

text{*first argument must be a constant*}
definition
  bv_add_N :: "nat \<Rightarrow> bv\<Rightarrow>bv\<Rightarrow>bv"
where  "bv_add_N N op1 op2 =( let nat1 = bv2nat op1;
                              nat2 = bv2nat op2;
                              temp = if nat1 + nat2 < 2^N
                                   then nat1 + nat2
                                   else nat1 + nat2 - 2^N
                           in (nat2bvn N temp))"

definition
bv_add_int_N :: "nat \<Rightarrow> bv\<Rightarrow>bv\<Rightarrow>bv"
where  "bv_add_int_N N op1 op2 =( let int1 = bv_to_int op1;
                               int2 = bv_to_int op2;
                              temp = if int1 + int2 < 2^N
                                   then int1 + int2
                                   else int1 + int2 - 2^N
                           in (int2bvn N temp))"


definition bv_uminus_N :: "nat \<Rightarrow> bv\<Rightarrow>bv"
 where "bv_uminus_N N op1 = 
       (if   bv_to_int op1 = (-2)^(N - 1)
        then op1
        else int2bvn N (- bv_to_int op1))"

definition bv_sub_N :: "nat \<Rightarrow>bv\<Rightarrow>bv\<Rightarrow>bv"
where  "bv_sub_N N op1 op2 = bv_add_N N op1 (bv_uminus_N N op2)"

definition
  bv_mult_N :: "nat \<Rightarrow> bv\<Rightarrow>bv\<Rightarrow>bv"
where  "bv_mult_N N op1 op2 = 
        (let nat1 = bv2nat op1;
             nat2 = bv2nat op2;
             temp = if nat1 * nat2 < 2^N
                  then nat1 * nat2
                  else nat1 * nat2 - 2^N
          in (nat2bvn N temp))"

text{*32-bits aliasing*}
definition
 bv_add_32 :: "bv\<Rightarrow>bv\<Rightarrow>bv"
 where  "bv_add_32 op1 op2 = bv_add_N 32 op1 op2"

definition bv_uminus_32 :: "bv\<Rightarrow>bv"
where  "bv_uminus_32 op1 = bv_uminus_N 32 op1"

definition bv_sub_32 :: "bv\<Rightarrow>bv\<Rightarrow>bv"
where  "bv_sub_32 op1 op2 = bv_sub_N 32 op1 op2"

(************************************)
text{*bit wise operations; noth argumets of the same length*}
definition bv_and :: "bv\<Rightarrow>bv\<Rightarrow>bv"
where  "bv_and a b = map (%x. fst x AND snd x) (zip a b)"

definition bv_or :: "bv\<Rightarrow>bv\<Rightarrow>bv"
where "bv_or a b = map (%x. fst x OR snd x) (zip a b)"

definition bv_xor :: "bv\<Rightarrow>bv\<Rightarrow>bv"
where  "bv_xor a b = map (%x. (fst x) XOR (snd x)) (zip a b)"

definition bv_nand :: "bv\<Rightarrow>bv\<Rightarrow>bv"
where  "bv_nand bv1 bv2 = bv_not(bv_and bv1 bv2)"

definition bv_nor :: "bv\<Rightarrow>bv\<Rightarrow>bv"
where  "bv_nor bv1 bv2 = bv_not(bv_or bv1 bv2)"

definition bv_xnor :: "bv\<Rightarrow>bv\<Rightarrow>bv"
where  "bv_xnor bv1 bv2 = bv_not(bv_xor bv1 bv2)"

lemma bv_to_nat_helper': 
      "bv \<noteq> [] \<Longrightarrow> bv_to_nat bv = bitval (hd bv) * 2 ^ (length bv - 1) + bv_to_nat (tl bv)"
  by (cases bv,simp_all)

(*************************************)
text{*shifts operations*}

text{* Bitvector left shift *}
definition bv_left_shift :: "nat \<Rightarrow> bv \<Rightarrow> bv"
where  "bv_left_shift k w == (w @ (replicate k 0))^[length w - 1, 0]"

text{* Bitvector right shift *}
definition bv_right_shift :: "nat \<Rightarrow> bv \<Rightarrow> bv"
where  "bv_right_shift k w == (replicate k 0) @ (w^[length w - 1, k])"

(*************************************)

definition maxint_32 :: int
where  "maxint_32 == (2^31) - 1"

definition minint_32 :: int
where  "minint_32 == -(2^31)"

definition in_rng_2s_comp_32 :: "int\<Rightarrow>bool"
where  "in_rng_2s_comp_32 x == minint_32 \<le> x \<and> x \<le> maxint_32"

(************************************)

definition bv_and_bit :: "bv \<Rightarrow> bit \<Rightarrow> bv"
where  "bv_and_bit a b == map (%x. x AND b) a"

definition bv_or_bit :: "bv \<Rightarrow> bit \<Rightarrow> bv"
where  "bv_or_bit a b == map (%x. x OR b) a"

definition bv_xor_bit :: "bv \<Rightarrow> bit \<Rightarrow> bv"
where  "bv_xor_bit a b == map (%x. x XOR b) a"

lemma bit_and_bv_One: "bv_and_bit bv (1::bit) = bv"
  by(simp add: bv_and_bit_def)


lemma bit_and_bv_Zero: "bv_and_bit bv 0 = (replicate (length bv) 0)"
apply(simp add: bv_and_bit_def)
apply(induct_tac bv)
 apply simp
apply simp
done

(************************************************************)
text{*less operation on bit vectors for integers and natural*}
fun bv_less :: "(bv \<times> bv) \<Rightarrow> bool"
where 
  "bv_less ([], [])  =     False"
 | "bv_less ((a#as), (b#bs))  = (
                       if a = b then bv_less (as, bs)
                       else if a = 0 \<and> b = 1 then True
                       else False)"

definition bv_le :: "bv \<Rightarrow> bv \<Rightarrow> bool"
  where "bv_le a b = ((bv_less (a, b)) \<or> a = b) "

definition bv_gt :: "bv \<Rightarrow> bv \<Rightarrow> bool"
  where "bv_gt a b =  (bv_less (b, a))"

definition bv_ge :: "bv \<Rightarrow> bv \<Rightarrow> bool"
  where "bv_ge a b = ((bv_less (b, a)) \<or> a = b)"

definition bv_eq :: "bv \<Rightarrow> bv \<Rightarrow> bool"
 where"bv_eq a b = (a = b)"
(*******************)
definition minbv_32 :: "bv"
  where  "minbv_32 =  (1::bit) # (replicate 31 (0::bit))"

definition maxbv_32 :: "bv"
  where "maxbv_32 =  (0::bit) # (replicate 31 (1::bit))"
(*******************)
text{*less operation on bit vectors for integers*}
definition bv_less_int :: "bv \<Rightarrow> bv \<Rightarrow> bool"
  where "bv_less_int a b =
        (if (hd a = hd b) then (bv_less (tl a, tl b)) else (hd a = (1::bit)))"

definition bv_less_eq_int :: "bv \<Rightarrow> bv \<Rightarrow> bool"
  where "bv_less_eq_int a b = (bv_less_int a b \<or> a = b)"

text{*test if a bit vector is in range for 32-bit two's complement numbers *}
definition in_rng_bv_N :: "nat \<Rightarrow> bv \<Rightarrow> bool"
  where "in_rng_bv_N n a = 
         (let  min_bv = bv_extend n (1::bit) minbv_32;
               max_bv = bv_extend n (0::bit) maxbv_32
          in (bv_less_eq_int min_bv a) \<and> (bv_less_eq_int a max_bv))" 

text{*create lits of bit-vector indexes*}

primrec upto_bv :: "nat \<Rightarrow> nat list"
where
  "upto_bv 0 = [0]"
| "upto_bv (Suc n) = (Suc n)#(upto_bv n)"

lemma bv_and_replicate_zeros[rule_format]: 
      "! n. n = length xs \<longrightarrow> bv_and xs (replicate n (0::bit)) = replicate n (0::bit)"
apply (simp add: bv_and_def)
apply (induct xs)
 apply simp
apply (case_tac a)
 apply simp_all
done

lemma bv_less_correct: 
      "!b. length a = length b \<longrightarrow> bv_less(a, b)  = (bv_to_nat a < bv_to_nat b)"
apply(induct a)
 apply(simp add: bv2nat_def)
apply(rule allI, case_tac b)
 apply simp
apply(simp add: bv2nat_def)
apply(case_tac "a = a1")
 apply simp
 apply(case_tac a1)
  apply simp
 apply simp
apply(case_tac "a")
 apply(case_tac "a1")
  apply simp
 apply simp 
 apply(cut_tac w = list in bv_to_nat_upper_range)
 apply(case_tac "bv_to_nat list = 0")
  apply simp
 apply(case_tac "0<bv_to_nat list")
  apply simp
 apply simp
apply(case_tac a1, simp_all)
apply(cut_tac w = a2 in bv_to_nat_upper_range)
apply auto
done

lemma bv_le_correct: "length a = length b \<longrightarrow> bv_le a b  = (bv_to_nat a \<le> bv_to_nat b)"
apply clarsimp
apply (simp add: bv_le_def)
apply (simp add: bv_less_correct)
apply auto
apply (case_tac "bv_to_nat a = bv_to_nat b")
 apply simp
apply auto
using bv_extend_norm_unsigned nat_bv_nat
apply metis
done

lemma bv_less_inj : "a = b \<longrightarrow> bv_less a = bv_less b"
by auto

lemma  bv2int_inj : "a = b \<longrightarrow> bv_to_int a = bv_to_int b"
by auto

lemma bv_to_nat_bi : "length a = length b \<longrightarrow> (a = b) = (bv_to_nat a = bv_to_nat b)"
apply(rule impI, rule iffI)
apply simp
using bv_extend_norm_unsigned nat_bv_nat
apply metis
done

lemma bv_not_bi : "!b. (a=b) = (bv_not a = bv_not b)"
apply(induct a)
 apply(rule allI)
 apply(case_tac b)
  apply simp_all
apply(rule allI)
apply(case_tac b)
 apply simp_all
apply(erule_tac x=list in allE)
apply(case_tac a)
 apply(case_tac a1, simp_all)
apply(case_tac a1, simp_all)
done

lemma bv_to_int_bi : "length a = length b \<longrightarrow> (a = b) = (bv_to_int a = bv_to_int b)"
apply(rule impI, rule iffI)
 apply simp
apply(simp add:  bv_to_int_qinj)
done

(******************)                                                                                                                                                         
lemma bv_less_int_correct: 
     "\<forall> b. length a = length b \<and> a~=[] \<longrightarrow> (bv_to_int a < bv_to_int b) = (bv_less_int a b)"
apply(induct a, simp)
apply(simp add: bv_less_int_def)
apply(intro allI impI)
apply(case_tac "a2=[]", simp)
 apply(simp_all add: bv_to_int_def)
 apply(case_tac a1, simp_all add: bv_msb_def)
  apply(case_tac b, simp_all)
  using length_is_1_impl_list_is_head 
   apply fastforce
 apply(case_tac b, simp_all)
 apply(case_tac a, simp_all split: bit.split_asm if_split_asm)
 apply (simp add: bv_less_correct)
 apply (simp add: bv_less_correct) 
apply(case_tac b, simp)
apply(erule_tac x=list in allE)
apply simp
apply(case_tac "a1=a", simp)
 apply(simp add: bv_less_correct)
 apply(case_tac a, simp)
 apply simp
 apply(intro impI)
 apply(cut_tac xs=list in bv_to_nat_as_complement)
 apply(cut_tac xs=a2 in bv_to_nat_as_complement)
 apply simp
 apply(subgoal_tac "Suc (bv_to_nat (bv_not a2)) \<le> 2 ^ length list")
  apply arith
 apply(cut_tac w="(bv_not a2)" in bv_to_nat_upper_range)
 apply(subgoal_tac "length (bv_not a2) = length a2")
  apply simp
 apply simp
apply simp
apply(case_tac "a1", simp)
 apply(simp add: bv_to_int_def)
 apply(case_tac a, simp)
 apply simp
apply(case_tac a, simp)
apply simp
using bv_less_correct complement_bv_eq of_nat_less_iff
apply smt 
done

lemma bv_less_eq_int_correct[rule_format]: 
     "\<forall> b. length a = length b \<and> a~=[] \<longrightarrow> (bv_to_int a \<le> bv_to_int b) = (bv_less_eq_int a b)"
apply (rule allI)
apply (rule impI)
apply (simp add: bv_less_eq_int_def)
apply clarify
apply (subgoal_tac " bv_less_int a b = (bv_to_int a < bv_to_int b)")
  prefer 2  
  apply (simp add: bv_less_int_correct)   
apply (rotate_tac -1)
apply (erule ssubst)
apply (case_tac "(bv_to_int a < bv_to_int b)")
 apply simp
apply (case_tac "(bv_to_int a = bv_to_int b)")
 apply simp
 apply (simp add: bv_to_int_qinj)
apply auto
done

(* lemmata concerning bv_and/bv_or*)

lemma length_bv_and:
 "length (bv_and xs ys) = min (length xs) (length ys)"
by (simp add: bv_and_def)

lemma bv_and_nth:
 " n < length (bv_and xs ys) \<Longrightarrow>
  (bv_and xs ys) !n = (xs !n AND ys !n)"
by (simp add: bv_and_def)

lemma bv_and_append:
 "(bv_and (xs @ ys) zs) =
   bv_and xs (take (length xs) zs) @ bv_and ys (drop (length xs) zs)"
by (simp add: bv_and_def zip_append1)

lemma length_bv_or:
 "length (bv_or xs ys) = min (length xs) (length ys)"
by (simp add: bv_or_def)

lemma bv_or_nth:
" n < length (bv_or xs ys) \<Longrightarrow>
  (bv_or xs ys) !n  = (xs !n OR ys !n)"
by (simp add: bv_or_def)

lemma bv_or_append:
"(bv_or (xs @ ys) zs) =
  bv_or xs (take (length xs) zs) @ bv_or ys (drop (length xs) zs)"
by (simp add: bv_or_def zip_append1)


lemma length_nat_to_bv_upper_limit:
  assumes nk: "n \<le> 2 ^ k - 1"
  shows       "length (nat_to_bv n) \<le> k"
proof (cases "n = 0")
  case True
  thus ?thesis
    by (simp add: nat_to_bv_def nat_to_bv_helper.simps)
next
  case False
  hence n0: "0 < n" by simp
  show ?thesis
  proof (rule ccontr)
    assume "~ length (nat_to_bv n) \<le> k"
    hence "k < length (nat_to_bv n)" by simp
    hence "k \<le> length (nat_to_bv n) - 1" by arith
    hence "(2::nat) ^ k \<le> 2 ^ (length (nat_to_bv n) - 1)" by simp
    also have "... = 2 ^ (length (norm_unsigned (nat_to_bv n)) - 1)" by simp
    also have "... \<le> bv_to_nat (nat_to_bv n)"
      by (rule bv_to_nat_lower_limit) (simp add: n0)
    also have "... = n" by simp
    finally have "2 ^ k \<le> n" .
    with n0 have "2 ^ k - 1 < n" by arith
    with nk show False by simp
  qed
qed



lemmas length_nat_to_bv_upper_limit_impl_nat_limit_aux = 
       length_nat_to_bv_lower_limit (* legacy *)



end
