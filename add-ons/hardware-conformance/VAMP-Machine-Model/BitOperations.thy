(**
 * Copyright (c) 2003-2009 Kara Abdul-Qadar, Matthias Daum, Mark Hillebrand,
 * Dirk Leinenbach, Elena Petrova, Mareike Schmidt, Alexandra Tsyban,
 * Martin Wildmoser.
 * Some rights reserved, Saarland University and Technical University of
 * Munich.
 *
 * This work is licensed under the German-Jurisdiction Creative Commons
 * Attribution Non-commercial Share Alike 2.0 License.
 * See the file LIZENZ for a full copy of the license.
**)
(* $Id: BitOperations.thy 27414 2009-05-04 14:04:13Z MarkHillebrand $ *)
chapter {* Theory BitOperations: bit operations on the C0-level *}

theory BitOperations
imports MoreWord
begin

text {* This theory defines the typical bit operations (e.\,g.\ bitwise not,
 binary bitwise operators, and shifts) on natural numbers and integers as
 defined on the C0 level, along with a nice syntax. *}


(* ============================== *)
subsection {* Auxiliary functions *}
(* ============================== *)

text {* General framework for all \textbf{binary bitwise operations}. *}

definition s_bitop :: "(bit \<Rightarrow> bit \<Rightarrow> bit) \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int"
where
  "s_bitop f \<equiv> \<lambda>x y. let v=  int_to_bv x; w=int_to_bv y in
     bv_to_int (map (\<lambda> (a,b). f a b)
                    (zip (bv_extend (length w) (bv_msb v) v)
                         (bv_extend (length v) (bv_msb w) w)))"

definition   u_bitop :: "(bit \<Rightarrow> bit \<Rightarrow> bit) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat"
where
  "u_bitop f x y \<equiv>  let v= nat_to_bv x; w=nat_to_bv y in
     bv_to_nat (map (\<lambda> (a,b). f a b)
                    (zip (bv_extend (length w) (0::bit) v)
                         (bv_extend (length v) (0::bit) w)))"


(* ======================================= *)
subsection {* Declaration of the operators *}
(* ======================================= *)

text {* Certain operators take the data type's width as parameter.  It is
  explicitly stated with every operator whether this parameter has
  to be specified.  The width has always to be given in bits and is a
  @{typ nat} value.  For unary operators, it is generally the first, for
  binary parameters it is generally the second parameter. *}

text {* On unsigned integer types, the result of bitwise not depends on the
  width of the data type.  For symmetry, we supply the data type's width also
  for bitwise not on signed types. *}

text {* The following bitwise operations work on arbitrary integers resp.
 natural numbers.  Here, the width of the data type does not have to be
 known. *}

consts
  s_or  :: "int => int => int"		(infixl "sor"  40)
  u_or  :: "nat => nat => nat"		(infixl "uor"  40)
  s_xor :: "int => int => int"		(infixl "sxor" 42)
  u_xor :: "nat => nat => nat"		(infixl "uxor" 42)
  s_and :: "int => int => int"		(infixl "sand" 45)
  u_and :: "nat => nat => nat"		(infixl "uand" 45)


text {* Despite of the binary bitwise operations, the width of the data type
  must be known for the shift vectors.  Thus, we have 3 instead of 2 arguments:
    1. The number to be shifted
    2. The data type width
    3. The amount of bits to shift (must \textbf{always} be a nat) *}



(* The binding precedence is somewhat tricky, here.  The infixl notation lead
   to problems because of the third argument.  Thus, we use mixfix-
   declarations with a slightly higher priority of the last operand (ensuring
   a left-associative operator binding). -- Thanks to Norbert Schirmer! *)


(* Syntax *)
syntax
  s_not :: "nat => int => int"		("\<not>\<^bsub>s'/_\<^esub> _" [150, 100] 100)
  u_not :: "nat => nat => nat"		("\<not>\<^bsub>u'/_\<^esub> _" [150, 100] 100)
  s_or  :: "int => int => int"		(infixl "\<or>\<^sub>s" 40)
  u_or  :: "nat => nat => nat"		(infixl "\<or>\<^sub>u" 40)
  s_xor :: "int => int => int"		(infixl "\<oplus>\<^sub>s" 42)
  u_xor :: "nat => nat => nat"		(infixl "\<oplus>\<^sub>u" 42)
  s_and :: "int => int => int"		(infixl "\<and>\<^sub>s" 45)
  u_and :: "nat => nat => nat"		(infixl "\<and>\<^sub>u" 45)
  s_lsh :: "int => nat => nat => int"	("_ \<lless>\<^bsub>s'/_\<^esub> _" [60,60,61] 60)
  u_lsh :: "nat => nat => nat => nat"	("_ \<lless>\<^bsub>u'/_\<^esub> _" [60,60,61] 60)
  s_rsh :: "int => nat => nat => int"	("_ \<ggreater>\<^bsub>s'/_\<^esub> _" [60,60,61] 60)
  u_rsh :: "nat => nat => nat => nat"	("_ \<ggreater>\<^bsub>u'/_\<^esub> _" [60,60,61] 60)


text {* Note: In the previous syntax notation for bitwise not and for shifts,
  ' acts as a quotation character (hence, '/ will literally include a /).
  Thus with xsymbol support, the term @{text "s_not w x"} can be written as
  @{text "\<not>\<^bsub>s/w\<^esub> x"}, term @{text "x slsh 16 y"} as @{text "x \<lless>\<^bsub>s/16\<^esub> y"},
  and so on. *}


(* ====================================== *)
subsection {* Definition of the operators *}
(* ====================================== *)


definition 
 "s_not \<equiv> \<lambda>w x. bv_to_int (bv_not (int2bvn w x))"

definition
"u_not \<equiv> \<lambda>w x. bv_to_nat (bv_not (nat2bvn w x))"


translations (* BUG: explain *)
  "s_and" == "CONST s_bitop (op AND)"
  "u_and" == "CONST u_bitop (op AND)"
  "s_or"  == "CONST s_bitop (op OR)"
  "u_or"  == "CONST u_bitop (op OR)"
  "s_xor" == "CONST s_bitop (op XOR)"
  "u_xor" == "CONST u_bitop (op XOR)"

definition 
"s_lsh \<equiv> \<lambda>x w a. 
                           bv_to_int ((drop a (int2bvn w x)) @ replicate a 0)"
definition
"u_lsh \<equiv> \<lambda>x w a.
                           bv_to_nat ((drop a (nat2bvn w x)) @ replicate a 0)"

definition 
    "s_rsh x w a \<equiv> if a > 0 then int (bv_to_nat (take (w - a) (int2bvn w x)))
                            else x"

definition
    "u_rsh x w a \<equiv> bv_to_nat (take (length (nat_to_bv x) - a) (nat_to_bv x))"

(* ================== *)
subsection {* Lemmata *}
(* ================== *)

(* ------------------------------------------ *)
subsubsection {* Basic Properties *}
(* ------------------------------------------ *)


definition
  bv_mapzip :: "[bit => bit => bit,bit list, bit list] => bit list" where
  "bv_mapzip f w1 w2 =
    (let g = bv_extend (max (length w1) (length w2)) 0
     in map (case_prod f) (zip (g w1) (g w2)))"

lemma u_bitop_bv_mapzip:
  assumes v: "v = nat_to_bv x" and w: "w = nat_to_bv y"
  shows "u_bitop f x y = bv_to_nat (bv_mapzip f v w)"
proof -
  let ?max = "max (length v) (length w)"
  have
    "bv_extend (length w) 0 v = bv_extend ?max 0 v"
    "bv_extend (length v) 0 w = bv_extend ?max 0 w"
    by (simp split: split_max )+  (simp add: bv_extend_def)+
  thus ?thesis using v and w
  by (simp add: u_bitop_def bv_mapzip_def Let_def) 
qed

lemma u_bitop_commute:
 "(\<forall> u v. f u v = f v u) \<Longrightarrow> u_bitop f a b = u_bitop f b a"
proof -
  assume 1:"(\<forall> u v. f u v = f v u)"
  show ?thesis
  unfolding u_bitop_def
  using  1
  apply (subst map_zip_commute)
  unfolding length_bv_extend Let_def
  apply simp_all
  done
qed

lemma s_bitop_commute: 
     "(\<forall> u v. f u v = f v u) \<Longrightarrow> s_bitop f a b = s_bitop f b a"
proof -
  assume 1:"(\<forall> u v. f u v = f v u)"
  show ?thesis
  unfolding s_bitop_def
  using  1
  apply (subst map_zip_commute)
    unfolding length_bv_extend Let_def
  apply simp_all
  done
qed

lemma u_and_commute: "u_and a b = u_and b a"
proof -
  show ?thesis
  apply (subst u_bitop_commute)
    using bit_ops_comm(1) apply blast
  apply simp_all
  done
qed

lemma s_and_commute: "s_and a b = s_and b a"
apply (subst s_bitop_commute)
 apply (simp add: bitand_commute)
apply simp
done

lemma u_or_commute: "u_or a b = u_or b a"
apply (subst u_bitop_commute)
 apply (simp add: bitor_commute)
apply simp
done

lemma s_or_commute: "s_or a b = s_or b a"
apply (subst s_bitop_commute)
 apply (simp add: bitor_commute)
apply simp
done

lemma s_and_bv_less[rule_format]:"\<forall> v w. length v = length w
          \<longrightarrow> length v = l
          \<longrightarrow> (map (\<lambda>(x, y). x AND y) (zip v w)) \<noteq> w
          \<longrightarrow> bv_less (map (\<lambda>(x, y). x AND y) (zip v w), w)"
apply (induct_tac l)
 apply clarsimp
apply clarsimp
apply (case_tac w, simp)
apply clarsimp
apply (rename_tac w ws)
apply (case_tac v, simp)
apply clarsimp
done

lemma s_and_bv_le[rule_format]:"\<forall> v w. length v = length w
          \<longrightarrow> length v = l
          \<longrightarrow> bv_le (map (\<lambda>(x, y). x AND y) (zip v w)) w"
apply clarsimp
apply (simp add: bv_le_def)
apply clarsimp
apply (rule s_and_bv_less, simp+)
done

lemma bitand_bv_less_eq_int:
      "hd (bv_extend (length v) (bv_msb w) w) = 0
           \<longrightarrow> hd (bv_extend (length w) (bv_msb v) v) = 0
           \<longrightarrow> bv_less_eq_int (map (\<lambda>(x, y). x AND y) (zip (bv_extend (length w) (bv_msb v) v) 
                                                           (bv_extend (length v) (bv_msb w) w))) 
                                                       (bv_extend (length v) (bv_msb w) w)"
apply (simp add: bv_less_eq_int_def)
apply clarsimp
apply (simp add: bv_less_int_def)
apply (case_tac "bv_extend (length w) (bv_msb v) v = []")
 apply simp
 apply (subgoal_tac "bv_extend (length v) (bv_msb w) w = []")
  apply simp
 apply (case_tac "v")
  apply (case_tac "w", simp)
  apply clarsimp
  apply (simp add: bv_extend_def)
 apply clarsimp
 apply (case_tac "w", simp)
 apply (simp add: bv_extend_is_not_empty_1)
 apply clarsimp
 apply (simp add: bv_extend_def)
 apply clarsimp
 apply (subgoal_tac "tl (map (\<lambda>(x, y). x AND y) (zip (bv_extend (length w) (bv_msb v) v) 
                        (bv_extend (length v) (bv_msb w) w))) = 
                       (map (\<lambda>(x, y). x AND y) (zip (tl (bv_extend (length w) 
                       (bv_msb v) v)) (tl (bv_extend (length v) (bv_msb w) w))))")
  apply clarsimp
  apply (rule s_and_bv_less)
    apply (simp add: length_bv_extend)
   apply simp
  apply (frule not_eq_hd_tl)
    apply simp
    apply (simp add: length_bv_extend)
    apply arith
   apply simp+
 apply (simp add: map_tail[symmetric])
 apply (simp add: zip_tail)
done

(* ------------------------------------------ *)
subsubsection {* Lemmata regarding the length *}
(* ------------------------------------------ *)

text {* The following lemmata ensure that the result of the various bit
 operations will never exceed the maximal bit-width of the underlying data type
 *}


text {* \bf Auxiliary functions. *}
(* ----------------------------- *)

lemma length_nat2bvn[simp]: "length (nat2bvn w x) = w"
  apply (unfold nat2bvn_def)
  apply (simp add: Let_def bv_extend_def) 
done

lemma length_int2bvn[simp]: "length (int2bvn w x) = w"
  apply (unfold int2bvn_def)
  apply (simp add: Let_def bv_extend_def)
done

lemma bv_to_int_int2bvn[simp]:
    "length (int_to_bv x) \<le> w \<Longrightarrow> bv_to_int (int2bvn w x) = x"
unfolding int2bvn_def Let_def
apply simp
using bv_int_bv int_bv_int norm_signed_bv_extend_bv_msb
apply metis
done

text {* \bf Not operators. *}
(* ----------------------- *)

lemma norm_signed_length: "length (norm_signed w) \<le> length w"
  apply (cases w, simp_all)
  apply (subst norm_signed_Cons)
  apply (case_tac a, simp_all)
  apply (rule rem_initial_length)
  done

lemma length_int_to_bv_s_not:
  "length (int_to_bv x) \<le> w \<Longrightarrow> length (int_to_bv(\<not>\<^bsub>s/w\<^esub> x)) \<le> w"
  apply (simp add: s_not_def)
  apply (insert length_int2bvn[where w=w and x=x])
  apply (insert norm_signed_length[where w="bv_not (int2bvn w x)"])
  apply simp
done

lemma norm_unsigned_length [intro!]: 
      "length (norm_unsigned w) \<le> length w"
  by (rule rem_initial_length)

lemma length_nat_to_bv_u_not:
  "length (nat_to_bv x) \<le> w \<Longrightarrow> length (nat_to_bv(\<not>\<^bsub>u/w\<^esub> x)) \<le> w"
  apply (simp add: u_not_def)
  apply (insert length_nat2bvn[where w=w and x=x])
  apply (insert norm_unsigned_length[where w="bv_not (nat2bvn w x)"])
  apply (simp add: bv_to_nat_def)
  done 

text {* \bf Bitwise operations. *}
(* ---------------------------- *)

(* BUG: explain. *)

lemma length_int_to_bv_s_bitop_le_max:
  "length (int_to_bv(s_bitop f x y))
   \<le> max (length (int_to_bv x)) (length (int_to_bv y))"
  apply (simp add: s_bitop_def Let_def)
  apply (insert norm_signed_length[where
    w="map (case_prod f) 
           (zip (bv_extend (length (int_to_bv y)) (bv_msb (int_to_bv x))
                           (int_to_bv x))
                (bv_extend (length (int_to_bv x)) (bv_msb (int_to_bv y))
                           (int_to_bv y)))"])
  apply (simp only: max_def)
  apply (case_tac "length (int_to_bv x) \<le> length (int_to_bv y)")
  apply (simp add: bv_msb_def bv_extend_def)+
done

lemma length_int_to_bv_s_bitop:
  "\<lbrakk> length (int_to_bv x) \<le> w; length (int_to_bv y) \<le> w \<rbrakk>
   \<Longrightarrow> length (int_to_bv(s_bitop f x y)) \<le> w"
  apply (insert length_int_to_bv_s_bitop_le_max[of f x y])
  apply (simp add: max_def)
  apply (case_tac "length (int_to_bv x) \<le> length (int_to_bv y)")
  apply  simp+
done

lemma length_nat_to_bv_u_bitop_le_max:
  "length (nat_to_bv(u_bitop f x y))
   \<le> max (length (nat_to_bv x)) (length (nat_to_bv y))"
  apply (simp add: u_bitop_def Let_def)
  apply (insert norm_unsigned_length[where
    w="map (case_prod f) 
           (zip (bv_extend (length (nat_to_bv y)) 0 (nat_to_bv x))
                (bv_extend (length (nat_to_bv x)) 0 (nat_to_bv y)))"])
  apply (simp only: max_def)
  apply (case_tac "length (nat_to_bv x) \<le> length (nat_to_bv y)")
  apply (simp add: bv_msb_def bv_extend_def)+
done

lemma length_nat_to_bv_u_bitop:
  "\<lbrakk> length (nat_to_bv x) \<le> w; length (nat_to_bv y) \<le> w \<rbrakk>
   \<Longrightarrow> length (nat_to_bv(u_bitop f x y)) \<le> w"
  apply (insert length_nat_to_bv_u_bitop_le_max[of f x y])
  apply (simp add: max_def)
  apply (case_tac "length (nat_to_bv x) \<le> length (nat_to_bv y)")
  apply  simp+
done

text {* \bf Shift operations. *}
(* -------------------------- *)

lemma length_int_to_bv_s_lsh:
  "length (int_to_bv(x \<lless>\<^bsub>s/w\<^esub> a)) \<le> w"
  apply (simp add: s_lsh_def)
  apply (case_tac "a<w")
  apply  (insert norm_signed_length[where
                        w="drop a (int2bvn w x) @ replicate a 0"])
  apply  simp+
  apply (simp add: norm_signed_replicate_Zero)
done

lemma length_nat_to_bv_u_lsh:
  "length (nat_to_bv(x \<lless>\<^bsub>u/w\<^esub> a)) \<le> w"
  apply (simp add: u_lsh_def)
  apply (case_tac "a<w")
  apply  (insert norm_unsigned_length[where
                        w="drop a (nat2bvn w x) @ replicate a 0"])
  apply  simp+
  apply (simp add: norm_unsigned_replicate_Zero)
done

lemma length_int_to_bv_s_rsh:
  "length (int_to_bv x) \<le> w \<Longrightarrow> length (int_to_bv(x \<ggreater>\<^bsub>s/w\<^esub> a)) \<le> w"
  apply (simp add: s_rsh_def)
  apply (rule impI)
  apply (case_tac "w=0")
  apply  simp+
  apply (insert norm_signed_length[where w="0 # norm_unsigned (take (w - a) (int2bvn w x))"])
  apply simp
  apply (subgoal_tac
    "Suc (length (norm_unsigned (take (w - a) (int2bvn w x)))) \<le> w")
  apply  simp
  apply (insert norm_unsigned_length[where w="take (w - a) (int2bvn w x)"])
  apply simp
  done

lemma length_nat_to_bv_u_rsh:
  "length (nat_to_bv x) \<le> w \<Longrightarrow> length (nat_to_bv(x \<ggreater>\<^bsub>u/w\<^esub> a)) \<le> w"
 apply (simp add: u_rsh_def)
 apply (insert norm_unsigned_length
               [where w="take (length (nat_to_bv x) - a) (nat_to_bv x)"])
 apply simp
done
 

(* -------------------------------- *)
subsubsection {* Special properties *}
(* -------------------------------- *)

text {* This section includes simplification rules for special constants and
 similar properties. *}

lemma s_not_0: "0 < w \<Longrightarrow> s_not w 0 = -1"
  apply (unfold s_not_def)
  apply (unfold  int2bvn_def)
  apply (simp add: Let_def bv_extend_def bv_msb_def int_to_bv_def nat_to_bv_def)
  apply (rule bv_to_int_replicate_One, simp)
done

lemma u_and_zero: "u_and a 0 = 0"
apply (subst u_and_commute)
apply (simp add: u_bitop_def)
apply (simp add: bv_extend_def Let_def nat_to_bv_def)
apply (subst and_zero)
apply (simp add: bv_to_nat_replicate_Zero)
done


text {* \bf Shifting by a very large amount. *}
(* ----------------------------------------- *)

lemma u_lsh_by_ge_width_eq_0: "a \<ge> w ==> u_lsh  x  w a = 0"
  unfolding u_lsh_def
  by (simp add: bv_to_nat_replicate_Zero)

lemma s_lsh_by_ge_width_eq_0: "a \<ge> w ==> s_lsh  x  w a = 0"
  unfolding s_lsh_def
  by (simp, rule bv_to_int_replicate_Zero)

lemma u_rsh_by_ge_length_eq_0: "a \<ge> length (nat_to_bv x) ==>  u_rsh x w a = 0"
  unfolding u_rsh_def
  by simp

text {* \bf Shifting by 0. *}
(* ----------------------- *)

lemma length_impl_s_lsh_by_0:
  "length (int_to_bv x) \<le> w ==> s_lsh x w 0 = x"
by (simp add:s_lsh_def)

lemma range_impl_s_lsh_by_0:
  "[| 0<w ; -(2^(w - 1)) \<le> x ; x < 2^(w - 1) |] ==>s_lsh  x  w 0 = x"
apply (subgoal_tac "length (int_to_bv x) \<le> w")
apply  (simp only: length_impl_s_lsh_by_0)
apply (simp add: length_bounded_int_to_bv)
done


text {* \bf Shifting of 0. *}
(* ----------------------- *)

lemma s_rsh_0_eq_0[simp]: "0 \<ggreater>\<^bsub>s/w\<^esub> a = 0"
   apply (simp add: s_rsh_def)
  apply (induct a)
  apply  simp
  apply (simp add: int2bvn_def del: replicate_Suc)
  apply (unfold bv_extend_def Let_def)
  apply (simp add: bv_to_nat_replicate_Zero bv_to_nat_def nat_to_bv_def bv_msb_def)
  using bv_to_nat_def bv_to_nat_replicate_Zero
  apply auto
  done

lemma u_rsh_0_eq_0[simp]: "0 \<ggreater>\<^bsub>u/w\<^esub> a = 0"
  unfolding   u_rsh_def bv_to_nat_def nat_to_bv_def
  by simp

lemma s_lsh_0_eq_0[simp]: "0 \<lless>\<^bsub>s/w\<^esub> a = 0"
  apply (simp add: s_lsh_def)
  apply (simp add: int2bvn_def Let_def bv_extend_def nat_to_bv_def 
                   bv_msb_def bv_to_nat_def)
  apply (simp only: bv_to_nat_def replicate_add[of "w-a" a "0", THEN sym]
             split:bit.split)
  apply (rule bv_to_int_replicate_Zero)
done

lemma u_lsh_0_eq_0: "0 \<lless>\<^bsub>u/w\<^esub> a = 0"
   apply (simp add: u_lsh_def nat2bvn_def Let_def bv_extend_def
                    bv_to_nat_def nat_to_bv_def)
   using bv_to_nat_def bv_to_nat_replicate_Zero 
   apply auto
done


text {* \bf Bitwise OR. *}
(* -------------------- *)

text {* (Auxiliary lemma for the next lemma.) *}

lemma u_or_0_aux: "map (case_prod op OR) (zip (bv_extend (length v) 0 []) v) = v"
  apply (induct v)
  apply  simp
  apply (simp add: bv_extend_def)
done

lemma u_or_0[simp]: "(0 \<or>\<^sub>u x) = x"
  apply ( simp add: u_bitop_def Let_def)
  apply (subst (2) nat_to_bv_def) 
  apply (subst (2) nat_to_bv_def) 
  apply (subst (2) bv_extend_def) 
  apply (simp add: u_or_0_aux[where v = "nat_to_bv x"])
  done

lemma s_or_0: "(0 \<or>\<^sub>s x) = x"
  apply (simp add: s_bitop_def Let_def )
  apply (subst (2) nat_to_bv_def) 
  apply (subst (2) nat_to_bv_def) 
  apply (subst (2) bv_extend_def) 
  apply (simp add: bv_to_nat_def bv_msb_def u_or_0_aux[where v = "int_to_bv x"])
done

lemma s_or_0_2: "(x \<or>\<^sub>s 0) = x"
  apply (insert s_bitop_commute[where f="op OR"])
  apply (simp add: bitor_commute)
  apply (simp add: s_or_0)
done


(* ------------------------------------- *)
subsubsection {* Arithmetic equivalences *}
(* ------------------------------------- *)

text {* \bf Not operators. *}
(* ----------------------- *)

lemma "(\<not>\<^bsub>s/w\<^esub> x) = -x - 1"

oops (* BUG: prove it *)


text {* \bf Shift operations. *}
(* -------------------------- *)

text {* For lemma @{text u_rsh_is_div_power2}, we need some auxiliary lemmata.
 The term @{term "foldl (\<lambda>s b. 2*s + bitval b) s"} is motivated through
 @{thm bv_to_nat_def}.  However, we need the property for arbitrary s and
 thus, cannot use @{term bv_to_nat} directly. *}

lemma u_rsh_is_div_power2_aux2[rule_format]:
    "!!s. s = foldl (\<lambda>s b. 2*s + bitval b) s v div 2 ^ length v"
 apply (induct v)
  apply  simp+
  apply (subgoal_tac "(2::nat) * 2 ^ length v = 2 ^ length v * 2")
  apply  (simp (no_asm_simp))
  apply  (simp add: div_mult2_eq)
  apply  (subgoal_tac "bitval a<2")
  apply   arith
  apply  (case_tac a)
  apply   simp+
done

lemma u_rsh_is_div_power2_aux[rule_format]: "! s. length v \<ge> i \<longrightarrow>
                       foldl (\<lambda>s b. 2*s + bitval b) s (take (length v - i) v)
                     = foldl (\<lambda>s b. 2*s + bitval b) s v  div  2 ^ i"
  apply (induct v)
  apply  simp+
  apply (case_tac "length v \<ge> i")
  apply  (simp add: Suc_diff_le)
  apply clarsimp
  apply (case_tac "i=Suc (length v)")
  apply  auto
  apply (subgoal_tac
           "s = foldl (\<lambda>s b. 2*s + bitval b) s (a#v) div 2 ^ length (a#v)")
  apply  simp
  apply (rule u_rsh_is_div_power2_aux2)
done

lemma bv_to_nat_droplast:
   "bv_to_nat (take (length v - a) v) = bv_to_nat v div 2 ^ a"
 apply (cases " length v \<le> a")
 apply simp
 apply (frule bv_to_nat_less_power)
 apply (simp add: div_pos_pos_trivial bv_to_nat_def)
 apply (simp add: bv_to_nat_def)
 apply (subgoal_tac "(a \<le> (length v))")
 apply (frule_tac i = "a" and s = "0" in u_rsh_is_div_power2_aux)
 apply (simp add: int_div int_power)
 apply simp
done

lemma u_rsh_is_div_power2: "x \<ggreater>\<^bsub>u/w\<^esub> a = x div 2^a"
  apply (simp add: u_rsh_def)
  apply (case_tac "a \<ge> length(nat_to_bv x)")
  apply  simp
  apply  (frule length_nat_to_bv_upper_limit_impl_nat_limit[where k=a])
  apply  simp
  apply (insert u_rsh_is_div_power2_aux[where s=0 and v="nat_to_bv x" and i=a])
  apply simp
  apply (insert bv_to_nat_def)
  apply simp
done   

lemma s_rsh_pos_eq_div:
    "\<lbrakk> length(int_to_bv x) \<le> w; x\<ge>0 \<rbrakk> \<Longrightarrow> x \<ggreater>\<^bsub>s/w\<^esub> a = x div 2^a"
apply (simp add: s_rsh_def del: int_to_bv_ge0)
 apply (rule impI)
 apply (simp add:  int2bvn_def Let_def del: int_to_bv_ge0)
 apply (simp (no_asm_simp))
 apply (simp add: int_to_bv_ge0[of "x", THEN sym] del: int_to_bv_ge0)
 apply (insert bv_to_nat_droplast[where v="bv_extend w 0 (int_to_bv x)" and a=a])
 apply (simp add: bv_msb_def bv_extend_def min_def 
             split: if_split_asm del: int_to_bv_ge0)
 apply (subst (asm) (1)  HOL.eq_commute)
 apply (simp only: bv_to_nat_int_to_bv_pos)
apply (simp add: int_div int_power)
apply (smt Divides.transfer_int_nat_functions(1) bv_nat_bv bv_to_nat0 bv_to_nat_replicate_Zero bv_to_nat_replicate_Zero_append div_nonpos_pos_le0 i_div_ge_0 int_nat_eq int_nat_two_exp norm_signed_Zero_nat_to_bv semiring_1_class.of_nat_0 zero_less_nat_eq zero_less_power)
apply (subst (asm) (1)  HOL.eq_commute)
 apply (simp only: bv_to_nat_int_to_bv_pos)
apply (simp add: int_div int_power)
apply (metis Divides.transfer_int_nat_functions(1) bv_nat_bv bv_to_nat0 bv_to_nat_replicate_Zero_append int_nat_eq int_nat_two_exp norm_signed0 norm_signed_zero_nat_to_bv)
done

lemma s_rsh_neg_eq_div: "\<lbrakk> length(int_to_bv x) \<le> w; a>0; x<0 \<rbrakk>
    \<Longrightarrow> x \<ggreater>\<^bsub>s/w\<^esub> a = (2^w + x )div 2^a"
  apply (simp add: s_rsh_def del: int_to_bv_lt0)
   apply (simp add: int2bvn_def Let_def del: int_to_bv_lt0)
   apply (simp (no_asm_simp))
   apply (subgoal_tac "norm_signed (1 # bv_not (nat_to_bv  (nat ((- x) - (1::int))))) = 
                       int_to_bv x")
   prefer 2
   apply  simp
   apply (simp only:)
   apply (insert bv_to_nat_droplast[of "bv_extend w 1 (int_to_bv x)" a])
   apply (subst (asm) (2) int_to_bv_def)
   apply (simp only: split: if_split_asm)
   apply (metis Divides.transfer_int_nat_functions(1) bv_msb_def 
                bv_to_nat_extend_int_to_bv_neg diff_is_0_eq' 
                drop_0 int2bvn_def int_nat_two_exp int_to_bv_def 
                length_int2bvn list.sel(1) list.simps(3) 
                norm_signed_One_bv_not_nat_to_bv)
done

text {* The naming convention @{text "\<dots>_adef"} stands for ``arithmetic
  definition'' -- you can use these lemmata just as if they were the actual
  definitions.
*} 

lemma u_lsh_adef: "x \<lless>\<^bsub>u/w\<^esub> a = (x * 2^a) mod 2^w"
apply (simp add: u_lsh_def nat2bvn_def Let_def)
apply (case_tac "w=0")
 apply  (simp add: bv_to_nat_replicate_Zero)
apply  (simp add: bv_to_nat_dist_append)
apply  (simp add: bv_to_nat_replicate_Zero)
apply (case_tac "length (nat_to_bv x) < w")
 apply (simp add: bv_extend_def Let_def)
 apply  (simp add: bv_to_nat_dist_append)
 apply (case_tac "a+ length (nat_to_bv x) < w")
  apply simp
  apply (case_tac "x*2^a < 2^w")
   apply (simp add: mod_less)
   using bv_extend_norm_unsigned le_numeral_extra(3) list.size(3) nat_to_bv_of_neg_is_Nil 
   apply force
  apply (case_tac "(2::nat)^(length (nat_to_bv x)+a)<2^w")
   apply (simp add: power_add)
   apply (case_tac "x<2^length(nat_to_bv x)")
    apply (insert mult_less_mult[of "x" "2^length(nat_to_bv x)" "2^a" "2^w"] )
    apply (simp add: bv_extend_def)
   apply (insert bv_to_nat_upper_range[of "nat_to_bv x"])
   apply simp
  apply (simp add: bv_extend_def) 
 apply (insert drop_is_mod3[of "nat_to_bv x" "w" "a"])
 apply simp
apply (insert drop_is_mod4[of "nat_to_bv x" "w" "a"])
apply (simp add:)
apply auto
using power_add_2 
apply auto[1]
apply (simp add: bv_to_nat_replicate_Zero_append mult_bv_to_nat_is_bv_to_nat_append)
apply (simp add: mult_bv_to_nat_is_bv_to_nat_append)
using One_nat_def lessI mult.commute numeral_2_eq_2 power_add power_strict_increasing_iff
apply metis
apply (smt Nat.diff_diff_right add.commute bv_nat_bv bv_to_nat_replicate_Zero_append diff_add_inverse2 diff_is_0_eq' drop_is_mod3 less_imp_le_nat mult_bv_to_nat_is_bv_to_nat_append not_less)
using bv_nat_bv bv_to_nat_replicate_Zero_append mult_bv_to_nat_is_bv_to_nat_append
apply metis 
using bv_nat_bv bv_to_nat_replicate_Zero_append mult_bv_to_nat_is_bv_to_nat_append
apply metis
using bv_nat_bv bv_to_nat_replicate_Zero_append mult_bv_to_nat_is_bv_to_nat_append
apply metis
using bv_nat_bv bv_to_nat_replicate_Zero_append mult_bv_to_nat_is_bv_to_nat_append
apply metis
using Nat.add_diff_assoc Nat.diff_diff_right bv_to_nat_replicate_Zero_append diff_is_0_eq' 
      diff_zero less_imp_le_nat mult_bv_to_nat_is_bv_to_nat_append not_less
apply (smt )
done
 
text {* We need a division algorithm with truncation toward zero.  The builtin
  algorithm does always round down.  Hence, we adjust it here if the dividend
  is negative.  A more general approach would be to define the according
  operations @{text divide} and @{text modulo}.  Then we could write
  @{text "x \<lless>\<^bsub>s/w\<^esub> a = (x * 2^a) modulo 2^w"}.
*}
lemma s_lsh_adef: "x \<lless>\<^bsub>s/w\<^esub> a = (if x<0 then -((-x * 2^a) mod 2^w) 
                                       else (x * 2^a) mod 2^w)"
oops (* BUG: prove it *)

lemma bitwise_op_zip_zero_norm_unsigned_eq[rule_format]: 
      "f 0 0 = 0  \<longrightarrow> 
       norm_unsigned (map (\<lambda>(x, y). f x y) (zip (replicate n 0 @ a) (replicate n 0 @ b))) = 
       norm_unsigned (map (\<lambda>(x, y). f x y) (zip a b))"
apply (induct_tac n)
 apply simp
apply clarsimp
done

text {* Unsigned bitwise operators can be split using mod/div *}

lemma u_bitop_split_aux1[rule_format]: 
      "f 0 0 = 0 \<longrightarrow> 
       norm_unsigned (map (\<lambda>(x, y). f x y) 
                     (zip (bv_extend (length b) 0 a) (bv_extend (length a) 0 b))) = 
       norm_unsigned (map (\<lambda>(x, y). f x y) (zip (bv_extend (length (norm_unsigned b)) 0 
                    (norm_unsigned a)) (bv_extend (length (norm_unsigned a)) 0 (norm_unsigned b))))"
apply clarsimp
apply (subgoal_tac "(bv_extend (length b) 0 a) = 
                    (bv_extend (length b) 0 (bv_extend (length a) 0 (norm_unsigned a)))")
 apply clarsimp
 apply (simp add: bv_extend_bv_extend)
 apply (subgoal_tac "(bv_extend (length a) 0 b) = 
                     (bv_extend (length a) 0 (bv_extend (length b) 0 (norm_unsigned b)))")
  apply clarsimp
  apply (simp add: bv_extend_bv_extend)
  apply (subst bv_extend_max[symmetric, where l="length (norm_unsigned b)" and 
                                              a="norm_unsigned a"])
  apply (subst bv_extend_max[symmetric, where l="length (norm_unsigned a)" and 
                                              a="norm_unsigned b"])
  apply (simp add: nat_max_commute)
  apply (case_tac "max (length (norm_unsigned a)) (length (norm_unsigned b)) \<le> 
                   max (length a) (length b)")
   apply (subst bv_extend_bv_extend2[where v="norm_unsigned a" and 
                                           l="max (length (norm_unsigned a)) 
                                                  (length (norm_unsigned b))"], simp)
   apply (subst bv_extend_bv_extend2[where v="norm_unsigned b" and 
                                           l="max (length (norm_unsigned a)) 
                                                  (length (norm_unsigned b))"], simp)
   apply clarsimp
   apply (subgoal_tac 
          "zip (bv_extend (max (length a) (length b)) 0 
               (bv_extend (max (length (norm_unsigned a)) (length (norm_unsigned b))) 0 (norm_unsigned a)))
            (bv_extend (max (length a) (length b)) 0
            (bv_extend (max (length (norm_unsigned a)) (length (norm_unsigned b))) 0
            (norm_unsigned b))) = 
           zip (replicate (max (length a) (length b) - 
               max (length (norm_unsigned a)) (length (norm_unsigned b))) 0 @ 
               (bv_extend (max (length (norm_unsigned a)) (length (norm_unsigned b))) 0 (norm_unsigned a)))
            (replicate (max (length a) (length b) - max (length (norm_unsigned a)) 
            (length (norm_unsigned b))) 0 @ (bv_extend (max (length (norm_unsigned a)) 
            (length (norm_unsigned b))) 0 (norm_unsigned b)))")
    apply simp
    using norm_unsigned_replicate_Zero_append 
    apply blast
    apply (simp add: bitwise_op_zip_zero_norm_unsigned_eq)
   apply (simp add: bv_extend_def)
   apply (simp add: max_def)
   apply (smt BitOperations.norm_unsigned_length dual_order.trans le_SucI not_less_eq_eq)
  apply (simp add: max_def)
   apply (insert length_norm_unsigned_le[where w="a"])
   apply (insert length_norm_unsigned_le[where w="b"])
   apply clarsimp
   apply (simp add: bv_extend_norm_unsigned)+
done
 
lemma u_bitop_split_aux2[rule_format]:
      "f 0 0 = 0\<longrightarrow> 
       norm_unsigned (map (\<lambda>(x, y). f x y) 
                      (zip (drop (max (length a) (length b) - n) (bv_extend (length b) 0 a))
                      (drop (max (length a) (length b) - n) (bv_extend (length a) 0 b)))) = 
       norm_unsigned (map (\<lambda>(x, y). f x y) 
                     (zip (bv_extend (length (norm_unsigned (drop (length b - n) b))) 0 
                     (norm_unsigned (drop (length a - n) a)))
                     (bv_extend (length (norm_unsigned (drop (length a - n) a))) 0 
                     (norm_unsigned (drop (length b - n) b)))))"
apply clarsimp
apply (case_tac "max (length a) (length b) \<le> n")
 apply clarsimp
 apply (simp add: u_bitop_split_aux1[symmetric])
apply clarsimp
apply (simp add:  u_bitop_split_aux1[symmetric])
apply (case_tac "length a \<le> n")
 apply clarsimp
 apply (simp add: bv_extend_def max_def)
 apply (case_tac "length a = n")
  (*apply clarsimp
  apply (simp add: bv_extend_def)
  apply (smt append_Nil bv_extend_def diff_diff_cancel diff_self_eq_0 length_drop nat_le_linear replicate_empty u_bitop_split_aux1)
  apply (smt append_self_conv2 bv_extend_def diff_diff_cancel diff_is_0_eq length_drop nat_le_linear replicate_empty u_bitop_split_aux1)
*)
apply clarsimp
apply (simp add: max_def)
apply (rule conjI) 
 apply clarsimp
 apply(simp only:  drop_bv_extend_less)
 apply (simp add: min_def bv_extend_def)
apply clarsimp
apply (case_tac "n < length b")
 apply clarsimp
 apply (subst drop_bv_extend_less, simp)
 apply (simp add: min_def)
 apply (subgoal_tac "Suc (length b) - n = Suc (length b - n)")
  apply (simp add: bv_extend_def)
 apply arith
apply clarsimp
apply (case_tac "length b = n")
 apply clarsimp
 apply (simp_all add: bv_extend_def)
done                     

lemma u_bitop_split[rule_format]: 
"f 0 0 = 0 \<longrightarrow> u_bitop f a b = (u_bitop f (a div 2^n) (b div 2^n)) * 2^n + u_bitop f (a mod 2^n) (b mod 2^n) "
apply clarsimp
apply (simp add: u_bitop_def)
apply (simp add: Let_def)
apply (subst bv_to_nat_bv_chop_append[where n="n"])
apply (simp add: nat_to_bv_div_fst_bv_chop)
apply (simp add: nat_to_bv_mod_snd_bv_chop)
apply (simp add: bv_chop_def)
apply (simp add: length_bv_extend)
apply (simp add: take_map)
apply (simp add: drop_map)
apply (simp add: take_zip)
apply (simp add: drop_zip)
apply (subst nat_max_commute[where a="length (nat_to_bv b)" and b="length (nat_to_bv a)"])+
apply simp
apply (simp add: Let_def)

apply (simp add: take_bv_extend)
apply (subst nat_max_commute)
apply (simp add: take_bv_extend)

apply (rule bv_to_nat_norm_unsigned_eq)
apply (simp add: u_bitop_split_aux2)
done

text {* Arithmetic meaning of bitwise operation with some special values *}

lemma u_and_power2_minus1[rule_format]: 
    "0 < n \<longrightarrow> u_and a (2^n - Suc 0) = a mod 2^n"
apply (subst u_bitop_split[where n="n"], simp)
apply clarsimp
apply (simp add: u_and_zero)
apply (subst u_and_commute)
apply (simp add: u_bitop_def)
apply (simp add: nat_to_bv_power2_minus1)
apply (subgoal_tac "length (nat_to_bv (a mod 2^n)) \<le> n")
 apply (simp add: bv_extend_def)
 apply (insert and_one[where v= "replicate (n - length (nat_to_bv (a mod 2 ^ n)))
                                            0 @ nat_to_bv (a mod 2 ^ n)"])
 apply clarsimp
 apply (simp add: bv_to_nat_replicate_Zero_append)
apply clarsimp
apply (subgoal_tac "0 < (2::nat)^n")
 apply (frule_tac m="a" and n="2^n" in mod_less_divisor)
 using nat_upper_limit_impl_length_nat_to_bv_limit 
 apply blast
 apply arith
done

lemma u_and_power2: "u_and a (2^n) = (a mod 2^(Suc n)) div 2^n * 2^n"
apply (subst u_bitop_split[where n="Suc n"], simp)
apply simp
apply (simp add: u_and_zero)
apply (subst u_and_commute)
apply (simp add: u_bitop_def Let_def)
apply (simp add: nat_to_bv_power2)
apply (rule bv_to_nat_and_one_replicate_zero_nat_to_bv)
apply (cut_tac m="a" and n="2 * 2^n" in mod_less_divisor)
 apply simp
using nat_upper_limit_impl_length_nat_to_bv_limit 
apply auto
done

(* -------------------- *)
subsubsection {* Limits *}
(* -------------------- *)


text {* \bf Not operators. *}
(* ----------------------- *)

lemma le_exp_le: 
      "\<lbrakk>0 < (m::nat); n \<le> m\<rbrakk> \<Longrightarrow> ((2::int) ^ (n - 1)) \<le> (2 ^ (m - 1))"
  by simp

lemma bounded_s_bitop: 
  assumes lb: "lb = - ub"
  assumes ub: "ub = 2^(w - 1)"
  assumes w: "0 < w"
  assumes i1_bounded: "lb \<le> i1" "i1 < ub"
  assumes i2_bounded: "lb \<le> i2" "i2 < ub"
  shows "lb \<le> (s_bitop f i1 i2) \<and> (s_bitop f i1 i2) < ub"
proof -
  from length_bounded_int_to_bv [OF lb ub w i1_bounded]
  have i1_w: "length (int_to_bv i1) \<le> w".
  from length_bounded_int_to_bv [OF lb ub w i2_bounded]
  have i2_w: "length (int_to_bv i2) \<le> w".  
  let ?w="(map (\<lambda>(x, y). f x y)
            (zip (bv_extend (length (int_to_bv i2)) (bv_msb (int_to_bv i1))
                   (int_to_bv i1))
              (bv_extend (length (int_to_bv i1)) (bv_msb (int_to_bv i2))
                (int_to_bv i2))))"
  from norm_signed_length [where w="?w"]
  have length_le: "length ?w \<le> w"
    apply simp
    apply (simp only: min_def )
    apply (case_tac "length (int_to_bv i1) \<le> length (int_to_bv i2)")
    apply  (simp_all add: i2_w bv_msb_def bv_extend_def)
    apply (simp_all add: i1_w)
    done
  from le_exp_le [OF w length_le]
  have exp_le: "((2::int) ^ (length ?w - 1)) \<le> (2 ^ (w - 1))".
  hence "- (2 ^ (w - 1)) \<le> - ((2::int) ^ (length ?w - 1))"
    by simp
  also
  from bv_to_int_lower_range [of ?w]
  have "- (2 ^ (length ?w - 1)) \<le> s_bitop f i1 i2"
    by (simp add: s_bitop_def Let_def)
  finally have lower_b: "lb  \<le> s_bitop f i1 i2"
    by (simp add: lb ub)
  from bv_to_int_upper_range [of ?w]
  have "s_bitop f i1 i2 < (2 ^ (length ?w - 1))"
    by (simp add: s_bitop_def Let_def)
  also note exp_le
  finally have "s_bitop f i1 i2 < ub"
    by (simp add: ub)
  with lower_b show ?thesis by simp
qed

lemma bounded_u_bitop: 
  assumes ub: "ub = 2^w"
  assumes w: "0 < w"
  assumes n1_bounded: "n1 < ub"
  assumes n2_bounded: "n2 < ub"
  shows "(u_bitop f n1 n2) < ub"
proof -
  from ub n1_bounded
  have n1_w: "length (nat_to_bv n1) \<le> w"
    by (simp add: nat_upper_limit_impl_length_nat_to_bv_limit)
  from ub n2_bounded
  have n2_w: "length (nat_to_bv n2) \<le> w"
    by (simp add: nat_upper_limit_impl_length_nat_to_bv_limit)
  let ?w="(map (\<lambda>(x, y). f x y)
           (zip (bv_extend (length (nat_to_bv n2)) 0 (nat_to_bv n1))
           (bv_extend (length (nat_to_bv n1)) 0 (nat_to_bv n2))))"
  from bv_to_nat_upper_range [of ?w]
  have "u_bitop f n1 n2 < 2 ^ length ?w"
    by (simp add: u_bitop_def Let_def)
  also
  from norm_unsigned_length [where w="?w"]
  have length_le: "length ?w \<le> w"
    apply simp
    apply (simp only: min_def )
    apply (case_tac "length (nat_to_bv n1) \<le> length (nat_to_bv n2)")
    apply  (simp_all add: n2_w bv_msb_def bv_extend_def)
    apply (simp_all add: n1_w) 
    done
  then
  have exp_le: "((2::nat) ^ (length ?w)) \<le> (2 ^ w)"
    by simp
  finally show ?thesis
    by (simp add: ub)
qed


text {* \bf Left-shift operations. *}
(* ------------------------------- *)

text {* lower limit for @{term u_lsh} is trivial: @{term "0 \<le> x ulsh w a" } *}

lemma u_lsh_upper_limit: "u_lsh x  w a < 2^w"
  apply (case_tac "w < a")
  apply  (simp add: u_lsh_by_ge_width_eq_0)
  apply (unfold u_lsh_def)
  apply (subgoal_tac "EX v. drop a (nat2bvn w x) @ replicate a 0 = v")
  prefer 2
  apply  simp
  apply (erule exE)
  apply simp
  apply (subgoal_tac "w = length v")
  prefer 2
  apply  clarsimp
  apply simp
  apply (subgoal_tac "(0::int) < 2 ^ length v")
  prefer 2
  apply (simp_all add: bv_to_nat_upper_range)
done

lemma s_lsh_lower_limit: "- (2 ^ (w - 1)) \<le> s_lsh x  w a"
  apply (case_tac "w < a")
  apply  (simp add: s_lsh_by_ge_width_eq_0)
  apply  (subgoal_tac "(0::int) < 2^(w - Suc 0)")
  apply   simp
  apply (unfold s_lsh_def)
  apply (subgoal_tac "ALL v. - (2 ^ (length v - 1)) \<le> bv_to_int v")
  prefer 2
  apply  (rule allI)
  apply  (rule bv_to_int_lower_range)
  apply (erule_tac x="drop a (int2bvn w x) @ replicate a 0" in allE)
  apply clarsimp
  apply simp
done

lemma s_lsh_upper_limit: "s_lsh x w a < 2^(w - 1)"
  apply (case_tac "w < a")
  apply  (simp add: s_lsh_by_ge_width_eq_0)
  apply (unfold s_lsh_def)
  apply (subgoal_tac "ALL v. bv_to_int v < 2 ^ (length v - 1)")
  prefer 2
  apply  (rule allI)
  apply  (rule bv_to_int_upper_range)
  apply (erule_tac x="drop a (int2bvn w x) @ replicate a 0" in allE)
  apply clarsimp
done

lemma s_lsh_arith_aux[rule_format]:
      "bw \<noteq> 0 \<longrightarrow> (-(2^(bw - 1))) \<le> x \<and> x < (2^(bw - 1)) \<longrightarrow>s_lsh x bw (Suc n) = 
       (((s_lsh x bw n)* 2) smod bw)"
apply clarsimp
apply (case_tac "bw < n")
apply (simp add: s_lsh_by_ge_width_eq_0)
apply (case_tac "bw = n")
apply (simp add: s_lsh_by_ge_width_eq_0)
apply (subgoal_tac "n < bw")
apply simp_all
apply (insert  s_lsh_lower_limit [of "bw" "x" "(Suc n)"])
apply (insert  s_lsh_upper_limit [of "x" "bw" "(Suc n)" ])
apply (subgoal_tac "bw \<noteq> 0")
apply (frule_tac bw = "bw" and x = "(x \<lless>\<^bsub>s/bw\<^esub> (Suc n))" in smod_equality)
apply simp
apply (subgoal_tac "(x \<lless>\<^bsub>s/bw\<^esub> (Suc n)) = ((x \<lless>\<^bsub>s/bw\<^esub> (Suc n)) smod bw)")
apply (thin_tac "(((x \<lless>\<^bsub>s/bw\<^esub> (Suc n)) smod bw) = (x \<lless>\<^bsub>s/bw\<^esub> (Suc n)))")
apply simp_all
apply (erule ssubst)
apply (simp add: s_lsh_def)
apply (case_tac "(drop n (int2bvn bw x)) =  []")
apply (subgoal_tac "(drop n (int2bvn bw x)) =  [] \<longrightarrow> (drop (Suc n) (int2bvn bw x)) = []")
apply simp
defer 1 
apply (case_tac "(drop (Suc n) (int2bvn bw x)) \<noteq> []")
apply (simp add: bv_to_int_append)
apply (simp add: bv_to_nat_replicate_Zero)
apply (subgoal_tac "(drop 1 (drop n (int2bvn bw x))) \<noteq> []")
prefer 2
apply simp
apply (frule_tac bv = "(drop n (int2bvn bw x))" in drop_1_eq_smod_length)
apply simp
apply (insert smod_zmult_zmult1 [of "(Suc n)" "(bv_to_int (drop n (int2bvn bw x)))" "bw - (Suc n)"])
apply simp 
apply (subgoal_tac "((((2::int) * ((2::int) ^ n)) * ((bv_to_int (drop n (int2bvn bw x))) smod 
                     (bw - (Suc n))))= 
                    ((((2::int) * ((2::int) ^ n)) * (bv_to_int (drop n (int2bvn bw x)))) smod bw))")
apply (thin_tac "(((((2::int) * ((2::int) ^ n)) * (bv_to_int (drop n (int2bvn bw x)))) smod bw) =
                 (((2::int) * ((2::int) ^ n)) * ((bv_to_int (drop n (int2bvn bw x))) smod 
                 (bw - (Suc n)))))")
prefer 2
apply simp
apply (subgoal_tac "((((2::int) * ((2::int) ^ n)) * ((bv_to_int (drop n (int2bvn bw x))) smod 
                     (bw - (Suc n)))) )= 
                    (((bv_to_int (drop n (int2bvn bw x))) smod 
                      (bw - (Suc n))) * ((2::int) * ((2::int) ^ n)))")
prefer 2
apply (simp add: mult_ac)
apply simp
apply (simp add: smod_smod_trivial)
apply (subgoal_tac "(((2::int) * ((2::int) ^ n)) * (bv_to_int (drop n (int2bvn bw x)))) = 
                    (((bv_to_int (drop n (int2bvn bw x))) * ((2::int) ^ n)) * (2::int))")
apply (erule ssubst)+
apply simp
apply simp
apply (subgoal_tac "(Suc n) = bw ")
prefer 2
apply simp
apply (subgoal_tac "(Suc n) = bw \<longrightarrow> (n = (bw - (1::nat)))")
prefer 2
apply simp
apply simp
apply (subgoal_tac "(length (drop (bw - (Suc (0::nat))) (int2bvn bw x))) = 1")
prefer 2
apply simp
apply (case_tac "(drop (bw - (Suc (0::nat))) (int2bvn bw x))")
apply simp
apply simp
apply (case_tac "a")
apply simp
apply (simp add: bv_to_nat_replicate_Zero)
apply simp
apply (simp add: bv_to_nat_replicate_Zero bv_to_nat_replicate_One)
apply (subgoal_tac "(int (((2::nat) ^ (bw - (Suc (0::nat)))) - (Suc (0::nat)))) = 
                    ((int ((2::nat) ^ (bw - (Suc (0::nat))))) - (int (Suc (0::nat))))")
prefer 2
apply (subgoal_tac "(Suc 0) \<le> ((2::nat) ^ (bw - (Suc (0::nat))))")
apply (frule_tac m = "((2::nat) ^ (bw - (Suc (0::nat))))" and n = "(Suc 0)" in of_nat_diff)
apply simp
apply (simp add: one_le_power)
apply (simp add: int_power)
apply (simp add: "MoreIntDiv.smod_def" Let_def)
apply (subgoal_tac "(((2::int) ^ (bw - (Suc (0::nat)))) * (2::int)) = ((2::int) ^ bw)")
apply simp
apply (insert mod_mult_self2_is_0 [of "-1" "((2::int) ^ bw)"])
apply simp
apply (insert  power_add [of "(2::int)" "bw - (1::nat)" "1"])
apply simp
apply simp
done


lemma s_lsh_arith:
  "\<lbrakk>0<bw; -(2^(bw - 1)) \<le> x; x < 2^(bw - 1); n \<le> bw\<rbrakk> \<Longrightarrow>
   s_lsh x bw n = (x * 2 ^n) smod  bw"
apply (case_tac "bw \<le> n")
apply (subgoal_tac "bw\<noteq> 0")
apply (frule_tac x = "x" in smod_equality)
apply simp
apply (simp only: s_lsh_by_ge_width_eq_0)
apply (simp add: "MoreIntDiv.smod_def")
apply simp+
(*case bw > n *)
apply (induct "n")
apply simp
apply (subgoal_tac "length (int_to_bv x) \<le> bw")
apply (simp add: length_impl_s_lsh_by_0)
apply (subgoal_tac "bw\<noteq> 0")
apply (frule_tac x = "x" in smod_equality)
apply simp+
apply (case_tac "x = 0")
apply simp 
apply (case_tac "x = -1")
apply (simp add: int_to_bv_def)
apply (case_tac "x < -1")
apply (simp add: length_int_to_bv_upper_limit_lem1 del:int_to_bv_lt0)
apply (simp add: length_int_to_bv_upper_limit_gt0 del:int_to_bv_ge0)
apply (subgoal_tac "bw \<noteq> 0")
prefer 2
apply simp
apply (frule_tac bw = "bw" and x = "x" and n = "n" in s_lsh_arith_aux)
apply simp_all
apply (subgoal_tac "((((x * ((2::int) ^ n)) * (2::int)) smod bw) = 
                    ((((x * ((2::int) ^ n)) smod bw) * (2::int)) smod bw))")
apply (subgoal_tac "((x * ((2::int) ^ n)) * (2::int)) = (x * ((2::int) * ((2::int) ^ n)))")
apply simp
using nat_to_bv_non_Nil 
apply force
apply simp
apply (frule_tac a = "(x * ((2::int) ^ n))" and b = "(2::int)" and c = "bw" in smod_zmult1_eq')
apply (metis One_nat_def   length_int_to_bv_s_lsh  range_impl_s_lsh_by_0 )
proof -
  fix na :: nat
  assume a1: "\<not> bw \<le> Suc na"
  assume a2: "x < 2 ^ (bw - Suc 0)"
  assume a3: "- (2 ^ (bw - Suc 0)) \<le> x"
  assume "s_lsh x bw na = x * 2 ^ na smod bw"
  then have "s_lsh x bw na * 2 smod bw = x * 2 ^ Suc na smod bw"
    by (metis mult.assoc mult.commute power_Suc smod_zmult1_eq')
  then show "s_lsh x bw (Suc na) = x * (2 * 2 ^ na) smod bw"
    using a3 a2 a1 by (simp add: s_lsh_arith_aux)
qed


(* TODO rename, generalize *)

lemma u_lsh_assoc: " (a  \<lless>\<^bsub>u/32\<^esub>  (b + c) ) = (a  \<lless>\<^bsub>u/32\<^esub> b  \<lless>\<^bsub>u/32\<^esub> c )"
 apply (subst u_lsh_adef)+
 apply(subst power_add) 
 apply(subgoal_tac " a * (2 ^ b * 2 ^ c) =  (a * 2 ^ b) * 2 ^ c")
 apply (rotate_tac -1, erule ssubst)
 apply (subst mod_mult_left_eq)
 apply (rule refl)
 apply arith
done

text {* \bf Right-shift operations. *}
(* -------------------------------- *)

lemma s_rsh_lower_limit: 
  assumes x_bounded: "- (2 ^ (w - 1)) \<le> x"
  shows "- (2 ^ (w - 1)) \<le> s_rsh x  w a"
proof (cases "0 < a")
  case False
  with x_bounded show ?thesis
    by (simp add: s_rsh_def)
next
  case True   
  have "- (2 ^ (w - 1)) \<le> (0::int)"
    by auto
  also have "0 \<le> int (bv_to_nat (take (w - a) (int2bvn w x))) "
    by simp
  finally show ?thesis
    using True
    by (simp add: s_rsh_def)
qed

lemma s_rsh_upper_limit: 
  assumes x_bounded: "x < (2 ^ (w - 1))"
  shows "s_rsh x w a < (2 ^ (w - 1))"
proof (cases "0 < a")
  case False
  with x_bounded show ?thesis
    by (simp add: s_rsh_def)
next
  case True
  let ?w="(take (w - a) (int2bvn w x))"
  from bv_to_nat_upper_range [of ?w]
  have "bv_to_nat ?w < 2 ^ length ?w".
  also from True
  have "length ?w \<le> w - 1"
    by simp 
  hence "(2::nat) ^ length ?w \<le> 2 ^ (w - 1)"
    by simp
  finally
  have "int (bv_to_nat ?w) < int (2 ^ (w - 1))"
  using less_imp_of_nat_less by blast
  hence "int (bv_to_nat ?w) < (2 ^ (w - 1))"
    by (simp add: int_power)
  with True show ?thesis
    by (simp add: s_rsh_def)
qed

lemma u_rsh_upper_limit: 
  assumes x_bounded: "x < (2 ^ w)"
  shows "u_rsh x w a < (2 ^ w)"
proof -
  let ?w="(take (length (nat_to_bv x) - a) (nat_to_bv x))"
  from bv_to_nat_upper_range [of ?w]
  have "u_rsh x  w a < (2 ^ length ?w)"
    by (simp add: u_rsh_def)
  also
  from x_bounded
  have "length (nat_to_bv x) \<le> w"
    by (rule nat_upper_limit_impl_length_nat_to_bv_limit)
  hence "length ?w \<le> w"
    by simp 
  hence "(2::nat) ^ length ?w \<le> 2 ^ w"
    by simp
  finally
  show ?thesis .
qed

lemma shift_hd_nth[rule_format]:
"a < 2^ n \<longrightarrow> b < n \<longrightarrow>
  nat2bvn n a ! b  = nat2bvn n (a\<lless>\<^bsub>u/n\<^esub> b) ! 0 "
 apply (intro impI)
 apply (subgoal_tac "a \<le> 2 ^ n - 1")
  apply (drule length_nat_to_bv_upper_limit)
  apply (insert length_nat_to_bv_u_lsh [of "a" "n" "b"])
  apply (simp add: nat2bvn_def Let_def )
  apply (simp add: u_lsh_def nat2bvn_def Let_def )
  
  apply (subst bv_extend_norm_unsigned_eq[THEN sym])  
  apply (simp_all add: bv_extend_def nth_append)

  apply (rule conjI)
   apply arith
  apply (rule impI)
   apply arith
done


(* TODO rename, generalize *)
lemma u_rsh_assoc: " (a   \<ggreater>\<^bsub>u/32\<^esub>  (b + c) ) = (a  \<ggreater>\<^bsub>u/32\<^esub> b  \<ggreater>\<^bsub>u/32\<^esub>  c )"
 apply (simp add: u_rsh_is_div_power2)
 apply(subst power_add) 
 apply (subst div_mult2_eq)
 apply (rule refl) 
done 

(* -------------------------------------------------------------- *)
subsubsection {* Bitwise operations with a fixed maximum bitwidth *}
(* -------------------------------------------------------------- *)

text {* The following lemmata @{text u_bitop_fixed_def} and
 @{text s_bitop_fixed_def} are helpful when arguing about operators of a
 fixed maximum bitwidth. *}


lemma u_bitop_fixed_def:
  "\<lbrakk> w \<ge> length (nat_to_bv x) ; w \<ge> length (nat_to_bv y) ; f (0::bit) (0::bit) = (0::bit)\<rbrakk>
    \<Longrightarrow> u_bitop f x y = bv_to_nat (map (\<lambda> (a,b). f a b)
                                  (zip (bv_extend w 0 (nat_to_bv x))
                                       (bv_extend w 0 (nat_to_bv y))))"
  apply (simp add: u_bitop_def Let_def)
  apply (induct w)
  apply  simp+
  apply (case_tac "Suc w>length(nat_to_bv x) \<and> Suc w>length (nat_to_bv y)")
  apply  clarsimp
  apply(thin_tac "_")
  apply  (simp add: bv_extend_def) 
  apply(subst Suc_diff_le) apply arith
  apply(subst Suc_diff_le) apply arith
  apply simp
  apply (case_tac "length(nat_to_bv x) = Suc w")
  apply simp+
  apply (simp_all add: bv_extend_def bv_msb_def)
done

lemma s_bitop_fixed_def:
  "\<lbrakk> w \<ge> length (int_to_bv x) ; w \<ge> length (int_to_bv y) ; f (0::bit) 0 = 0 \<rbrakk>
    \<Longrightarrow> s_bitop f x y = (let vx=int_to_bv x; vy=int_to_bv y in
                           bv_to_int (map (case_prod f)
                                     (zip (bv_extend w (bv_msb vx) vx)
                                          (bv_extend w (bv_msb vy) vy))))"
 apply (simp add: s_bitop_def Let_def)
  apply (induct w)
  apply  simp+
  apply (case_tac "Suc w>length(int_to_bv x) \<and> Suc w>length (int_to_bv y)")
  apply  clarsimp
  (*apply  (simp add: bv_extend_Suc)*)
  apply  (subgoal_tac "f (bv_msb (int_to_bv x)) (bv_msb (int_to_bv y))
                      = bv_msb (map (case_prod f)
              (zip (bv_extend w (bv_msb (int_to_bv x)) (int_to_bv x))
                (bv_extend w (bv_msb (int_to_bv y)) (int_to_bv y))))")
  (*apply   (simp add: bv_to_int_Cons_bv_msb)*)
  apply  (case_tac w, simp)
 (* apply  (simp add: bv_msb_map_zip_bv_extend)
  apply simp*)
  apply (case_tac "length(int_to_bv x) = Suc w")
  apply  simp+
apply (simp add: bv_extend_def bv_msb_def)
apply (simp add: bv_extend_def bv_msb_def )
using zip_Nil2 apply auto[1] apply (simp add: split: if_split_asm) apply auto[1]
 (* apply (simp_all add: bv_extend_def bv_msb_def 
         split: if_split if_split_asm)
  using zip_Nil2 apply auto[1]*)
sorry


(*  apply (simp add: s_bitop_def Let_def)
  apply (induct w)
  apply  simp+
  apply (case_tac "Suc w>length(int_to_bv x) \<and> Suc w>length (int_to_bv y)")
  apply  clarsimp
  apply (simp_all add: s_bitop_def Let_def bv_extend_def bv_msb_def)
  apply (induct w)
  (*apply  simp+*)
  apply (case_tac "Suc w>length(int_to_bv x) \<and> Suc w>length (int_to_bv y)")
  apply  clarsimp
  apply(subst Suc_diff_le) apply arith
  apply(subst Suc_diff_le) apply arith
  apply  (simp add: bv_extend_Suc)
  apply  (subgoal_tac "f (bv_msb (int_to_bv x)) (bv_msb (int_to_bv y))
                      = bv_msb (map (case_prod f)
              (zip (bv_extend w (bv_msb (int_to_bv x)) (int_to_bv x))
                (bv_extend w (bv_msb (int_to_bv y)) (int_to_bv y))))")
  apply(subst Suc_diff_le) apply arith
  apply(subst Suc_diff_le) apply arith
  apply   (simp add: bv_to_int_Cons_bv_msb)
  apply  (case_tac w, simp)
  apply  (simp add: bv_msb_map_zip_bv_extend)
  
(* ================== rev. 12634 ======================

  apply(subst Suc_diff_le) apply arith
  apply(subst Suc_diff_le) apply arith
  apply simp
  apply (case_tac "length(int_to_bv x) = Suc w")
  apply  simp+
  ================== rev. 12634 ====================== *)
sorry*)

subsubsection{* nat2bvn *}


lemma nat2bvn_hd_is_One[rule_format]:
 "2^ n \<le> a \<longrightarrow> a < 2^(Suc n) \<longrightarrow> (nat2bvn (Suc n) a )! 0 = (1::bit)"
  apply (intro impI)
 apply (drule length_nat_to_bv_lower_limit)
 apply (subgoal_tac "a \<le> 2 ^ Suc n - 1")
  apply (drule length_nat_to_bv_upper_limit)
  apply (simp add: nat2bvn_def Let_def)
  apply (case_tac "nat_to_bv a")
   apply (simp add:bv_extend_def)
  apply (frule nat_to_bv_Cons_impl_head_is_One)
  apply simp
  apply (simp add: bv_extend_def)
 apply arith
done

lemma nat2bvn_hd_is_Zero[rule_format]:
" a < 2^ n \<longrightarrow> (nat2bvn (Suc n) a ) ! 0 = (0::bit)"
 apply (rule impI)
 apply (subgoal_tac "a \<le> 2 ^ n - 1")
  apply (drule length_nat_to_bv_upper_limit)
  apply (simp add:  nat2bvn_def Let_def bv_extend_def)
  apply (subgoal_tac "Suc n - length (nat_to_bv a) = Suc (n - length (nat_to_bv a))")
   apply (rotate_tac -1, erule ssubst)
   apply simp
  apply arith
 apply arith
done

lemma filter_nat2bvn_nat_to_bv_for_One_eq[rule_format]:
"a < 2^w \<longrightarrow> 
length (filter (\<lambda> x. x = (1::bit)) (nat2bvn w a)) = length (filter (\<lambda> x. x = (1::bit)) (nat_to_bv a)) "
 apply (intro impI)
 apply (subgoal_tac "a \<le> 2 ^ w - 1")
  apply (drule length_nat_to_bv_upper_limit)
  apply (simp add: nat2bvn_def Let_def )
  apply (simp add: bv_extend_def)
  apply simp
done

subsubsection {* help lemmas for masking bit operations*}

lemma map_split_bitand_replicate_Zero [rule_format]: 
 " \<forall>i. i = length xs \<longrightarrow> map (case_prod op AND) (zip xs (replicate i (0::bit))) = replicate i 0"    
apply (induct xs)
apply simp_all
done

lemma  map_split_bitand_replicate_One [rule_format]:
 "\<forall>i. i = length xs \<longrightarrow> map (\<lambda>(ua, u). ua AND u) (zip xs (replicate i (1::bit) )) = xs"         
apply (induct xs) 
 apply simp_all
done

lemma map_split_bitor_replicate_Zero  [rule_format] : 
" \<forall>i. i = length xs \<longrightarrow> map (case_prod op OR) (zip xs (replicate i (0::bit) )) = xs"   
apply (induct xs)
apply simp_all
done

(* TODO used only once *)

(* bu somewhat artificially constrained this to bit lists. *)
lemma map_split_bitand_commute [rule_format]:  
"\<forall>ys::bit list. map (case_prod op AND) (zip xs ys) = map (case_prod op AND) (zip ys xs)" 
 apply (induct xs)
 apply auto
 apply (case_tac "ys")
  apply simp
 apply (simp add: bitand_commute)
done

subsubsection {* signed bitwise and  *}

lemma sand_0: " (k  \<and>\<^sub>s 0) = 0"
 apply (simp add: s_bitop_def bv_extend_def bv_msb_def Let_def)  
 apply (subst map_split_bitand_replicate_Zero)
  apply simp
 apply (simp add: bv_to_int_replicate_Zero)
 using nat_to_bv_non_Nil 
 apply force
done

lemma bitand_all_One: 
"\<lbrakk> v \<noteq> [] ; i < length v \<rbrakk> \<Longrightarrow> 
 map (\<lambda>(ua, u). ua AND u) (zip (bv_extend (Suc i) (bv_msb v) v) 
          (bv_extend (length v) (0::bit) ((0::bit) # replicate i 1))) = 
 replicate (length v - i ) (0::bit) @ (drop (length v - i)  v) "

 apply (simp only: bv_extend_def)
 apply simp
 apply (subgoal_tac "Suc (length v - Suc i ) = length v - i" ) 

  apply (subgoal_tac "(zip v (replicate (length v - Suc i) 0 @ 0 # replicate i 1))  = (zip ( take (length v - i)  v @ drop (length v - i)  v) (replicate (length v - Suc i) 0 @ 0 # replicate i 1)) ")
   apply (rotate_tac -1, erule ssubst)
   apply (subgoal_tac " (replicate (length v - Suc i) 0 @ 0 # replicate i 1) = replicate (length v - Suc i + 1) 0 @  replicate i 1")
    apply (rotate_tac -1,erule ssubst)
    apply (subgoal_tac "length (take (length v - i) v ) = length (replicate (length v - Suc i + 1) 0)  ")
     apply (subgoal_tac "length (drop (length v - i) v) = length (replicate i 1) ")
      apply (simp del: replicate_Suc)
       apply (subgoal_tac " length v -  i  = length(take (length v - i) v ) ")
        apply (drule map_split_bitand_replicate_Zero)
        apply (rotate_tac -1, erule ssubst)
       apply (case_tac i) 
        apply simp
      apply (subgoal_tac "i = length (drop (length v - i) v )")
       apply (drule map_split_bitand_replicate_One)       
       apply simp_all
  apply (subgoal_tac "[(0::bit)] = replicate 1 (0::bit)") 
   apply (rotate_tac -1, erule ssubst)
 apply (subgoal_tac "Suc i \<le> length v")  
  apply (drule_tac i ="1" in  diff_add_assoc2)
  apply simp+
apply (metis map_split_bitand_replicate_Zero)
apply (metis le_0_eq length_0_conv not_less_eq_eq)
apply simp
prefer 2
apply (metis replicate_Suc')
apply(drule sym)
apply(simp only:, simp)
apply(case_tac v, simp_all)
sorry

lemma bitand_all_One1: 
"\<lbrakk>  length v \<le> i\<rbrakk> \<Longrightarrow> 
 map (\<lambda>(ua, u). ua AND u) (zip (bv_extend (Suc i) (bv_msb v) v) (bv_extend (length v) 0  (0 # replicate i 1))) = 
 0 # replicate (i - length v ) (bv_msb v)  @ v  "

 apply (simp only: bv_extend_def)
 apply (subgoal_tac "replicate (length v - length (0 # replicate i 1)) 0 = []")
  
  apply (rotate_tac -1, erule ssubst)
  apply (subgoal_tac "replicate i 1 = replicate (i - length v ) 1 @ replicate ( length v ) 1 ")
   apply (rotate_tac -1, erule ssubst) 
   apply (subgoal_tac "length (replicate (Suc i - length v) (bv_msb v) ) = length (0 # replicate (i - length v) 1) ")
    apply (subgoal_tac "length v = length ( replicate (length v) 1)")
    
     apply (simp del: map_eq_Cons_conv)
    apply (subgoal_tac "length v = length v")   
     apply (drule  map_split_bitand_replicate_One)
      apply (simp del: map_eq_Cons_conv)
      apply (subgoal_tac "replicate (Suc i - length v) (bv_msb v) = (bv_msb v) # replicate ( i - length v) (bv_msb v) ")
       apply (rotate_tac -1, erule ssubst)    
       apply (simp add: bitand_commute)
      apply (subgoal_tac "Suc i - length v = i - length v + 1 ")
       apply simp_all
      
 apply (subst replicate_add [THEN sym])  
 apply simp
done

lemma s_and_int_upper_bound: "s_and (int x) (int y) \<le> (int y)"
apply (case_tac "x=0")
 apply clarsimp
 apply (subst s_and_commute)
 apply (simp add: sand_0)
apply (case_tac "y=0")
 apply clarsimp
 apply (simp add: sand_0)
apply (simp add: s_bitop_def)
apply (simp add: Let_def)
apply (cut_tac w="norm_signed (0 # nat_to_bv y)" and v="norm_signed (0 # nat_to_bv x)" 
                  in bitand_bv_less_eq_int)
apply clarsimp
apply (subgoal_tac "nat_to_bv y \<noteq> []")
 apply (subgoal_tac "nat_to_bv x \<noteq> []")
  apply (cut_tac a="(map (\<lambda>(x, y). x AND y)
        (zip (bv_extend (length (norm_signed (0 # nat_to_bv y))) 0 
             (norm_signed (0 # nat_to_bv x))) (bv_extend (length (norm_signed (0 # nat_to_bv x))) 0 
             (norm_signed (0 # nat_to_bv y)))))" and 
         b="(bv_extend (length (norm_signed (0 # nat_to_bv x))) 0 
              (norm_signed (0 # nat_to_bv y)))" in bv_less_eq_int_correct[symmetric])

   apply clarsimp
   apply (rule conjI)
    apply (simp add: length_bv_extend)
    apply (metis bv_extend_is_not_empty_1 list.distinct(1) 
                 norm_signed_Zero_nat_to_bv zip_Nil2)
   apply (simp add: norm_signed_zero_nat_to_bv)
  apply (subgoal_tac 
         "hd (bv_extend (length (norm_signed (0 # nat_to_bv x))) 0 (norm_signed (0 # nat_to_bv y))) =
          0 \<and> hd (bv_extend (length (norm_signed (0 # nat_to_bv y))) 0 (norm_signed (0 # nat_to_bv x))) = 0")
   apply clarsimp
   apply (simp add: bv_msb_def)
  apply (simp add: norm_signed_zero_nat_to_bv)
  apply (simp add: bv_extend_def)
   apply (case_tac "length (nat_to_bv x) - length (nat_to_bv y)", simp)
   apply clarsimp
   apply (simp add: bv_to_nat_replicate_Zero_append)
   apply (simp add: bv_extend_Suc norm_signed_Zero_nat_to_bv)
  apply (case_tac "length (nat_to_bv y) - length (nat_to_bv x)", simp)
  apply clarsimp
 apply clarsimp
 apply (drule nat_to_bv_is_Nil_impl_nat_is_0)
 apply simp
apply clarsimp
apply (drule nat_to_bv_is_Nil_impl_nat_is_0)
apply simp
done

lemma s_and_int_lower_bound: 
      "0 \<le> s_and (int x) (int y)"
apply (simp add: s_bitop_def)
apply (simp add: Let_def)
apply (simp add: bv_to_int_def)
apply (simp split: bit.split)
apply (simp add: bv_msb_def)
apply (simp add: head_map)
apply (case_tac "bv_extend (length (norm_signed (0 # nat_to_bv y))) 0 (norm_signed (0 # nat_to_bv x))")
 apply simp
apply (case_tac "bv_extend (length (norm_signed (0 # nat_to_bv x))) 0 (norm_signed (0 # nat_to_bv y))")
 apply simp
apply clarsimp
apply (case_tac a, simp)
apply (case_tac aa, simp)
apply clarsimp
apply (simp add: bv_extend_def)
apply (case_tac "nat_to_bv x = []", simp)
apply (case_tac "nat_to_bv y = []", simp)
apply (simp add: norm_signed_zero_nat_to_bv)
apply (case_tac "length (nat_to_bv y) - length (nat_to_bv x)", simp)
apply simp
done

lemma s_and_int_range: "0 \<le> s_and (int x) (int y) \<and> s_and (int x) (int y) \<le> (int y)"
  by (simp add: s_and_int_lower_bound s_and_int_upper_bound)

subsubsection{* mask using signed and*}

lemma mask_with_One_is_mod_help1[rule_format]:
"z > 0 \<longrightarrow> z \<le> length (nat_to_bv a) \<longrightarrow> ((int a) \<and>\<^sub>s int (2 ^ z - Suc 0)) = int (a mod 2 ^ z)"
apply (rule impI)+
 apply (case_tac "a = 0")
  apply (simp add: sand_0)
  apply (metis less_nat_zero_code linorder_not_le list.size(3) nat_to_bv_non_Nil)
 apply (subgoal_tac "2 ^ z - Suc 0 = bv_to_nat (replicate z 1)")
  prefer 2
  apply (subst bv_to_nat_replicate_One)
  apply simp
 apply (rotate_tac 4)
 apply (erule ssubst)
 apply(simp add: s_bitop_def Let_def)
 apply (simp add: norm_unsigned_replicate_One)
 apply (simp add: norm_signed_01_is_01)
 apply (subgoal_tac "norm_signed (0 # nat_to_bv a) = 0 # nat_to_bv a")
  prefer 2 
  apply (subgoal_tac "nat_to_bv a = hd (nat_to_bv a) # tl (nat_to_bv a)")
   apply (frule_tac b="a" and x="hd (nat_to_bv a)" and 
                    xs="tl (nat_to_bv a)" in nat_to_bv_Cons_impl_head_is_One)
   apply (rotate_tac -2)
   apply (erule ssubst)
   apply (erule ssubst)
   apply (simp add: norm_signed01)
  apply (subgoal_tac "nat_to_bv a \<noteq> []")
   prefer 2
   apply clarsimp
  apply simp
 apply (rotate_tac -1)
 apply (erule ssubst)
 apply (subgoal_tac "z < length (0 # nat_to_bv a)")
  prefer 2
  apply simp
 apply (subgoal_tac "0 # nat_to_bv a \<noteq> []")
  prefer 2
  apply simp
 apply (drule_tac v="0 # nat_to_bv a" and i="z" in bitand_all_One)
  apply assumption
 apply simp
 apply (subgoal_tac "0 < Suc (length (nat_to_bv a)) - z")
  prefer 2
  apply simp
 apply (drule_tac i="Suc (length (nat_to_bv a)) - z" and 
                     w="drop (Suc (length (nat_to_bv a)) - z) (0 # nat_to_bv a)" in 
                     bv_to_int_replicate_Zero_append_bv_to_nat_eq)
apply (simp add: bv_msb_def drop_is_mod)
done 

lemma mask_with_One_is_mod_help2[rule_format]:
"z > 0 \<longrightarrow> z > length (nat_to_bv a) \<longrightarrow> ((int a) \<and>\<^sub>s int (2 ^ z - Suc 0)) = int (a mod 2 ^ z)"
  apply (rule impI)+
 apply (case_tac "a = 0")
  apply (simp add: sand_0)
  apply (subgoal_tac "(int (2 ^ z - Suc 0) \<and>\<^sub>s 0) = 0")
   apply (simp add: s_and_commute)
  apply (simp add: sand_0)
 apply (subgoal_tac "2 ^ z - Suc 0 = bv_to_nat (replicate z 1)")
  prefer 2
  apply (subst bv_to_nat_replicate_One [of "z"])
  apply simp
 apply (rotate_tac 4)
 apply (erule ssubst)
 apply(simp add: s_bitop_def Let_def)
 apply (simp add: norm_unsigned_replicate_One)
 apply (simp add: norm_signed_01_is_01)
 apply (subgoal_tac "norm_signed (0 # nat_to_bv a) = 0 # nat_to_bv a")
  prefer 2 
  apply (subgoal_tac "nat_to_bv a = hd (nat_to_bv a) # tl (nat_to_bv a)")
   apply (frule_tac b="a" and x="hd (nat_to_bv a)" and xs="tl (nat_to_bv a)" in 
                    nat_to_bv_Cons_impl_head_is_One)
   apply (rotate_tac -2)
   apply (erule ssubst)
   apply (erule ssubst)
   apply (simp add: norm_signed01)
  apply (subgoal_tac "nat_to_bv a \<noteq> []")
   prefer 2
   apply (case_tac "a=0")
    apply simp
   apply clarsimp
   apply (simp add: nat_to_bv_non0)
  apply simp
 apply (rotate_tac -1)
 apply (erule ssubst)
 apply (subgoal_tac "z \<ge> length (0 # nat_to_bv a)")
  prefer 2
  apply simp
 apply (subgoal_tac "0 # nat_to_bv a \<noteq> []")
  prefer 2
  apply simp
 apply (drule_tac v="0 # nat_to_bv a" and i="z" in bitand_all_One1)
 apply (case_tac "bv_msb (0 # nat_to_bv a)")
  prefer 2
  apply simp
 apply (case_tac "map (\<lambda>(ua, u). ua AND u)(zip (bv_extend (Suc z) 0 (0 # nat_to_bv a))
                 (bv_extend (length (0 # nat_to_bv a)) 0 (0 # replicate z 1))) = 
                 0 # replicate (z - length (0 # nat_to_bv a)) 0 @ 0 # nat_to_bv a")
  prefer 2
  apply simp
 apply (rotate_tac -1)
 apply (erule ssubst)
  apply (case_tac "z = length (0 # nat_to_bv a)")
  apply simp
  apply (subgoal_tac "bv_to_nat (nat_to_bv (a)) < 2^(length (nat_to_bv a))")
   prefer 2
   apply (simp only: bv_to_nat_upper_range)
  apply simp
 apply (subgoal_tac "a < 2 ^ z")
  prefer 2
  apply (subgoal_tac "bv_to_nat (nat_to_bv (a)) < 2^(length (nat_to_bv a))")
   prefer 2
   apply (simp only: bv_to_nat_upper_range)
  apply simp
  apply (subgoal_tac "(2::nat) ^ length (nat_to_bv a) \<le> 2 ^ z")
   prefer 2
   apply simp
  apply (auto simp add: less_le_trans bv_msb_def)
 apply (metis Divides.mod_less Suc_pred bv_nat_bv bv_to_nat0 
              bv_to_nat_replicate_Zero_append length_replicate 
              less_SucI nat_to_bv_length_mono nat_to_bv_power2_minus1 
              pow2_greater_zero_nat)
 done

 lemma mask_is_mod_help:
"z > 0 \<longrightarrow> ((int a) \<and>\<^sub>s int (2 ^ z - Suc 0)) = int (a mod 2 ^ z)"
 apply (case_tac "z > length (nat_to_bv a)")
  apply (simp add: mask_with_One_is_mod_help2)
 apply (simp add: mask_with_One_is_mod_help1)
done

lemma mask_is_mod[rule_format]:
"\<forall> a b. (\<exists> z>0. nat_to_bv b = replicate z 1) \<longrightarrow> ((int(a) \<and>\<^sub>s int(b)) = int(a mod (b+1)))"
 apply clarsimp
 apply (subgoal_tac "bv_to_nat (nat_to_bv b) = bv_to_nat (replicate z 1)")
  prefer 2
  apply (simp add: bv_nat_bv)
 apply (thin_tac "nat_to_bv b = replicate z 1")
 apply (simp add: bv_to_nat_replicate_One)
 apply (thin_tac "b = 2 ^ z - Suc 0")
 apply (simp add: mask_is_mod_help)
done

lemma mask_is_mod_nat[rule_format] : "0 < z \<longrightarrow> a \<ge> 0 \<longrightarrow> s_and a (2^z - 1) = a mod 2^z"
 apply clarsimp
apply (cut_tac a="nat a" and z="z" in mask_is_mod_help)
apply (simp add: zmod_int)
apply (simp add: of_nat_diff)
done

subsubsection{* mask using unsigned and *}

lemma unsigned_and_mask[rule_format]:
"nat_to_bv b = replicate k 1 @ replicate m  0  \<longrightarrow> ( a \<and>\<^sub>u b) = a mod 2^(k + m) - a mod 2^m "
apply clarsimp
 apply (simp add: u_bitop_def Let_def)
 apply (case_tac "length (nat_to_bv a) \<le> k+m")
  apply (simp add: bv_extend_def)
  apply (subst zip_append2)
  apply (simp only: map_append)
  apply (subst map_split_bitand_replicate_Zero)
   apply (simp add: min_def)
  apply (subst map_split_bitand_replicate_One)
   apply (subst length_replicate)
   apply (subst length_take)
   apply (simp add: min_def)
  apply (simp add: take_append)
  apply (subst bv_to_nat_replicate_Zero_append)
  apply (subgoal_tac "a < 2 ^ (k + m)")
   apply simp
   apply (subst bv_to_nat_take_append_replicate)
   apply (subst bv_nat_bv)+
   apply (rule refl)
  apply (drule length_nat_to_bv_upper_limit_impl_nat_limit)
  apply assumption

 --"second case"
 apply (subgoal_tac "length (nat_to_bv a) > k + m")
  apply (simp add: bv_extend_def)
  apply (subst zip_append2)
  apply (simp only: map_append)
  apply (subst map_split_bitand_replicate_Zero)
   apply (simp add: min_def)
   apply arith
  apply (subst  bv_to_nat_replicate_Zero_append)
  apply (subst zip_append2)
  apply (simp only: map_append)
  apply (subst map_split_bitand_replicate_One)
   apply (simp add: min_def) 
  apply (subst map_split_bitand_replicate_Zero)  
   apply (simp add: min_def)
  apply simp
  apply (subst bv_to_nat_take_drop_append_replicate)
   apply assumption
  apply (subst bv_nat_bv)+
  apply (rule refl)
 apply simp
done

text {* Masking with @{text u_and} *}

lemma u_and_eq_nth_bitval:
assumes "n < length list"
   and  "list \<noteq> []"
shows "if bitval (list !n) = 0
          then (bv_to_nat (rev list) \<and>\<^sub>u 2 ^ n) = 0
          else (bv_to_nat (rev list) \<and>\<^sub>u 2 ^ n) \<noteq> 0"
proof - 
  have minimum: "min (length list) (Suc n) = (Suc n) \<and> min (length list) n = n"
    using assms by arith

  have split_list: "bv_to_nat (rev list) =
                    bv_to_nat (rev (drop (Suc n) list) 
                    @ rev (take (Suc n) list))"
    by (simp add: rev_append[symmetric])

thus ?thesis using assms minimum
  using u_and_power2[where n = "n"]
  using bv_to_nat_dist_append
  apply (clarsimp, simp add: mod_add_eq)
  apply (cut_tac w ="(rev (take (Suc n) list))" in bv_to_nat_upper_range)
  apply (cut_tac w ="(rev (take n list))" in bv_to_nat_upper_range)
  apply (simp add: take_Suc_conv_app_nth  add.commute)
  done
qed

end
