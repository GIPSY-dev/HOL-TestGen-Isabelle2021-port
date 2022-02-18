(*****************************************************************************
 * HOL-TestGen --- theorem-prover based test case generation
 *                 http://www.brucker.ch/projects/hol-testgen/
 *                                                                            
 * RBT_def.thy --- testing red-black trees
 * This file is part of HOL-TestGen.
 *
 * Copyright (c) 2005-2007 ETH Zurich, Switzerland
 *               2011      Achim D. Brucker, Germany
 *
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are
 * met:
 *
 *     * Redistributions of source code must retain the above copyright
 *       notice, this list of conditions and the following disclaimer.
 *
 *     * Redistributions in binary form must reproduce the above
 *       copyright notice, this list of conditions and the following
 *       disclaimer in the documentation and/or other materials provided
 *       with the distribution.
 *
 *     * Neither the name of the copyright holders nor the names of its
 *       contributors may be used to endorse or promote products derived
 *       from this software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
 * "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
 * LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
 * A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
 * OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
 * SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
 * LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
 * DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
 * THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
 * (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
 * OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 ******************************************************************************)
(* $Id: RBT_def.thy 13155 2017-08-18 20:22:39Z brucker $ *)

 
chapter {* Defining Red-Black Trees *}


theory 
  RBT_def
imports
   Testing
begin


(******************************)

  (* mimicking ml's datatype order *)
text {* The implementation of Red-Black trees is mainly based
on the following datatype declaration:
*}
datatype ml_order = LESS | EQUAL | GREATER  

class LINORDER = linorder +
  fixes compare :: "'a \<Rightarrow> 'a \<Rightarrow> ml_order"
  assumes LINORDER_less  : "((compare x y) = LESS)    = (x < y)"
    and LINORDER_equal   : "((compare x y) = EQUAL)   = (x = y)"
    and LINORDER_greater : "((compare x y) = GREATER) = (y < x)"

datatype  color = R | B

datatype 'a tree = E | T color "'a tree" "'a" "'a tree"


(* insert *)

  
fun
  ins :: "'a::LINORDER \<times> 'a tree \<Rightarrow> 'a tree"
where 
  ins_empty  : "ins (x, E) = T R E x E"
| ins_branch : "ins (x, (T color a y b)) = 
  (case (compare x y) of 
    LESS \<Rightarrow> (case a of 
              E \<Rightarrow> (T B (ins (x, a)) y b)
            |(T m c z d) \<Rightarrow> (case m of 
                              R \<Rightarrow> (case (compare x z) of 
                                     LESS \<Rightarrow> (case (ins (x, c))of 
                                               E \<Rightarrow> (T B (T R E z d) y b)
                                              |(T m e w f) \<Rightarrow> 
                                             (case m of 
                                               R \<Rightarrow> (T R (T B e w f) z (T B d y b))
                                             | B \<Rightarrow> (T B (T R (T B e w f) z d) y b)))
                                    |EQUAL \<Rightarrow> (T color  (T R c x d) y b)
                                    |GREATER \<Rightarrow> (case (ins (x, d)) of 
                                                 E \<Rightarrow> (T B (T R c z E) y b)
                                                |(T m e w f) \<Rightarrow> (case m of 
                                                   R \<Rightarrow> (T R (T B c z e) w (T B f y b))
                                                  |B \<Rightarrow> (T B (T R c z (T B e w f)) y b))
                                                )
                                   )
                           | B \<Rightarrow> (T B (ins (x, a)) y b))
             )
  | EQUAL \<Rightarrow> (T color a x b)
  | GREATER \<Rightarrow> (case b of 
                 E \<Rightarrow> (T B a y (ins (x, b)))
               |(T m c z d) \<Rightarrow> (case m of 
                                 R \<Rightarrow>(case (compare x z) of 
                                        LESS \<Rightarrow> (case (ins (x, c)) of 
                                                  E \<Rightarrow> (T B a y (T R E z d))
                                                |(T m e w f) \<Rightarrow> (case m of 
                                                    R \<Rightarrow> (T R (T B a y e) w (T B f z d))
                                                   |B \<Rightarrow> (T B a y (T R (T B e w f) z d))) 
                                                )
                                      | EQUAL \<Rightarrow> (T color a y (T R c x d))
                                      | GREATER \<Rightarrow> (case (ins (x, d)) of 
                                                 E \<Rightarrow> (T B a y (T R c z E))
                                                |(T m e w f) \<Rightarrow> (case m of 
                                                    R \<Rightarrow> (T R (T B a y c) z (T B e w f))
                                                   |B \<Rightarrow> (T B a y (T R c z (T B e w f))))
                                                   )
                                     ) 
                                |B \<Rightarrow> (T B a y (ins (x, b)))))
  )"







(* deletion *)
(* originally "local datatype", used to memorize information about 
   structure and content of tree *)
datatype 'a zipper
        = TOP
        | LEFT  color "'a" "'a tree" "'a zipper"
        | RIGHT color "'a tree" "'a" "'a zipper"

(* functions used by delete *)

(* reconstruction of the tree, second argument is changed subtree *)

fun  zip    :: "'a zipper \<Rightarrow> 'a tree \<Rightarrow> 'a tree"
where
  zip_top:   "zip TOP t = t"
  | zip_left:  "zip (LEFT color x b z) a = zip z (T color a x b)"
  | zip_right: "zip (RIGHT color a x z) b = zip z (T color a x b)"

(* needed to construct wfo for bbZip *)

(* left subtrees have to be weighted stronger in order to cope with rotations *)
fun 
  treesize   :: "'a tree \<Rightarrow> nat"
where
   treesize_empty:   "treesize E = 0"
|  treesize_branch:  "treesize (T c a x b) = 1 + treesize a + treesize a + treesize b"

(* sum up weights of trees in the zipper *)
fun 
  zippersize :: "'a zipper \<Rightarrow> nat"
where
  zippersize_top:   "zippersize TOP = 0"
  | zippersize_left:  "zippersize (LEFT c x t z) = treesize t + zippersize z"
  | zippersize_right: "zippersize (RIGHT c t x z) = treesize t + zippersize z"


(* reconstructing trees, the new subtree having a black deficit *)
function (sequential) bbZip  :: "'a zipper \<times> 'a tree \<Rightarrow> bool \<times> 'a tree"
where
  bbZip_1: "bbZip (TOP, t) = (True, t)"
|  bbZip_2: "bbZip ((LEFT B x (T R c y d) z), a) = 
                  bbZip ((LEFT R x c (LEFT B y d z)), a)"  (* case 1L *)
|  bbZip_3: "bbZip ((LEFT color x (T B (T R c y d) w e) z), a) = 
                  bbZip ((LEFT color x (T B c y (T R d w e)) z), a)" (* case 3L *)
|  bbZip_4: "bbZip ((LEFT color x (T B c y (T R d w e)) z), a) = 
                  (False, zip z (T color (T B a x c) y (T B d w e)))" (* case 4L *)
|  bbZip_5: "bbZip ((LEFT R x (T B c y d) z), a) = 
                  (False, zip z (T B a x (T R c y d)))" (* case 2L *)
|  bbZip_6: "bbZip ((LEFT B x (T B c y d) z), a) = 
                  bbZip (z, (T B a x (T R c y d)))" (* case 2L *)
|  bbZip_7: "bbZip ((RIGHT color (T R c y d) x z), b) = 
                  bbZip ((RIGHT R d x (RIGHT B c y z)), b)" (* case 1R *)
|  bbZip_8: "bbZip ((RIGHT color (T B (T R c w d) y e) x z), b) = 
                  bbZip ((RIGHT color (T B c w (T R d y e)) x z), b)" (* case 3R *)
|  bbZip_9: "bbZip ((RIGHT color (T B c y (T R d w e)) x z), b) = 
                  (False, zip z (T color c y (T B (T R d w e) x b)))" (* case 4R *)
|  bbZip_10:"bbZip ((RIGHT R (T B c y d) x z), b) = 
                  (False, zip z (T B (T R c y d) x b))" (* case 2R *)
|  bbZip_11:"bbZip ((RIGHT B (T B c y d) x z), b) = 
                  bbZip (z, (T B (T R c y d) x b))" (* case 2R *)
|  bbZip_12:"bbZip (z, t) = (False, zip z t)"
by pat_completeness  auto

termination bbZip
apply (relation "measure (%(z,t).(zippersize z))")
by(auto)


(* getting symmetric successor, information about deficit and resulting subtree *)
fun delMin :: "'a tree \<times> 'a zipper \<Rightarrow> ('a \<times> (bool  \<times> 'a tree)) option "
where
  del_min:  "delMin ((T R E y b), z) = Some (y, (False, zip z b))"
|  delMin_1: "delMin ((T B E y b), z) = Some (y, bbZip(z, b))"
|  delMin_2: "delMin ((T color a y b), z) = delMin(a, (LEFT color y b z))"
|  delMin_3: "delMin (E, z) = None"  (* raise Match *)

(* replaced _ by c, let (x, (needB, b')) = delMin(b, TOP) by sequence of assignements *)
(* choose appropriate function for reconstruction *)
fun  join   :: "color \<times> 'a tree \<times> 'a tree \<times> 'a zipper \<Rightarrow> ('a tree) option"
where
  join_1:   "join (R, E, E, z) = Some (zip z E)"
|  join_2:   "join (c, a, E, z) = Some (snd(bbZip(z, a)))"       (* color = black *)
|  join_3:   "join (c, E, b, z) = Some (snd(bbZip(z, b)))"       (* color = black *)
|  join_4:   "join (color, a, b, z) = (case (delMin(b, TOP)) of None \<Rightarrow> None
                                    | (Some r) \<Rightarrow> 
                 (let x = fst (r); 
                      needB = fst(snd(r)); 
                      b' = snd(snd(r))
                  in  if needB
                      then Some (snd(bbZip(z,(T color a x b'))))  
                      else Some (zip z (T color a x b'))
                  )
                                      )"


(* delete k *)
fun  del    :: "'a::LINORDER \<Rightarrow> 'a tree \<Rightarrow> 'a zipper \<Rightarrow> ('a tree) option"
where
  del_empty: "del k E z = None" (* raise LibBase.NotFound    *)
| del_branch: "del k (T color a y b) z = (case (compare k y)
                 of LESS \<Rightarrow> (del k a (LEFT color y b z))
                  | EQUAL \<Rightarrow> (join (color, a, b, z)) 
                  | GREATER \<Rightarrow> (del k b (RIGHT color a y z)))"

(* delete k in t using del with empty zipper *)
definition 
  delete :: "'a::LINORDER \<Rightarrow> 'a tree \<Rightarrow> ('a tree) option"
where
  "delete k t \<equiv> del k t TOP"

(* end of translation *)

(* extended version of inserting as in Okasaki's implementation, 
   coloring the root black after finishing insertion *)

fun
  makeBlack :: "'a tree \<Rightarrow> 'a tree"
where 
  makeBlack_empty:   "makeBlack E = E"
|  makeBlack_branch:  "makeBlack (T color a x b) = (T B a x b)"

definition 
  insert :: "'a::LINORDER \<Rightarrow> 'a tree \<Rightarrow> 'a tree"
where
 "insert x t \<equiv> makeBlack (ins(x,t))"

(* invariants *)

text {*
In this example we have chosen not only to check if keys are stored or
deleted correctly in the trees but also to check if the trees satisfy
the balancing invariants. We formalize the red and black invariant by recursive
predicates:


*}

fun isin         :: "'a::LINORDER \<Rightarrow> 'a tree \<Rightarrow> bool"
where
    isin_empty :  "isin x E = False"
 |  isin_branch : "isin x (T c a y b) = (((compare x y) = EQUAL) 
                                       | (isin x a) | (isin x b))"

fun isord        :: "('a::LINORDER) tree \<Rightarrow> bool"
where
    isord_empty  : "isord E = True"
 |  isord_branch : "isord (T c a y b) = 
                    (isord a \<and> isord b 
                     \<and> (\<forall> x. isin x a \<longrightarrow> ((compare x y) = LESS))
                     \<and> (\<forall> x. isin x b \<longrightarrow> ((compare x y) = GREATER)))"


text{* weak red invariant: no red node has a red child *} 
fun   redinv       :: "'a tree \<Rightarrow> bool"
where  redinv_1:   "redinv E = True"
     | redinv_2:   "redinv (T B a y b) = (redinv a \<and> redinv b)"
     | redinv_3:   "redinv (T R (T R a x b) y c) = False"
     | redinv_4:   "redinv (T R a x (T R b y c)) = False"
     | redinv_5:   "redinv (T R a x b) = (redinv a \<and> redinv b)"


text{* strong red invariant: every red node has an immediate black ancestor, i.e. 
   the root is black and the weak red invariant holds *}
fun   strong_redinv :: "'a tree \<Rightarrow> bool"
where 
   Rinv_1:  "strong_redinv E = True"
|  Rinv_2:  "strong_redinv (T R a y b) = False"
|  Rinv_3:  "strong_redinv (T B a y b) = (redinv a \<and> redinv b)"


text{* calculating maximal number of black nodes on any path from root to leaf *}
fun  max_B_height :: "'a tree \<Rightarrow> nat"
where
  maxB_height_1:  "max_B_height E = 0"
| maxB_height_3:  "max_B_height (T B a y b) 
                   = Suc(max (max_B_height a) (max_B_height b))"
|  maxB_height_2:  "max_B_height (T R a y b) 
                   = (max (max_B_height a) (max_B_height b))"


text{* black invariant: number of black nodes equal on all paths from root to leaf *}
fun   blackinv     :: "'a tree \<Rightarrow> bool"
where 
      blackinv_1:  "blackinv E = True"
|     blackinv_2:  "blackinv (T color a y b) 
                       = ((blackinv a) \<and> (blackinv b) 
                          \<and> ((max_B_height a) = (max_B_height b)))"


section {* Advanced Elements of the Test Specification and Test-Case-Generation *}

instantiation int::LINORDER
begin

definition "compare (x::int) y
                 = (if (x < y) then LESS 
                                else (if (y < x) 
                                      then GREATER 
                                      else EQUAL))"

instance
  by intro_classes (simp_all add: compare_int_def)

end


lemma compare1[simp]:"(compare (x::int) y = EQUAL) = (x=y)"
by(auto simp:compare_int_def)

lemma compare2[simp]:"(compare (x::int) y = LESS) = (x<y)"
by(auto simp:compare_int_def)

lemma compare3[simp]:"(compare (x::int) y = GREATER) = (y<x)"
by(auto simp:compare_int_def)



text{* Now we come to the core part of the test generation:
  specifying the test specification. We will test an arbitrary program
  (insertion \verb+add+, deletion \verb+delete+) for test data
  that fulfills the following conditions:
  \begin{itemize}
  \item the trees must respect the invariants, i.e.~in particular
        the red and the black invariant,
  \item the trees must even respect the strong red invariant - i.e.
        the top node must be black,
  \item the program under test gets an additional parameter \verb+y+
        that is contained in the tree (useful for delete),
  \item the tree must be ordered (otherwise the implementations will
        fail). 
  \end{itemize}

  The analysis of previous test case generation attempts showed   
  that the following lemmas (altogether trivial to prove) help
  to rule out many constraints that are unsolvable - this knowledge
  is both useful for increasing the coverage (not so many failures
  will occur) as well for efficiency reasons: attempting to random solve
  unsolvable constraints takes time. Recall that that the number
  of random solve attempts is controlled by the \verb+iterations+
  variable in the test environment of this test specification. 
*}


lemma max_0_0 : "((max (a::nat) b) = 0) = (a = 0 \<and> (b = 0))"
 by(auto simp: max_def)

lemma [simp]: "(max (Suc a) b) \<noteq> 0"
 by(auto simp: max_def)

lemma [simp]: "(max b (Suc a) ) \<noteq> 0"
 by(auto simp: max_def)

lemma size_0[simp]: "(size x = 0) = (x = E)"
 by(induct "x",auto)


end
