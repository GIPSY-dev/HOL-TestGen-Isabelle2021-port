(*****************************************************************************
 * HOL-TestGen --- theorem-prover based test case generation
 *                 http://www.brucker.ch/projects/hol-testgen/
 *                                                                            
 * AVL_def.thy --- AVL tree specification
 * This file is part of HOL-TestGen.
 *
 * Copyright (c) 1998, TU Munchen, Germany
 * Copyright (c) 2005-2007 ETH Zurich, Switzerland
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
(* $Id: AVL_def.thy 13156 2017-08-18 20:29:44Z brucker $ *)

chapter "Parametrized AVL Trees"

theory 
  AVL_def 
imports
   Testing
begin

text {* This test theory specifies a quite conceptual algorithm
        for insertion and deletion in AVL Trees. It is essentially 
        a streamlined version of the AFP~\cite{afp} theory developed
        by Pusch, Nipkow, Klein and the authors. *}

(* *********************************************************************** *)
(*                                                                         *)
(* Conceptual Algorithm                                                    *)
(*                                                                         *)
(* *********************************************************************** *)

datatype 'a tree = ET |  MKT 'a "'a tree" "'a tree"

fun height :: "'a tree \<Rightarrow> nat"
where
  "height ET = 0"
| "height (MKT n l r) = 1 + max (height l) (height r)"

fun is_in  :: "'a \<Rightarrow> 'a tree \<Rightarrow> bool"
where
  "is_in k ET = False"
| "is_in k (MKT n l r) = (k=n \<or> is_in k l \<or> is_in k r)"

fun is_ord :: "('a::order) tree \<Rightarrow> bool"
where
  isord_base: "is_ord ET = True"
| isord_rec:  "is_ord (MKT n l r) = ((\<forall>n'. is_in n' l \<longrightarrow> n' < n) \<and>
                                    (\<forall>n'. is_in n' r \<longrightarrow> n < n') \<and>
                                    is_ord l \<and> is_ord r)"

fun is_bal :: "'a tree \<Rightarrow> bool"
where
  "is_bal ET = True"
| "is_bal (MKT n l r) = ((height l = height r \<or>
                         height l = 1+height r \<or>
                         height r = 1+height l) \<and> 
                         is_bal l \<and> is_bal r)"
text {* 
  We also provide a more efficient variant of @{text is_in}: 
*}

fun
  is_in_eff   :: "('a::order) \<Rightarrow> 'a tree \<Rightarrow> bool"
where
  "is_in_eff k ET = False"
| "is_in_eff k (MKT n l r) = (if k = n then True
                              else (if k<n then (is_in_eff k l)
                                    else (is_in_eff k r)))"

datatype bal = Just | Left | Right

definition bal :: "'a tree \<Rightarrow> bal"
where  "bal t \<equiv> case t of ET \<Rightarrow> Just
                 | (MKT n l r) \<Rightarrow> if height l = height r then Just
                                 else if height l < height r then Right 
                                      else Left"

hide_const ln

fun     r_rot  :: "'a \<times> 'a tree \<times> 'a tree \<Rightarrow> 'a tree"
where  "r_rot (n, MKT ln ll lr, r) = MKT ln ll (MKT n lr r)"

fun     l_rot  :: "'a \<times> 'a tree \<times> 'a tree \<Rightarrow> 'a tree"
where  "l_rot(n, l, MKT rn rl rr) = MKT rn (MKT n l rl) rr"

fun     lr_rot :: "'a \<times> 'a tree \<times> 'a tree \<Rightarrow> 'a tree"
where  "lr_rot(n, MKT ln ll (MKT lrn lrl lrr), r) = 
             MKT lrn (MKT ln ll lrl) (MKT n lrr r)"

fun     rl_rot :: "'a \<times> 'a tree \<times> 'a tree \<Rightarrow> 'a tree"
where  "rl_rot(n, l, MKT rn (MKT rln rll rlr) rr) = 
                MKT rln (MKT n l rll) (MKT rn rlr rr)"


definition l_bal :: "'a \<Rightarrow> 'a tree \<Rightarrow> 'a tree \<Rightarrow> 'a tree"
where     "l_bal n l r \<equiv> if bal l = Right 
                         then lr_rot (n, l, r)
                         else r_rot (n, l, r)"

definition  r_bal :: "'a \<Rightarrow> 'a tree \<Rightarrow> 'a tree \<Rightarrow> 'a tree"
where      "r_bal n l r \<equiv> if bal r = Left
                           then rl_rot (n, l, r)
                           else l_rot (n, l, r)"

fun insert :: "'a::order \<Rightarrow> 'a tree \<Rightarrow> 'a tree"
where
  insert_base:  "insert x ET = MKT x ET ET"
| insert_rec:   "insert x (MKT n l r) =
                  (if x=n
                   then MKT n l r
                   else if x<n
                        then let l' = insert x l
                             in if height l' = 2+height r
                                then l_bal n l' r
                                else MKT n l' r
                        else let r' = insert x r
                             in if height r' = 2+height l
                                then r_bal n l r'
                                else MKT n l r')"



text {* delete *}

consts
  tmax :: "'a tree \<Rightarrow> 'a"
  delete :: "'a::order \<times> ('a tree) \<Rightarrow> ('a tree)"

end
