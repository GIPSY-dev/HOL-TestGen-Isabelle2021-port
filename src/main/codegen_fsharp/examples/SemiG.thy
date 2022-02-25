(*****************************************************************************
 * HOL-TestGen --- theorem-prover based test case generation
 *                 http://www.brucker.ch/projects/hol-testgen/
 *                                                                            
 * SemiG.thy ---
 * This file is part of HOL-TestGen.
 *
 * Copyright (c) 2010-2012 ETH Zurich, Switzerland
 *               2010-2012 Achim D. Brucker, Germany
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
(* $Id: SemiG.thy 9263 2011-12-25 15:49:36Z brucker $ *)

theory SemiG
imports Main
begin

class semigroup =
  fixes mult :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<otimes>" 70)
  assumes assoc: "(x \<otimes> y) \<otimes> z = x \<otimes> (y \<otimes> z)"

class monoid = semigroup +
  fixes neutral :: "'a" ("\<one>")
  assumes neutl: "x \<otimes> \<one> = x"
      and neutr: "\<one> \<otimes> x = x"

instantiation nat :: monoid
begin
  primrec mult_nat where
    "0 \<otimes> n = (0::nat)"
  | "Suc m \<otimes> n = n + m \<otimes> n"

  definition neutral_nat where
    "\<one> = Suc 0"

  lemma add_mult_distrib:
    fixes n m q :: nat
    shows "(n + m) \<otimes> q = n \<otimes> q + m \<otimes> q"
    by (induct n) simp_all

  instance proof
    fix m n q :: nat
    show "m \<otimes> n \<otimes> q = m \<otimes> (n \<otimes> q)"
      by (induct m) (simp_all add: add_mult_distrib)
    show "\<one> \<otimes> n = n"
      by (simp add: neutral_nat_def)
    show "m \<otimes> \<one> = m"
      by (induct m) (simp_all add: neutral_nat_def)
  qed
end

primrec (in monoid) pow :: "nat \<Rightarrow> 'a \<Rightarrow> 'a" where
  "pow 0 a = \<one>"
| "pow (Suc n) a = a \<otimes> pow n a"

definition bexp :: "nat \<Rightarrow> nat" where
  "bexp n = pow n (Suc (Suc 0))"

export_code pow bexp in OCaml
  module_name SemiG file "SemiG.ml"

end

