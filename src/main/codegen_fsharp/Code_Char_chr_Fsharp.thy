(*****************************************************************************
 * HOL-TestGen --- theorem-prover based test case generation
 *                 http://www.brucker.ch/projects/hol-testgen/
 *                                                                            
 * Code_Char_chr_Fsharp.thy --- Isar setup for HOL-TestGen
 * This file is part of HOL-TestGen.
 *
 * Copyright (c) 2010-2012 ETH Zurich, Switzerland
 *               2010-2013 Achim D. Brucker, Germany
 *               2016      The University of Sheffield, UK
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
(* $Id: Code_Char_chr_Fsharp.thy 12648 2016-06-17 09:26:51Z brucker $ *)

theory Code_Char_chr_Fsharp
imports 
(*  "~~/src/HOL/Library/Char_ord" *)
  Code_Char_Fsharp 
  code_fsharp
begin

definition
  "int_of_char = int o nat_of_char"

lemma [code]:
  "nat_of_char = nat o int_of_char"
  unfolding int_of_char_def by (simp add: fun_eq_iff)

definition
  "char_of_int = char_of_nat o nat"

lemma [code]:
  "char_of_nat = char_of_int o int"
  unfolding char_of_int_def by (simp add: fun_eq_iff)


code_printing 
  constant "Unity" \<rightharpoonup>
  (Fsharp) "()"

code_printing
  constant int_of_char \<rightharpoonup> 
  (SML)     "!(IntInf.fromInt o Char.ord)" and
  (OCaml)   "Big'_int.big'_int'_of'_int (Char.code _)" and 
  (Fsharp)  "Big'_int.big'_int'_of'_int (Char.code _)" and 
  (Haskell) "toInteger (fromEnum (_ :: Char))" and 
  (Scala)   "BigInt(_.toInt)" 
| constant char_of_int \<rightharpoonup>
  (SML)     "!(Char.chr o IntInf.toInt)" and
  (OCaml)   "Char.chr (Big'_int.int'_of'_big'_int _)" and
  (Fsharp)  "Char.chr (Big'_int.int'_of'_big'_int _)" and
  (Haskell) "!(let chr k | (0 <= k && k < 256) = toEnum k :: Char in chr . fromInteger)" and
  (Scala)   "!((k: BigInt) => if (BigInt(0) <= k && k < BigInt(256)) k.charValue else error(\"character value out of range\"))"

end
