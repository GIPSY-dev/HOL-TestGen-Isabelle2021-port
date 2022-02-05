(*****************************************************************************
 * HOL-TestGen --- theorem-prover based test case generation
 *                 http://www.brucker.ch/projects/hol-testgen/
 *                                                                            
 * AQ.thy thy --- 
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
(* $Id: AQ.thy 9263 2011-12-25 15:49:36Z brucker $ *)


theory AQ
imports code_fsharp
begin

datatype 'a queue = AQueue "'a list" "'a list"

definition empty :: "'a queue" where
  "empty = AQueue [] []"

primrec enqueue :: "'a \<Rightarrow> 'a queue \<Rightarrow> 'a queue" where
  "enqueue x (AQueue xs ys) = AQueue (x # xs) ys"

fun dequeue :: "'a queue \<Rightarrow> 'a option \<times> 'a queue" where
   "dequeue (AQueue [] []) = (None, AQueue [] [])"
 | "dequeue (AQueue xs (y # ys)) = (Some y, AQueue xs ys)"
 | "dequeue (AQueue xs []) = 
      (case rev xs of y # ys \<Rightarrow> (Some y, AQueue [] ys))"

fun not :: "bool \<Rightarrow> bool" where
    "not True = False"
  | "not False = True"

fun head2 :: "('b list) list \<Rightarrow> 'b option" where
   "head2 [] = None"
 | "head2 (x # xs) = (case x of [] \<Rightarrow> None | (y # ys) \<Rightarrow> Some y)"

export_code empty dequeue enqueue not head2 in Fsharp
  module_name Example file "test.fs"
