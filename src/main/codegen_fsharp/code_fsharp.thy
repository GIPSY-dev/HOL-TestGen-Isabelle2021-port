(*****************************************************************************
 * HOL-TestGen --- theorem-prover based test case generation
 *                 http://www.brucker.ch/projects/hol-testgen/
 *                                                                            
 * code_fsharp.thy  --- 
 * This file is part of HOL-TestGen.
 *
 * Copyright (c) 2010-2012 ETH Zurich, Switzerland
 *               2010-2013 Achim D. Brucker, Germany
 *               2016      The University of Sheffield, UK
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
(* $Id: code_fsharp.thy 12648 2016-06-17 09:26:51Z brucker $ *)

theory code_fsharp
imports 
  Main
begin

ML_file "code_fsharp.ML" 

(* In file HOL/HOL.thy *)

code_printing
  type_constructor bool \<rightharpoonup>
  (Fsharp) "bool"

code_printing 
  constant True \<rightharpoonup>
    (Fsharp) "true"
| constant False \<rightharpoonup>
    (Fsharp) "false"
| constant Not \<rightharpoonup>
    (Fsharp) "not" 
| constant HOL.conj \<rightharpoonup>
    (Fsharp) infixl 3 "&&"
| constant HOL.disj \<rightharpoonup>
    (Fsharp) infixl 2 "||"
| constant HOL.implies \<rightharpoonup>
    (Fsharp) "!(if (_)/ then (_)/ else true)"
| constant If \<rightharpoonup>
    (Fsharp) "!(if (_)/ then (_)/ else (_))"

code_reserved Fsharp
  bool

code_printing 
  constant undefined \<rightharpoonup>
  (Fsharp) "failwith/ \"undefined\""


(* In file HOL/Option.thy *)
code_printing
  type_constructor option \<rightharpoonup>
  (Fsharp) "_ option"

code_printing 
  constant None \<rightharpoonup>
    (Fsharp) "None"
| constant Some \<rightharpoonup>
    (Fsharp) "Some _"

code_reserved Fsharp
  option None Some

(* In file HOL/List.thy *)
code_printing 
  type_constructor list \<rightharpoonup>
  (Fsharp) "_ list"
| constant Nil \<rightharpoonup>
    (Fsharp) "[]"
| constant Cons \<rightharpoonup>
  (Fsharp) "(_ ::/ _)"

code_reserved Fsharp
  list

code_printing 
  constant "op @" \<rightharpoonup>
  (Fsharp) infixr 6 "@"

code_printing 
  type_constructor "unit" \<rightharpoonup>
  (Fsharp) "unit"

code_printing 
  constant "Unity" \<rightharpoonup>
  (Fsharp) "()"

code_reserved Fsharp
  unit

code_printing 
  type_constructor prod \<rightharpoonup>
  (Fsharp) infix 2 "*"

code_printing 
  constant "Pair" \<rightharpoonup>
  (Fsharp) "!((_),/ (_))"

end
