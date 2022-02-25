(*****************************************************************************
 * HOL-TestGen --- theorem-prover based test case generation
 *                 http://www.brucker.ch/projects/hol-testgen/
 *                                                                            
 * Code_Integer_Fsharp.thy --- 
 * This file is part of HOL-TestGen.
 *
 * Copyright (c) 2010-2012 ETH Zurich, Switzerland
 *               2010-2012 Achim D. Brucker, Germany
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
(* $Id: Code_Integer_Fsharp.thy 12803 2016-09-01 08:38:47Z brucker $ *)


theory Code_Integer_Fsharp
imports
 code_fsharp
begin
text {*
  Representation-ignorant code equations for conversions.
*}

text {*
  HOL numeral expressions are mapped to integer literals
  in target languages, using predefined target language
  operations for abstract integer operations.
*}

code_printing
  type_constructor integer \<rightharpoonup>
    (Fsharp) "int"

code_printing
  constant "0::integer" \<rightharpoonup>
    (Fsharp) "0"

setup \<open>
  fold (fn target =>
    Numeral.add_code @{const_name Code_Numeral.Pos} I Code_Printer.literal_numeral target
    #> Numeral.add_code @{const_name Code_Numeral.Neg} (op ~) Code_Printer.literal_numeral target)
    ["SML", "OCaml", "Haskell", "Scala", "Fsharp"]
\<close>

code_printing
  constant "plus :: integer \<Rightarrow> _ \<Rightarrow> _" \<rightharpoonup>
    (Fsharp) infixl 8 "+"
| constant "uminus :: integer \<Rightarrow> _" \<rightharpoonup>
    (Fsharp) "-/ _"
| constant "minus :: integer \<Rightarrow> _" \<rightharpoonup>
    (Fsharp) infixl 8 "-"
| constant Code_Numeral.dup \<rightharpoonup>
    (Fsharp) "failwith/ \"dup\""
| constant Code_Numeral.sub \<rightharpoonup>
    (Fsharp) "failwith/ \"sub\""
| constant "times :: integer \<Rightarrow> _ \<Rightarrow> _" \<rightharpoonup>
    (Fsharp) infixl 9 "*"
| constant Code_Numeral.divmod_abs \<rightharpoonup>
    (SML) "IntInf.divMod/ (IntInf.abs _,/ IntInf.abs _)"
| constant "HOL.equal :: integer \<Rightarrow> _ \<Rightarrow> bool" \<rightharpoonup>
    (Fsharp) infixl 6 "="
| constant "less_eq :: integer \<Rightarrow> _ \<Rightarrow> bool" \<rightharpoonup> 
    (Fsharp) infixl 6 "<="
| constant "less :: integer \<Rightarrow> _ \<Rightarrow> bool" \<rightharpoonup>
    (Fsharp) infixl 6 "<"


code_identifier
  code_module Int \<rightharpoonup> (SML) Arith and (OCaml) Arith and (Haskell) Arith
                                    and (Fsharp)

end
