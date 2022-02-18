(*****************************************************************************
 * HOL-TestGen --- theorem-prover based test case generation
 *                 http://www.brucker.ch/projects/hol-testgen/
 *
 * UPF
 * This file is part of HOL-TestGen.
 *
 * Copyright (c) 2010-2012 ETH Zurich, Switzerland
 *               2010-2012 Achim D. Brucker, Germany
 *               2010-2012 Université Paris-Sud, France
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
(* $Id: CodeGeneratorSetup.thy 12724 2016-08-12 15:55:33Z brucker $ *)


theory 
  CodeGeneratorSetup
imports 
  ServiceTest  
  Code_Integer_Fsharp 
  Code_Char_chr_Fsharp
  Code_String_Fsharp       
begin


consts PUT :: 'a
code_const PUT (Fsharp "List.map (fun (x : Lazy<unit stubs.decision>) -> x.Force ())")

code_type Operation (Fsharp "Operation")
code_const createSCR (Fsharp "lazy (stubs.createSCR _ _ _)")
code_const appendEntry (Fsharp "lazy (stubs.appendEntry _ _ _ _ _)")
code_const deleteEntry (Fsharp "lazy (stubs.deleteEntry _ _ _ _)")
code_const readEntry (Fsharp "lazy (stubs.readEntry _ _ _ _)")
code_const readSCR (Fsharp "lazy (stubs.readSCR _ _ _)")
code_const addLR (Fsharp "lazy (stubs.addLR _ _ _ _ _)")
code_const removeLR (Fsharp "lazy (stubs.removeLR _ _ _ _)")
code_const deleteSCR (Fsharp "lazy (stubs.deleteSCR _ _ _)")
code_const changeStatus (Fsharp "lazy (stubs.changeStatus _ _ _ _ _)")
code_const editEntry (Fsharp "lazy (stubs.editEntry _ _ _ _ _)")
code_type role (Fsharp "stubs.Role")
code_const"ClinicalPractitioner" and "Nurse" and "Clerical"
  (Fsharp "stubs.ClinicalPractitioner" and "stubs.Nurse" and "stubs.Clerical")



code_type decision (Fsharp "_ stubs.decision")
code_const "allow" and "deny" (Fsharp "stubs.Allow" and "stubs.Deny")


code_const "lazy" (Fsharp "lazy (_) ") 
code_type Lazy (Fsharp "Lazy<bool>")

(* Unsure, how much of the following is needed: *)

code_type status (Fsharp "Status")
code_const Open (Fsharp "stubs.Open")
code_const Closed (Fsharp "stubs.Closed")

code_type data (Fsharp "string")


code_const dummyContent (Fsharp "stubs.dummyContent")

code_const set (Fsharp "Set.ofList")


end
