(*****************************************************************************
 * HOL-TestGen --- theorem-prover based test case generation
 *                 http://www.brucker.ch/projects/hol-testgen/
 *                                                                            
 * Triangle.thy --- The classical triangle example
 * This file is part of HOL-TestGen.
 *
 * Copyright (c) 2005-2007 ETH Zurich, Switzerland
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
(* $Id: Triangle.thy 12973 2017-01-05 21:04:24Z brucker $ *)

chapter {* The Triangle Example *}


theory 
  Triangle
imports
  Testing
  (* Testing *)
begin

text {*
A prominent example for automatic test case generation is the triangle
problem~\cite{north:automatic:1990}: given three integers representing the 
lengths of the sides of a triangle, a
small algorithm has to check whether these integers describe an equilateral,
isosceles, or scalene triangle, or no triangle at all. First we define an 
abstract data type describing the possible results in Isabelle/HOL:
*}

datatype triangle = equilateral | scalene | isosceles | error

text {*
For clarity (and as an example for specification modularization) we define an
auxiliary predicate deciding if the three lengths are describing a non-empty triangle:
*}

definition is_triangle :: "[int,int,int] \<Rightarrow> bool"
where     "is_triangle x y z \<equiv> (0<x \<and> 0<y \<and> 0 < z \<and>  (z < x+y) \<and> (x < y+z) \<and> (y < x+z))"


text {* Now we define the behavior of the triangle program: *}


definition triangle_classifier_spec :: "[int,int,int] \<Rightarrow> triangle"
where     "triangle_classifier_spec x y z \<equiv> 
               (if is_triangle x y z  
                then if x=y then if y=z  then equilateral  
                                         else  isosceles          
                             else if y=z then isosceles           
                                         else if x=z 
                                              then isosceles      
                                              else scalene 
               else error)"
end
