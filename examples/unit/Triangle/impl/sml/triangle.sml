(*****************************************************************************
 * HOL-TestGen --- theorem-prover based test case generation
 *                 http://www.brucker.ch/projects/hol-testgen/
 *                                                                            
 * max.sml --- the "Triangle" example (SML version)
 * This file is part of HOL-TestGen.
 *
 * Copyright (c) 2014      Achim D. Brucker, Germany
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
(* $Id: triangle.sml 10691 2014-08-31 12:48:28Z brucker $ *)

structure myTriangle = struct

datatype triangle = Equilateral | Scalene | Isosceles | Error;

fun isTriangle (x:IntInf.int,y,z) = ((z<(x+y)) andalso  (x < (x+z)) andalso (y < (x+z)))

fun  testTriangle ((x:IntInf.int),(y,z)) = if isTriangle(x,y,z) then 
                                           if x=y then if y=z  then Equilateral  
                                                               else Isosceles          
                                                   else if y=z then Isosceles           
                                                                else if x=z 
                                                                     then Isosceles      
                                                                     else Scalene
                                            else Error

end
