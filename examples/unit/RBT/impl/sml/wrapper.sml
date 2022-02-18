(*****************************************************************************
 * HOL-TestGen --- theorem-prover based test case generation
 *                 http://www.brucker.ch/projects/hol-testgen/
 *                                                                            
 * wrapper.sml --- wrapper for calling RBT deleteimplementation 
 * This file is part of HOL-TestGen.
 *
 * Copyright (c) 2005-2007, ETH Zurich, Switzerland
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
(* $Id: wrapper.sml 12864 2016-09-20 10:45:25Z brucker $ *)

structure wrapper = 
struct
(* open IntRedBlackSet;  *)

datatype color = R | B
datatype 'a tree
      = E
      | T of (color * ('a tree) * 'a * ('a tree))

type 'a Tree = 'a tree


fun convT conv E                 = E
  | convT conv (T(c, t1, v, t2)) = T(c, convT conv t1, conv v, convT conv t2)                   
                
fun fromIntRedBlackSet fromInt IntRedBlackSet.E = E
  | fromIntRedBlackSet fromInt (IntRedBlackSet.T(IntRedBlackSet.R,t1,e,t2)) = T(R, fromIntRedBlackSet fromInt t1, fromInt(e), fromIntRedBlackSet fromInt t2) 
  | fromIntRedBlackSet fromInt (IntRedBlackSet.T(IntRedBlackSet.B,t1,e,t2)) = T(B, fromIntRedBlackSet fromInt t1, fromInt(e), fromIntRedBlackSet fromInt t2) 

fun toIntRedBlackSet toInt E = IntRedBlackSet.E
  | toIntRedBlackSet toInt (T(R,t1,e,t2)) = IntRedBlackSet.T(IntRedBlackSet.R, toIntRedBlackSet toInt t1, toInt(e), toIntRedBlackSet toInt t2) 
  | toIntRedBlackSet toInt (T(B,t1,e,t2)) = IntRedBlackSet.T(IntRedBlackSet.B, toIntRedBlackSet toInt t1, toInt(e), toIntRedBlackSet toInt t2) 

fun del fromInt toInt  (e,s)  =  let 
                       val retset = IntRedBlackSet.delete  ((IntRedBlackSet.SET(0,toIntRedBlackSet (toInt) s)), (toInt) e); 
	               val (IntRedBlackSet.SET(_,ret)) = retset;
		 in fromIntRedBlackSet (fromInt) ret end

end
