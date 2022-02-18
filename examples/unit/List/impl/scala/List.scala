/*****************************************************************************
 * HOL-TestGen --- theorem-prover based test case generation
 *                 http://www.brucker.ch/projects/hol-testgen/
 *                                                                            
 * List.scala --- the "List" example (Scala version)
 * This file is part of HOL-TestGen.
 *
 * Copyright (c) 2013      Achim D. Brucker, Germany
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
 ***************************************************************************** */

object myList {
  /* incorrect implementation: */  
  def ins_p (x:BigInt, xs:List[BigInt]):List[BigInt] = { xs match {
    case Nil     => x::Nil
    case (y::ys) => {if (x < y) {y::(x::ys)} else {(y::(ins_p(x,ys)))}}
  }}
  def sort_p (xs:List[BigInt]):List[BigInt] = { xs match {
    case Nil     => Nil
    case (y::ys) => ins_p(y, (sort_p(ys)))
  }} 

  /* correct implementation: */
  def ins_pp (x:BigInt, xs:List[BigInt]):List[BigInt] = { xs match {
    case Nil     => x::Nil
    case (y::ys) => {if (x < y) {x::(ins_pp(y, ys))} else {(y::(ins_p(x,ys)))}}
  }}
  def sort_pp (xs:List[BigInt]):List[BigInt] = { xs match {
    case Nil     => Nil
    case (y::ys) => ins_pp(y, (sort_pp(ys)))
  }} 

  /* binding name for testing: */
  def sort[T] (l:List[BigInt]) = sort_p(l)
} /* object MyList */
