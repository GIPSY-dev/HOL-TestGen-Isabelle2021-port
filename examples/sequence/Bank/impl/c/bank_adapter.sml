(*****************************************************************************
 * HOL-TestGen --- theorem-prover based test case generation
 *                 http://www.brucker.ch/projects/hol-testgen/
 *                                                                            
 * List.sml --- foreign language interface for "List" example (C version)
 * This file is part of HOL-TestGen.
 *
 * Copyright (c) 2005-2007 ETH Zurich, Switzerland
 *               2013      Achim D. Brucker, Germany
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
(* $Id: List.sml 11028 2015-01-03 07:36:59Z wolff $ *)

structure BankAdapter = struct

val c_deposit  = _import "deposit" public: int * int * int -> unit;
val c_withdraw = _import "withdraw" public: int * int * int -> unit;
val c_balance  = _import "balance" public: int * int -> int;

(* Note, the conversion from List to Array and vice versa is only
   neded because our C implementation works over Arrays whereas 
   our specification is defined over lists. *)

fun customer_to_int x = 4;

fun balance (str) (no:int) (s)=
                (let val x : int = c_balance(customer_to_int str,  no);
                 in  SOME(IntInf.fromInt x, s) end)
   
fun deposit (str) (no:IntInf.int) (amount:IntInf.int) (s)=
                (c_deposit(customer_to_int str, IntInf.toInt no, IntInf.toInt amount);
                 SOME((),s))

fun withdraw(str) (no:IntInf.int) (amount:IntInf.int) (s)=
                 (c_withdraw(customer_to_int str, IntInf.toInt no, IntInf.toInt amount);
                  SOME((),s))

 

end

