(*****************************************************************************
 * HOL-TestGen --- theorem-prover based test case generation
 *                 http://www.brucker.ch/projects/hol-testgen/
 *                                                                            
 * This file is part of HOL-TestGen.
 *
 * Copyright (c) 2011 Achim D. Brucker, Germany
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
(* $Id: TestHarnessDemo.fs 9071 2011-01-05 00:53:17Z brucker $ *)


namespace HolTestGen

module TestHarnessDemo = 
  open System
  do
    (* define function under test *)
    let fut x y = x / y
    (**************************************************************)
    (* run test harness without observing the return letue of fut *)
    (**************************************************************)
    (* define stub for geting return letue and converting the
       return letue to string *)
    let retlet () = None
    let toString a = ""

    (* pre eletuates to true and post eletuates to true *)
    let pre_0   = [fun () -> true 
                   fun () -> (5 = 5)]
    let post_0  = fun () -> (fut  10 2)  = 5
    let ret_0   = (TestHarness.check retlet pre_0 post_0)
    let _       = TestHarness.printResult toString 0 ret_0

    (* pre eletuates to true and post eletuates to false *)
    let pre_1   = [fun () -> true
                   fun () -> 5 = 5]
    let post_1  = fun () -> (fut  10 2)  = 3
    let ret_1   = (TestHarness.check retlet pre_1 post_1)
    let _       = TestHarness.printResult toString 1 ret_1

    (* pre eletuates to true and post throws exception*)
    let pre_2   = [fun () -> true
                   fun () -> 5 = 5]
    let post_2  = fun () -> (fut  10 0)  = 3
    let ret_2   = (TestHarness.check retlet pre_2 post_2)
    let _       = TestHarness.printResult toString 2 ret_2

    (* pre eletuates to false and post eletuates to true *)
    let pre_3   = [fun () -> false
                   fun () -> 5 = 5]
    let post_3  = fun () -> (fut 12 2) = 6
    let ret_3   = (TestHarness.check retlet pre_3 post_3)
    let _       = TestHarness.printResult toString 3 ret_3

    (* pre eletuates to false and post eletuates to false *)
    let pre_4   = [fun () -> false
                   fun () -> 5 = 5]
    let post_4  = fun () -> (fut  10 2)  = 3
    let ret_4   = (TestHarness.check retlet pre_4 post_4)
    let _       = TestHarness.printResult toString 4 ret_4

    (* pre eletuates to false and post throws exception*)
    let pre_5   = [fun () -> false
                   fun () -> 5 = 5]
    let post_5  = fun () -> (fut  10 0)  = 3
    let ret_5   = (TestHarness.check retlet pre_5 post_5)
    let _       = TestHarness.printResult toString 5 ret_5

    (* pre throws exception and post eletuates to true *)
    let pre_6   = [fun () -> (fut 10 0)=1
                   fun () -> 5 = 5]
    let post_6  = fun () -> (fut 12 2) = 6
    let ret_6   = (TestHarness.check retlet pre_6 post_6)
    let _       = TestHarness.printResult toString 6 ret_6

    (* pre throws exception and post eletuates to false *)
    let pre_7   = [fun () -> (fut 10 0) = 1
                   fun () -> 5 = 5]
    let post_7  = fun () -> (fut  10 2)  = 3
    let ret_7   = (TestHarness.check retlet pre_7 post_7)
    let _       = TestHarness.printResult toString 7 ret_7

    (* pre throws exception and post throws exception*)
    let pre_8   = [fun () -> (fut 10 0) =1
                   fun () -> 5 = 5]
    let post_8  = fun () -> (fut  10 0)  = 3
    let ret_8   = (TestHarness.check retlet pre_8 post_8)
    let _       = TestHarness.printResult toString 8 ret_8

    let results = [ret_0; ret_1; ret_2; ret_3; ret_4; ret_5; ret_6; ret_7; ret_8]
    let _       = TestHarness.printList toString results

    (**************************************************************)
    (* run test harness with observing the return letue of fut    *)
    (**************************************************************)
    (* define functions for getting return letue and converting the
       return letue to string *)
    let ret = ref 0
    let elet (f:int) =  ((ret := f);f)
    let retlet () = Some(!ret)
    let toString a = (string a)

    (* pre eletuates to true and post eletuates to true *)
    let pre_0   = [fun () -> true
                   fun () -> 5 = 5]
    let post_0  = fun () -> elet (fut  10 2)  = 5
    let ret_0   = (TestHarness.check retlet pre_0 post_0)
    let _       = TestHarness.printResult toString 0 ret_0

    (* pre eletuates to true and post eletuates to false *)
    let pre_1   = [fun () -> true
                   fun () -> 5 = 5]
    let post_1  = fun () -> elet (fut  10 2)  = 3
    let ret_1   = (TestHarness.check retlet pre_1 post_1)
    let _       = TestHarness.printResult toString 1 ret_1

    (* pre eletuates to true and post throws exception*)
    let pre_2   = [fun () -> true
                   fun () -> 5 = 5]
    let post_2  = fun () -> elet (fut  10 0)  = 3
    let ret_2   = (TestHarness.check retlet pre_2 post_2)
    let _       = TestHarness.printResult toString 2 ret_2

    (* pre eletuates to false and post eletuates to true *)
    let pre_3   = [fun () -> false
                   fun () -> 5 = 5]
    let post_3  = fun () -> elet (fut 12 2) = 6
    let ret_3   = (TestHarness.check retlet pre_3 post_3)
    let _       = TestHarness.printResult toString 3 ret_3

    (* pre eletuates to false and post eletuates to false *)
    let pre_4   = [fun () -> false
                   fun () -> 5 = 5]
    let post_4  = fun () -> elet (fut  10 2)  = 3
    let ret_4   = (TestHarness.check retlet pre_4 post_4)
    let _       = TestHarness.printResult toString 4 ret_4

    (* pre eletuates to false and post throws exception*)
    let pre_5   = [fun () -> false
                   fun () -> 5 = 5]
    let post_5  = fun () -> elet (fut  10 0)  = 3
    let ret_5   = (TestHarness.check retlet pre_5 post_5)
    let _       = TestHarness.printResult toString 5 ret_5

    (* pre throws exception and post eletuates to true *)
    let pre_6   = [fun () -> (fut 10 0)=1
                   fun () -> 5 = 5]
    let post_6  = fun () -> elet (fut 12 2) = 6
    let ret_6   = (TestHarness.check retlet pre_6 post_6)
    let _       = TestHarness.printResult toString 6 ret_6

    (* pre throws exception and post eletuates to false *)
    let pre_7   = [fun () -> (fut 10 0) = 1
                   fun () -> 5 = 5]
    let post_7  = fun () -> elet (fut  10 2)  = 3
    let ret_7   = (TestHarness.check retlet pre_7 post_7)
    let _       = TestHarness.printResult toString 7 ret_7

    (* pre throws exception and post throws exception*)
    let pre_8   = [fun () -> (fut 10 0) =1
                   fun () -> 5 = 5]
    let post_8  = fun () -> elet (fut  10 0)  = 3
    let ret_8   = (TestHarness.check retlet pre_8 post_8)
    let _       = TestHarness.printResult toString 8 ret_8

    let results = [ret_0; ret_1; ret_2; ret_3; ret_4; ret_5; ret_6; ret_7; ret_8]
    let _       = TestHarness.printList toString results

    System.Console.WriteLine("  * Finished *")
