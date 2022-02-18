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
(* $Id: TestHarness.fs 9071 2011-01-05 00:53:17Z brucker $ *)


namespace HolTestGen
    module TestHarness = 
     type testresult = SUCCESS | WARNING | FAILURE | ERROR | FATAL

     let rsf = false

     let init () = System.Console.Write"NOT YET IMPLEMENTED"
               
     let check retlet prelist testpred =
         let fst (x,y) = x
         let pre = try 
                     (Some(List.fold (fun x y -> x && y) true (List.map (fun x -> (x () = true)) prelist )), None)
                   with 
                     | exn -> (None,Some(exn))
         let post = try 
                      (Some((testpred()=true)),retlet(),None) 
                    with 
                      | exn -> (None,None,Some(exn))
         (pre,post)
    
     let printResultletue toString res = (match res with None   -> "\n" | Some r -> ", result: "+(toString r)+"\n")
        
     let printResult toString (num:int) = function
       | ((Some(true),None),(Some(true),res,None))   -> System.Console.Write ("Test "+(string num)+" -     SUCCESS"+(printResultletue toString res))
                                                        SUCCESS
       | ((Some(true),None),(Some(false),res,None))  -> System.Console.Write ("Test "+(string num)+" - *** FAILURE: post-condition false"+(printResultletue toString res))
                                                        FAILURE 
       | ((Some(true),None),(None,res,Some (exn:exn) )) -> System.Console.Write ("Test "+(string num)+" - *** FAILURE: exception during post-condition\n")
                                                           FAILURE
       | ((Some(false),None),(Some(true),res,None))  -> System.Console.Write ("Test "+(string num)+" -     WARNING: pre-condition false (post-condition true)"+(printResultletue toString res))
                                                        WARNING
       | ((Some(false),None),(Some(false),res,None)) -> System.Console.Write ("Test "+(string num)+" - *   WARNING: pre-condition false (post-condition false)"+(printResultletue toString res))
                                                        WARNING
       | ((Some(false),None),(None,res,Some (exn:exn) ))-> System.Console.Write ("Test "+(string num)+" - **  WARNING: pre-condition false (exception during post_condition)\n")
                                                           WARNING
       | ((None,Some(exn:exn)),(Some(true),res,None))  -> System.Console.Write ("Test "+(string num)+" - **  ERROR:exception during pre-condition (post-condition true)"+(printResultletue toString res))
                                                          ERROR
       | ((None,Some(exn:exn)),(Some(false),res,None)) -> System.Console.Write ("Test "+(string num)+" - **  ERROR: exception during pre-condition (post-condition false)"+(printResultletue toString res))
                                                          ERROR
       | ((None,Some(exn:exn)),(None,res,Some (exn':exn) )) -> System.Console.Write ("Test "+(string num)+" - **  ERROR: exception during pre-condition and post-condition\n")
                                                               ERROR
       |  _                                          -> System.Console.Write ("\nTest "+(string num)+" - ****** FATAL ERROR ******\n\n")
                                                        FATAL
    
     let rec foldl_map f = function
       | (x, [])      -> (x, [] )
       | (x, y :: ys) -> let (x', y') = f (x, y)
                         let (x'', ys') = foldl_map f (x', ys);
                         (x'', y' :: ys')
    

     let filter (pred: 'a->bool) : 'a list -> 'a list = let rec filt = function 
                                                          | []        -> []
                                                          | (x :: xs) -> if pred x then x :: filt xs else filt xs
                                                        filt

     let printList resultToString results =
         let _             = System.Console.Write ("\n\n")
         let _             = System.Console.Write ( "Test Results:\n")
         let _             = System.Console.Write ( "=============\n")
         let (num,testres) = foldl_map (fun (num, res) -> (num+1, (printResult resultToString num res))) (0, results)
         let _             = System.Console.Write ("\n\n")
         let _             = System.Console.Write ("Summary:\n")
         let _             = System.Console.Write ("--------\n")
         let _             = System.Console.Write ("Number successful tests cases: ")
         let suc           = List.length (filter (fun (r) -> (r=SUCCESS)) testres)
         let _             = System.Console.Write ((string suc)+" of "+(string num)+" ")
         let _             = System.Console.Write ("(ca. "+(string ((suc * 100) / num))+"%)\n")
         let _             = System.Console.Write ("Number of warnings:             ")
         let warn          = List.length (filter (fun (r) -> (r=WARNING)) testres)
         let _             = System.Console.Write ((string warn)+" of "+(string num)+" ")
         let _             = System.Console.Write ("(ca. "+(string ((warn * 100) / num))+"%)\n")
         let _             = System.Console.Write ("Number of errors:               ")
         let err           = List.length (filter (fun (r) -> (r=ERROR)) testres)
         let _             = System.Console.Write ((string err)+" of "+(string num)+" ")
         let _             = System.Console.Write ("(ca. "+(string ((err * 100) / num))+"%)\n")
         let _             = System.Console.Write ("Number of failures:             ")
         let fail          = List.length (filter (fun (r) -> (r=FAILURE)) testres)
         let _             = System.Console.Write ((string fail)+" of "+(string num)+" ")
         let _             = System.Console.Write ("(ca. "+(string ((fail * 100) / num))+"%)\n")
         let _             = System.Console.Write ("Number of fatal errors:         ")
         let fatal         = List.length (filter (fun (r) -> (r=FATAL)) testres)
         let _             = System.Console.Write ((string fatal)+" of "+(string num)+" ")
         let _             = System.Console.Write ("(ca. "+(string ((fatal * 100) / num))+"%)\n")
         let _             = System.Console.Write ("\nOverall result: ")
         let _             = if (suc=num) then System.Console.Write ("success") else System.Console.Write ("failed ")
         let _             = System.Console.Write ("\n===============\n\n")
         ()
