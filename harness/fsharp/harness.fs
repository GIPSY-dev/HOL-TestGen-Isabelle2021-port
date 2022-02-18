(*****************************************************************************
 * HOL-TestGen --- theorem-prover based test case generation
 *                 http://www.brucker.ch/projects/hol-testgen/
 *                                                                            
 * harness.fs --- the HOL-TestGen test harness
 * This file is part of HOL-TestGen.
 *
 * Copyright (c) 2005-2013 Achim D. Brucker, Germany
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
 * LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES LOSS OF USE,
 * DATA, OR PROFITS OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
 * THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
 * (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
 * OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 ******************************************************************************)
(* $Id: harness.fs 9606 2013-02-03 20:17:02Z brucker $ *)

module TestHarness


type testresult = SUCCESS | WARNING | FAILURE | ERROR

type Either<'a,'b> = Left of 'a
                   | Right of 'b

let force (x : Lazy<'a>) : 'a = x.Force ()

// Create a lazy value that when forces evaluates the test
let check (prelist, testpred) = 
  lazy (
    let pre = try Right <| List.forall id (List.map force prelist)
              with e -> Left e
    let post = try Right <| force testpred
               with e -> Left e
    in (pre,post)
  )

let checkList l = List.map check l

// Print the result of a single test case.
let printResult num res =
  printf "Test %2d - " num
  match res with
  | (Right true, Right true) ->
    printfn "    SUCCESS"
    SUCCESS

  | (Right true, Right false) ->
    printfn "*** FAILURE: post-condition false"
    FAILURE

  | (Right true, Left _) ->
    printfn "*** FAILURE: exception during post-condition"
    FAILURE

  | (Right false, Right true) ->
    printfn "    WARNING: pre-condition false (post-condition true)"
    WARNING

  | (Right false, Right false) ->
    printfn "*   WARNING: pre-condition false (post-condition false)"
    WARNING

  | (Right false, Left _) ->
    printfn "**  WARNING: pre-condition false (exception during post_condition)"
    WARNING

  | (Left _, Right true) ->
    printfn "**  ERROR: exception during pre-condition (post-condition true)"
    ERROR

  | (Left _, Right false) ->
    printfn "**  ERROR: exception during pre-condition (post-condition false)"
    ERROR

  | (Left _, Left _) ->
    printfn "**  ERROR: exception during pre-condition and post-condition"
    ERROR
    
let rec foldl_map f =
  function 
  | (x, []) -> (x, [])
  | (x, y :: ys) ->
      let (x', y') = f (x, y)
      let (x'', ys') = foldl_map f (x', ys)
      (x'', y' :: ys')
    
let printList results  = 
  printfn "\n"
  printfn "Test Results:"
  printfn "============="

  // Force one test at a time and print the result together with the test index.
  let (num, testres) = foldl_map (fun (num,res) ->
                                      (num+1, printResult num (force res))) 
                                 (0, results)
  printfn "\n"

  let suc = List.length (List.filter ((=) SUCCESS) testres)
  let warn = List.length (List.filter ((=) WARNING) testres)
  let err = List.length (List.filter ((=) ERROR) testres)
  let fail = List.length (List.filter ((=) FAILURE) testres)

  printfn "Summary:"
  printfn "--------"
  printfn "Number of successful test cases:  %2d of %2d (ca. %3d%%)"
          suc num (suc * 100 / num)

  printfn "Number of warnings:               %2d of %2d (ca. %3d%%)"
          warn num (warn * 100 / num)

  printfn "Number of errors:                 %2d of %2d (ca. %3d%%)"
          err num (err * 100 / num)

  printfn "Number of failures:               %2d of %2d (ca. %3d%%)"
          fail num (fail * 100 / num)

  printf  "\nOverall result: "
  if suc = num
    then printfn "success"
    else printfn "failed"
  printfn "===============\n"


let run test_cases = printList (checkList test_cases)
