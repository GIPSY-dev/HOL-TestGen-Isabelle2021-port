(*****************************************************************************
 * HOL-TestGen --- theorem-prover based test case generation
 *                 http://www.brucker.ch/projects/hol-testgen/
 *                                                                            
 * harness.sml --- the HOL-TestGen test harness
 * This file is part of HOL-TestGen.
 *
 * Copyright (c) 2005-2007 ETH Zurich, Switzerland
 *               2011 Achim D. Brucker
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
(* $Id: harness.sml 9954 2013-11-15 09:03:21Z brucker $ *)


structure TestHarness  = 
struct
datatype testresult = SUCCESS | WARNING | FAILURE | ERROR | FATAL

val rsf = false;

fun init () = print "NOT YET IMPLEMENTED\n"
	      
    

fun check (prelist,testpred)  = 
    let
	fun fst (x,y)= x;
	val pre = (SOME(List.foldl (fn (x,y) => x andalso y) true 
			      (map (fn x => (x () = true)) prelist)),NONE)
	    handle e => (NONE,SOME(e));	
	val post =  (SOME((testpred()=true)), NONE) 
	    handle e => (NONE,SOME(e));    
    in 
	(pre,post)
    end

val  checkList =  map check 

fun printResult num ((SOME(true),NONE),(SOME(true),NONE)) =   
    let
	val _ = print ("Test "^(Int.toString(num))^
		       " -     SUCCESS\n")
    in 
	SUCCESS
    end
  | printResult num ((SOME(true),NONE),(SOME(false),NONE)) =  
    let
	val _ = print ("Test "^(Int.toString(num))
		       ^" - *** FAILURE: post-condition false\n")
    in 
	FAILURE
    end
  | printResult num ((SOME(true),NONE),(NONE,SOME(e_post))) = 
    let
	val _ = print ("Test "^(Int.toString(num))
		       ^" - *** FAILURE: exception during post-condition\n")
    in 
	FAILURE
    end
  | printResult num ((SOME(false),NONE),(SOME(true),NONE))=  
    let
	val _ = print ("Test "^(Int.toString(num))
		       ^" -     WARNING: pre-condition false "^
		       "(post-condition true)\n")
    in 
	WARNING
    end
  | printResult num ((SOME(false),NONE),(SOME(false),NONE)) =
    let
	val _ = print ("Test "^(Int.toString(num))
		       ^" - *   WARNING: pre-condition false "^
		       "(post-condition false)\n")
    in 
	WARNING
    end
  | printResult num ((SOME(false),NONE),(NONE,SOME(e_post))) =
    let
	val _ = print ("Test "^(Int.toString(num))^
		       " - **  WARNING: pre-condition false "^
		       "(exception during post_condition)\n")
    in 
	WARNING
    end
  | printResult num ((NONE,SOME(e_pre)),(SOME(true),NONE)) =  
    let
	val _ = print ("Test "^(Int.toString(num))^
		       " - **  ERROR:exception during pre-condition "^
		       "(post-condition true)\n")
    in 
	ERROR
    end
  | printResult num ((NONE,SOME(e_pre)),(SOME(false),NONE)) = 
    let
	val _ = print ("Test "^(Int.toString(num))^
		       " - **  ERROR: exception during pre-condition "^
	   "(post-condition false)\n")
    in 
	ERROR
    end
  | printResult num ((NONE,SOME(e_pre)),(NONE,SOME(e_post))) =
    let
	val _ = print ("Test "^(Int.toString(num))^
		       " - **  ERROR: exception during pre-condition "^
		       "and post-condition\n")
    in 
	ERROR
    end
  | printResult num  _ =  
    let
	val _ = print ("\nTest "^(Int.toString(num))^
		       " - ****** FATAL ERROR ******\n\n")
    in 
	FATAL
    end
    
fun foldl_map _ (x, []) = (x, [])
  | foldl_map f (x, y :: ys) =
    let
        val (x', y') = f (x, y);
        val (x'', ys') = foldl_map f (x', ys);
    in (x'', y' :: ys') end;
    
fun filter (pred: 'a->bool) : 'a list -> 'a list =
    let fun filt [] = []
          | filt (x :: xs) = if pred x then x :: filt xs else filt xs
    in filt end;

fun printList results  = 
    let	
	val _ = print("\n\n")
	val _ = print( "Test Results:\n") 
	val _ = print( "=============\n") 
	val (num,testres) = (foldl_map (fn (num,res) => 
					   (num+1,(printResult  
						       num res) )) 
				       (0, results));
	val _ = print ("\n\n");
	val _ = print ("Summary:\n");
	val _ = print ("--------\n");
	val _ = print ("Number successful tests cases: ")
	val suc = length (filter (fn (r) => (r=SUCCESS)) testres)
	val _ = print (Int.toString(suc)^" of "^Int.toString(num)^" ")
	val _ = print ("(ca. "^Int.toString((suc * 100) div num)^"%)\n")
	val _ = print ("Number of warnings:             ")
	val warn = length (filter (fn (r) => (r=WARNING)) testres)
	val _ = print (Int.toString(warn)^" of "^Int.toString(num)^" ")
	val _ = print ("(ca. "^Int.toString((warn * 100) div num)^"%)\n")
	val _ = print ("Number of errors:               ")
	val err = length (filter (fn (r) => (r=ERROR)) testres)
	val _ = print (Int.toString(err)^" of "^Int.toString(num)^" ")
	val _ = print ("(ca. "^Int.toString((err * 100) div num)^"%)\n")
	val _ = print ("Number of failures:             ")
	val fail = length (filter (fn (r) => (r=FAILURE)) testres)
	val _ = print (Int.toString(fail)^" of "^Int.toString(num)^" ")
	val _ = print ("(ca. "^Int.toString((fail * 100) div num)^"%)\n")
	val _ = print ("Number of fatal errors:         ")
	val fatal = length (filter (fn (r) => (r=FATAL)) testres)
	val _ = print (Int.toString(fatal)^" of "^Int.toString(num)^" ")
	val _ = print ("(ca. "^Int.toString((fatal * 100) div num)^"%)\n")
	val _ = print ("\nOverall result: ")
	val _ = if(suc=num) 
		then print ("success")
		else print ("failed ")
	val _ = print ("\n===============\n\n")
    in
	()
    end


fun run test_cases = printList (checkList test_cases)


end 	



 
