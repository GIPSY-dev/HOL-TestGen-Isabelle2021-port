/*****************************************************************************
 * HOL-TestGen --- theorem-prover based test case generation
 *                 http://www.brucker.ch/projects/hol-testgen/
 *                                                                            
 * harness.scala --- the HOL-TestGen test harness
 * This file is part of HOL-TestGen.
 *
 * Copyright (c) 2013 Achim D. Brucker, Germany
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
 ***************************************************************************** */
// $Id: harness.fs 9605 2013-02-03 20:15:15Z brucker $

/*

structure TestHarness :
  sig
DONE datatype testresult = ERROR | FAILURE | FATAL | SUCCESS | WARNING
DONE val rsf : bool
DONE val init : unit -> unit
DONE    val check : (unit -> bool) list * (unit -> bool)
                -> (bool option * exn option) * (bool option * exn option)
DONE    val checkList : ((unit -> bool) list * (unit -> bool)) list
                    -> ((bool option * exn option) * 
                        (bool option * exn option)) list

DONE    val printResult : int
                      -> (bool option * 'a option) * (bool option * 'b option)
                         -> testresult
    val foldl_map : ('a * 'b -> 'a * 'c) -> 'a * 'b list -> 'a * 'c list
    val filter : ('a -> bool) -> 'a list -> 'a list
    val printList : ((bool option * 'a option) * (bool option * 'b option)) 
                      list
                    -> unit
DONE    val run : ((unit -> bool) list * (unit -> bool)) list -> unit
  end

*/

object TestHarness
{

  val rsf = false;  

  def init() = {
    println("NOT YET IMPLEMENTED");
  }

  object testresult extends Enumeration {
    type testresult = Value
    val SUCCESS, WARNING, FAILURE, ERROR, FATAL = Value
  }

  
  def check(test_case:(List[() => Boolean], () => Boolean)):((Option[Boolean], Option[String]),(Option[Boolean], Option[String])) = 
  {
    val (prelist, testpred) = test_case; // TODO 
    val pre = try{
                  (Some(((prelist.map( (x:() => Boolean) =>  x () )).foldLeft(true)( ( (x:Boolean), (y:Boolean)) => x && y))),None);
              } catch {
                  case (e : Exception) => (None, Some(e.getMessage))
              }
    val post= try{
                  (Some(testpred ()),None);
              } catch {
                  case (e : Exception) => (None, Some(e.getMessage))
              }
    return (pre,post)
  }  

  def checkList(test_cases:List[(List[() => Boolean], () => Boolean)]):List[((Option[Boolean], Option[String]), (Option[Boolean], Option[String]))]=
  {
    return test_cases.map(check);
  } 


  def printResult (num:Integer,result:((Option[Boolean], Option[String]),(Option[Boolean], Option[String]))):testresult.testresult = {
    result match {
      case ((Some(true),None),(Some(true),None))    => {println("Test "+num+" -     SUCCESS"); return testresult. SUCCESS}
      case ((Some(true),None),(Some(false),None))   => {println("Test "+num+" - *** FAILURE: post-condition false"); return testresult.FAILURE}
      case ((Some(true),None),(None,Some(e_post)))  => {println("Test "+num+" - *** FAILURE: exception during post-condition: "+e_post); return testresult.FAILURE}
      case ((Some(false),None),(Some(true),None))   => {println("Test "+num+" - *   WARNING: pre-condition false (post-condition true)"); return testresult.WARNING}
      case ((Some(false),None),(Some(false),None))  => {println("Test "+num+" - *   WARNING: pre-condition false (post-condition false)"); return testresult.WARNING}
      case ((Some(false),None),(None,Some(e_post))) => {println("Test "+num+" - *   WARNING: pre-condition false (exception during post_condition): "+e_post); return testresult.WARNING}
      case ((None,Some(e_pre)),(Some(true),None))   => {println("Test "+num+" - **  ERROR:exception during pre-condition (post-condition true)"); return testresult.ERROR}
      case ((None,Some(e_pre)),(Some(false),None))  => {println("Test "+num+" - **  ERROR: exception during pre-condition (post-condition false)"); return testresult.ERROR}
      case ((None,Some(e_pre)),(None,Some(e_post))) => {println("Test "+num+" - **  ERROR: exception during pre-condition and post-condition: "+e_post); return testresult.ERROR}
      case _                                        => {println("Test "+num+" - ****** FATAL ERROR ******"); return testresult.FATAL}
    }  
   } 

  def foldl_map[A,B,C] (f:(A,B)=>(A,C), x:A,xs:List[B]):((A,List[C])) = {
   xs match {
    case Nil     => (x,Nil)
    case (y::ys) => {
      val (xp,yp) = f(x,y);
      val (xpp,ysp) = foldl_map (f, xp,ys);
      (xpp,yp::ysp)
    }
  }
  }

  def printList(results:List[((Option[Boolean], Option[String]), (Option[Boolean], Option[String]))]){ 
    println("");
    println("");
    println( "Test Results:")
    println( "=============")
    val (num, testres) = foldl_map (((num:Int,res:((Option[Boolean], Option[String]),(Option[Boolean], Option[String]))) 
                                       => (num+1,(printResult(num,res)))),0,results);
    val suc  = (testres.filter((r:testresult.testresult) => r == testresult.SUCCESS)).length
    val warn = (testres.filter((r:testresult.testresult) => r == testresult.WARNING)).length
    val err  = (testres.filter((r:testresult.testresult) => r == testresult.ERROR)).length
    val fail = (testres.filter((r:testresult.testresult) => r == testresult.FAILURE)).length
    val fatal= (testres.filter((r:testresult.testresult) => r == testresult.FATAL)).length

    println ();
    println ();
    println("Summary:");
    println("--------");
    println("Number successful tests cases: "+suc  +" of "+num+" (ca. "+(suc   * 100 / num)+"%)");

    println("Number of warnings:            "+warn +" of "+num+" (ca. "+(warn  * 100 / num)+"%)");
    println("Number of errors:              "+err  +" of "+num+" (ca. "+(err   * 100 / num)+"%)");
    println("Number of failures:            "+fail +" of "+num+" (ca. "+(fail  * 100 / num)+"%)");
    println("Number of fatal errors:        "+fatal+" of "+num+" (ca. "+(fatal * 100 / num)+"%)");
    println();
    if (suc == num) {
      println("Overall result: success");
    }else{
      println("Overall result: failure");    
    }
    println("===============");
    println();
  }

  def run(test_cases:List[(List[() => Boolean], () => Boolean)]){
    printList (checkList(test_cases));
  }

} /* object TestHarness */
