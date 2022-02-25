(*****************************************************************************
 * HOL-TestGen --- theorem-prover based test case generation
 *                 http://www.brucker.ch/projects/hol-testgen/
 *                                                                            
 * log_thy.thy --- Simple Logging Framework for HOL-TestGen
 * This file is part of HOL-TestGen.
 *
 * Copyright (c) 2005-2009 ETH Zurich, Switzerland
 *               2009-2013 Achim D. Brucker, Germany
 *               2010-2013 Université Paris-Sud, France
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
(* $Id: log.thy 11032 2015-01-04 10:02:45Z wolff $ *)

theory 
  log
imports 
  version
begin 

text{* Attempts/Elements for a reform: replace the ref's by a proper Isabelle state-
management. by bu*}
ML {* val tc_timer = Attrib.setup_config_int @{binding tc_timer} (K 0) *}
ML_val {* @{assert} (Config.get @{context} tc_timer = 0) *}
ML{* Config.put tc_timer 4 @{context}  *}
ML{*

type timer_config = {tc_timer : Time.time, 
                     spec_time : Time.time, 
                     td_time : Time.time,
                     log_file : string}
                     
(* val tc_timer_raw = Config.declare_option "tc_timer";
ROOT.ML:val quick_and_dirty = Config.bool quick_and_dirty_raw;
goal.ML:  if Config.get ctxt quick_and_dirty then *)                     
*}

ML{* open Config ; Int 3; *}
(* Conclusion - bu: must be done with a global functor instatiation on 
   timer_config.  I temporarily leave the ref's here in order not
   to break to many interfaces ... bu
*)   

text{* Back to the original ...*}

ML {*
structure LogThy = 
struct


val tc_timer =  Unsynchronized.ref (Timer.startRealTimer ())
val spec_time = Unsynchronized.ref (Timer.checkRealTimer (!tc_timer))

val td_time = Unsynchronized.ref (Timer.checkRealTimer (!tc_timer))

val log_file = Unsynchronized.ref "";

fun start () = (spec_time := Timer.checkRealTimer (!tc_timer))

fun get_tc_delta () = Time.-(Timer.checkRealTimer (!tc_timer),!spec_time)
fun get_td_delta () = Time.-(Timer.checkRealTimer (!tc_timer),!td_time)

fun start_td_timer () = (td_time := Timer.checkRealTimer (!tc_timer))


fun set_log_file ctxt n = let
  val _ = if Config.get ctxt quick_and_dirty 
	  then () 
	  else ((log_file := n);())
  val today = (Date.toString(Date.fromTimeUniv (Time.now())))^" (UTC)";
  val hostname = the_default "hostname not set" (OS.Process.getEnv "HOSTNAME");
in
  if (!log_file) = "" 
  then ()
  else 
  File.write (Path.explode (!log_file)) 
  (  "# This file was generated automatically \n"
    ^"# by HOL-TestGen "^testgen_version^"\n"
    ^"# on "^today^"\n"
    ^"# Host: "^hostname^"\n"
    ^"# \n"
    ^"# theory,  test case name, type, num. of tests cases/data, time in seconds\n")
end

fun append s = if (!log_file) = "" then () else File.append (Path.explode (!log_file)) s



fun reset_log_file ctxt = set_log_file ctxt ""

fun log_thy ctxt thy = 
let
  val _ = set_log_file ctxt (thy^".csv")
  val _ = use_thy thy
  val _ = reset_log_file ctxt
in () end;

end

val log_thy = LogThy.log_thy

*}
end
