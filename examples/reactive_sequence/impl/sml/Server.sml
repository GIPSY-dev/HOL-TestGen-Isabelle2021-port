
(*****************************************************************************
 * HOL-TestGen --- theorem-prover based test case generation
 *                 http://www.brucker.ch/projects/hol-testgen/
 *                                                                            
 * Server.sml --- the "Sequence" example (SML version)
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
(* $Id: Server.sml 10002 2013-11-16 19:11:03Z brucker $ *)




structure server = struct

datatype vars = X | Y;
datatype data = Data;

datatype InEvent = req of int 
		 | reqA of vars
		 | send of data * int 
		 | sendA of data * vars 
		 | stop;

datatype OutEvent = port of int 
		  | portA of vars 
		  | ack;

fun vars2String X = "X"
  | vars2String Y = "Y"

fun InEvent2String (req x)   = "req("^(Int.toString x)^")"
  | InEvent2String (reqA x)  = "reqA("^(vars2String x)^")"
  | InEvent2String (send (x,y))  = "send(Data, port:"^(Int.toString y)^")"
  | InEvent2String (sendA x) = "sendA "
  | InEvent2String stop      = "stop  ";

fun OutEvent2String (port x)   = "port("^(Int.toString x)^")"
  | OutEvent2String (portA x)  = "portA("^(vars2String x)^")"
  | OutEvent2String  ack       = "ack"


fun implementation (req x)   = if (x-1) >=0 then port (x-1) else port 0
  | implementation (reqA x)  = ack
  | implementation (send x)  = ack
  | implementation (sendA x) = ack
  | implementation stop      = ack

fun implementation' (req x)   = port 5
  | implementation' (reqA x)  = ack
  | implementation' (send x)  = ack
  | implementation' (sendA x) = ack
  | implementation' stop      = ack

fun read event  =  
    let
	val _ = print ("received: "^(InEvent2String event))
        val ans = implementation event 
	val _ = print ("\t -> sending: "^(OutEvent2String ans)^("\n"))
    in
	ans
    end 


end
