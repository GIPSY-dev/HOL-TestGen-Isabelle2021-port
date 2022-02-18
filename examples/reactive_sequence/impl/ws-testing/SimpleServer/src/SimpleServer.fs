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
(* $Id: SimpleServer.fs 9071 2011-01-05 00:53:17Z brucker $ *)

namespace SequenceExample

  module SimpleServer = 
    type vars = X | Y
    type data = Data

    type InEvent = Req of int
                 | ReqA of vars
                 | Send of data * int
                 | SendA of data * vars
                 | Stop

    type OutEvent = Port of int 
                  | PortA of vars
                  | Ack

    let vars2String = function 
      | X -> "X"
      | Y -> "Y"

    let InEvent2String = function 
      | (Req x)      -> "req("+(string x)+")"
      | (ReqA x)     -> "reqA("+(vars2String x)+")"
      | (Send (x,y)) -> "send(Data, Port:"+(string y)+")"
      | (SendA _)    -> "sendA "
      | Stop         -> "stop  "

    let OutEvent2String = function 
      | (Port x)  -> "port("+(string x)+")"
      | (PortA x) -> "portA("+(vars2String x)+")"
      | Ack       -> "ack"


    let implementation = function 
      | (Req x)   -> if (x-1) >=0 then Port (x-1) else Port 0
      | (ReqA x)  -> Ack
      | (Send _)  -> Ack
      | (SendA _) -> Ack
      | Stop      -> Ack

    let implementation' = function 
      | (Req x)   -> Port 5
      | (ReqA x)  -> Ack
      | (Send _)  -> Ack
      | (SendA _) -> Ack
      | Stop      -> Ack

    let read event = let _   = System.Console.Write ("received: "+(InEvent2String event))
                     let ans = implementation event
                     let _   = System.Console.Write ("\t -> Sending: "+(OutEvent2String ans)+("\n"))
                     ans
