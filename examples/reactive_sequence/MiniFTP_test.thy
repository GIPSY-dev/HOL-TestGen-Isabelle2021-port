(*****************************************************************************
 * HOL-TestGen --- theorem-prover based test case generation
 *                 http://www.brucker.ch/projects/hol-testgen/
 *                                                                            
 * MiniFTP_test.thy --- sequence testing 
 * This file is part of HOL-TestGen.
 *
 * Copyright (c) 2005-2007 ETH Zurich, Switzerland
 *               2009-2015 Achim D. Brucker, Germany
 *               2009-2015 Univ. Paris-Sud, France
 *               2016-2017 The Univeristy of Sheffield, UK
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
(* $Id: Sequence_test.thy 8455 2009-04-08 07:58:38Z wolff $ *)

chapter {* Reactive Sequence Testing *} 

theory MiniFTP_test 
imports
   Testing
begin

declare [[testgen_profiling]]

text{* 
  In this theory, we present a simple reactive system and
  demonstrate  how \testgen{} can be used for testing such
  systems.

  Our scenario is motivated by the following communcation scenario: A
  client sends a communication request to a server and specifies a
  port-range $X$. The server non-deterministically chooses a port $Y$
  which is within the specified range. The client sends a sequence of
  data (abstracted away in our example to a constant @{term "Data"})
  on the port allocated by the server.  The communication is
  terminated by the client with a @{term "stop"} event. Using a
  \textsc{csp}-like notation, we can describe such a system 
  as follows:
 % \begin{multiline} 
  $  \mathit{req}?X \rightarrow \mathit{port}?Y[Y < X]$
  $  \rightarrow$
  $  (\mathit{rec}\;N \bullet \mathit{send}!D,Y \rightarrow$
  $   \mathit{ack} \rightarrow N\; \Box\; \mathit{stop} \rightarrow$
  $   \mathit{ack} \rightarrow \mathit{SKIP}) \nonumber $
 % \end{multiline}
  It is necessary for our approach that the protocol strictly
  alternates client-side and server-side events; thus, we will be able
  to construct in a test of the server a step-function ioprog that stimulates the server with an input and records its
  result. If a protocol does not have alternation in its events, it
  must be constructed by artificial acknowledge events; it is then a
  question of their generation in the test harness if they are sent
  anyway or if they correspond to something like ``server reacted
  within timebounds.''

  The \emph{stimulation sequence} of the system under test results
  just from the projection of this protocol to the input events:
%  \begin{gather}
   $ \mathit{req}?X \rightarrow (\mathit{rec}\; N \bullet \mathit{send}!D,Y $
   $ \rightarrow N\;\Box\; \mathit{stop} \rightarrow \mathit{SKIP}) \nonumber$
%  \end{gather}
*}

subsubsection{* Basic Technique: Events with explicit variables 
*}

text{* 
  We define \emph{abstract traces} containing explicit variables $X$,
  $Y$, \ldots. The whole test case generation is done on the basis of
  the abstract traces. However, the additional functions
  $substitute$ and $bind$ are used to replace them with concrete
  values during the run of the test-driver, as well as programs that
  check pre- and postconditions on the concrete values occuring in the
  concrete run. 
*}

text{* 
  We specify explicit variables and a joined type containing abstract
  events (replacing values by explicit variables) as well as their
  concrete counterparts. 
*}

datatype vars = X | Y
datatype data = Data


type_synonym    chan = int (* just to make it executable *)

datatype InEvent_conc  = req  chan  | send  data chan | stop
datatype InEvent_abs   = reqA vars  | sendA data vars | stopA
datatype OutEvent_conc = port  chan | ack 
datatype OutEvent_abs  = portA vars | ackA   


definition lookup :: "['a \<rightharpoonup> 'b, 'a] \<Rightarrow> 'b"
  where "lookup env v \<equiv>  the(env v)"

definition success:: "'\<alpha> option \<Rightarrow> bool"
  where "success x \<equiv> case x of None => False | Some x => True"

type_synonym     InEvent    = "InEvent_abs  + InEvent_conc"
type_synonym     OutEvent   = "OutEvent_abs + OutEvent_conc"
type_synonym     event_abs  = "InEvent_abs  + OutEvent_abs"

declare [[testgen_depth=15]]





subsubsection{* The infrastructure of the observer: substitute and rebind 

*}

text{* 
  The predicate @{term "substitute"} allows for mapping abstract events
  containing explicit variables to concrete events by substituting the
  variables by values communicated in the system run. It requires an
  environment (``substitution'') where the concrete values occuring in
  the system run are assigned to variables.  
*}
fun substitute :: "[vars \<rightharpoonup> chan, InEvent_abs] \<Rightarrow> InEvent_conc"
where
  "substitute env (reqA v)    = req(lookup env v)"
| "substitute env (sendA d v) = send d (lookup env v)"
| "substitute env stopA       = InEvent_conc.stop"

text{* 
  The predicate @{term "rebind"} extracts from concrete output events
  the values and binds them to explicit variables in @{term "env"}. It should
  never be applied to abstract values; therefore, we we can use an
  underspecified version (undefined). The predicate @{term "rebind"}
  only stores $?$-occurrences in the protocol into the environment;
  $!$-occurences are ignored.  Events that are the same in the
  abstract as well as the concrete setting are treated as abstract
  events.
 
  In a way, @{term "rebind"} can be viewed as an abstraction of the
  concrete log produced at runtime.  
*}


fun rebind :: "[vars \<rightharpoonup> chan, OutEvent_conc] \<Rightarrow> vars \<rightharpoonup> chan"
where
  "rebind env (port n)           = env(Y \<mapsto> n)"
| "rebind env OutEvent_conc.ack  = env"


subsubsection{* Abstract Protocols and Abstract Stimulation Sequences 

*}

text{* 
  Now we encode the protocol automaton (abstract version) by a
  recursive acceptance predicate.  One could project the set of
  stimulation sequences just by filtering out the outEvents occuring
  in the traces.

  We will not pursue this approach since a more constructive
  presentation of the stimulation sequence set is advisable for
  testing.

  However, we show here how such concepts can be specified. 
*}
(*
text{* must be nat for stupid reasons; the rec-package only 
accepts data-types and not, e.g., int *}
*)

abbreviation A :: nat where "A == 0"
abbreviation B :: nat where "B == Suc A"
abbreviation C :: nat where "C == Suc B"
abbreviation D :: nat where "D == Suc C"
abbreviation E :: nat where "E == Suc D"

fun   accept' :: "nat \<Rightarrow> event_abs list \<Rightarrow> bool"
where (* accept' "measure(\<lambda> (x,y). length y)" *)
      "accept' A ((Inl(reqA X))#S)    = accept' B S"
   |   "accept' B ((Inr(portA Y))#S)   = accept' C S"
   |   "accept' C ((Inl(sendA d Y))#S) = accept' D S"
   |   "accept' D ((Inr(ackA))#S)      = accept' C S"
   |   "accept' C ((Inl(stopA))#S)     = accept' E S"
   |   "accept' E ([Inr(ackA)])        = True"
   |   "accept' x y                  = False"

abbreviation accept :: "event_abs list \<Rightarrow> bool"
where      "accept s \<equiv> accept' 0 s"

text{* 
  We proceed by modeling a subautomaton of the protocol automaton
  accept. 
*}

fun    stim_trace' :: "nat \<Rightarrow> InEvent_abs list \<Rightarrow> bool"
where "stim_trace' A ((reqA X)#S)    = stim_trace' C S"
    |  "stim_trace' C ((sendA d Y)#S) = stim_trace' C S"
    |  "stim_trace' C [stopA]          = True"
    |  "stim_trace' x y               = False"

definition stim_trace :: "InEvent_abs list \<Rightarrow> bool"
where     "stim_trace s \<equiv> stim_trace' A s"


subsubsection{* The Post-Condition *}

fun    postcond :: "(vars \<rightharpoonup> int) \<Rightarrow> '\<sigma> \<Rightarrow> InEvent_conc \<Rightarrow> OutEvent_conc \<Rightarrow> bool"
where "postcond env x (req n) (port m) = (m <= n)"
     |"postcond env x (send z n) (OutEvent_conc.ack) = (n = lookup env Y)"
     |"postcond env x (InEvent_conc.stop) (OutEvent_conc.ack)  = True"   
     |"postcond env x y z = False"

subsubsection{* Testing for successful system runs of the server under test *}

text{* 
  So far, we have not made any assumption on the state $\sigma'$ of
  the program under test ioprog. It could be a log of the
  actual system run. However, for simplicity, we use only a
  trivial state in this test specification.
*}

(*<*)
declare [[testgen_trace]]
(*>*)

subsubsection{* Test-Generation: The Standard Approach *}

consts ioprog :: 'a

declare stim_trace_def[simp]
(* declare valid_def[simp]   CAUSES BUG IN gen_test_cases TODO !!! *)

test_spec "stim_trace trace \<longrightarrow> 
           ((empty(X\<mapsto>init_value),()) \<Turnstile> (os\<leftarrow>(mbind trace ioprog);result(length trace = length os)))"
  apply(gen_test_cases 4 1 "ioprog" )
  mk_test_suite "reactive"


declare [[testgen_iterations=1000]]

subsubsection{* Test-Generation: Refined Approach involving TP *}

text{* 
  An analysis of the previous approach shows that random solving on
  trace patterns is obviously still quite ineffective. Although path
  coverage wrt. the input stimulation trace automaton can be achieved
  with a reasonable high probability, the depth remains limited.

  The idea is to produce a better test theorem by more specialized
  rules, that take the special form of the input stimulation protocol
  into account. 
*}
thm vars.exhaust
lemma start :
   "stim_trace' A (x#S) = ((x = reqA X) \<and> stim_trace' C S)"
apply(cases "x", simp_all)
by (metis (full_types) stim_trace'.simps(1) stim_trace'.simps(13) vars.exhaust)


lemma final[simp]:
"(stim_trace' x (stopA # S)) = ((x=C)\<and>(S=[]))"
apply(case_tac "x=Suc (Suc (A::nat))", simp_all)
apply(cases "S",simp_all)
apply(case_tac "x=Suc (A::nat)", simp_all)
apply(case_tac "x = (A::nat)", simp_all)
apply(subgoal_tac "\<exists> xa. x = Suc(Suc(Suc xa))",erule exE)
apply(simp)
apply(arith)
done

lemma step1 :
   "stim_trace' C (x#y#S) = ((x=sendA Data Y) \<and> stim_trace' C (y#S))"
apply(cases "x", simp_all)
by (metis data.exhaust stim_trace'.simps(2) stim_trace'.simps(8) vars.exhaust)


lemma step2: 
   "stim_trace' C [x] = (x=stopA)"
apply(cases "x", simp_all)
using stim_trace'.elims(2) by fastforce


text{* 
  The three rules $start$, $step1$ and $step2$ give us a translation
  of a constraint of the form $\mathrm{stim\_trace'}(x,[a,\ldots,b])$
  into a simple conjunction of equalities (in general: disjunction and
  existential quantifier will also occur). Since a formula of this
  form is an easy game for $fast\_tac$ inside $gen\_test\_cases$, we
  will get dramatically better test theorems, where the constraints
  have been resolved already.  
*}

text{* We reconfigure the rewriter: *}
declare start[simp] step1[simp] step2 [simp]

test_spec "stim_trace \<iota>s \<and> init_value > 0 \<longrightarrow> 
   ((empty(X\<mapsto>init_value),()) \<Turnstile> (os\<leftarrow>(mbind \<iota>s (observer2 rebind substitute postcond ioprog)); 
                                 return(length \<iota>s = length os)))"

  apply(gen_test_cases 40 1 "ioprog" )
mk_test_suite "reactive2"

text{* This results in the following test-space exploration:
\begin{verbatim}
 1. ([X \<mapsto> ?X2X2231], ()) ⊧ ( os \<leftarrow> mbind [reqA X, InEvent_abs.stop] (observer2 rebind substitute postcond ioprog); result length ?X1X2229 = length os)
 2. THYP ((\<exists>x xa. ([X \<mapsto> xa], ()) ⊧ ( os \<leftarrow> mbind [reqA X, InEvent_abs.stop] (observer2 rebind substitute postcond ioprog); result length x = length os)) \<longrightarrow>
          (\<forall>x xa. ([X \<mapsto> xa], ()) ⊧ ( os \<leftarrow> mbind [reqA X, InEvent_abs.stop] (observer2 rebind substitute postcond ioprog); result length x = length os)))
 3. ([X \<mapsto> ?X2X2217], ()) ⊧
    ( os \<leftarrow> mbind [reqA X, sendA Data Y, InEvent_abs.stop] (observer2 rebind substitute postcond ioprog); result length ?X1X2215 = length os)
 4. THYP ((\<exists>x xa. ([X \<mapsto> xa], ()) ⊧
                  ( os \<leftarrow> mbind [reqA X, sendA Data Y, InEvent_abs.stop] (observer2 rebind substitute postcond ioprog); result length x = length os)) \<longrightarrow>
          (\<forall>x xa. ([X \<mapsto> xa], ()) ⊧
                  ( os \<leftarrow> mbind [reqA X, sendA Data Y, InEvent_abs.stop] (observer2 rebind substitute postcond ioprog); result length x = length os)))
 5. ([X \<mapsto> ?X2X2203], ()) ⊧
    ( os \<leftarrow> mbind [reqA X, sendA Data Y, sendA Data Y, InEvent_abs.stop] (observer2 rebind substitute postcond ioprog); result length ?X1X2201 = length os)
 6. THYP ((\<exists>x xa. ([X \<mapsto> xa], ()) ⊧
                  ( os \<leftarrow> mbind [reqA X, sendA Data Y, sendA Data Y, InEvent_abs.stop]
                          (observer2 rebind substitute postcond ioprog); result length x = length os)) \<longrightarrow>
          (\<forall>x xa. ([X \<mapsto> xa], ()) ⊧
                  ( os \<leftarrow> mbind [reqA X, sendA Data Y, sendA Data Y, InEvent_abs.stop]
                          (observer2 rebind substitute postcond ioprog); result length x = length os)))
 7. ([X \<mapsto> ?X2X2189], ()) ⊧
    ( os \<leftarrow> mbind [reqA X, sendA Data Y, sendA Data Y, sendA Data Y, InEvent_abs.stop]
            (observer2 rebind substitute postcond ioprog); result length ?X1X2187 = length os)
 8. THYP ((\<exists>x xa. ([X \<mapsto> xa], ()) ⊧
                  ( os \<leftarrow> mbind [reqA X, sendA Data Y, sendA Data Y, sendA Data Y, InEvent_abs.stop]
                          (observer2 rebind substitute postcond ioprog); result length x = length os)) \<longrightarrow>
          (\<forall>x xa. ([X \<mapsto> xa], ()) ⊧
                  ( os \<leftarrow> mbind [reqA X, sendA Data Y, sendA Data Y, sendA Data Y, InEvent_abs.stop]
                          (observer2 rebind substitute postcond ioprog); result length x = length os)))
 9. ([X \<mapsto> ?X2X2175], ()) ⊧
    ( os \<leftarrow> mbind [reqA X, sendA Data Y, sendA Data Y, sendA Data Y, sendA Data Y, InEvent_abs.stop]
            (observer2 rebind substitute postcond ioprog); result length ?X1X2173 = length os)
\end{verbatim}

The subsequent test data generation is therefore an easy game. It essentially boils down to choosing a random value for each
meta-variable, which is trivial since these variables occur unconstrained.

*}
declare [[testgen_iterations=100]]

gen_test_data "reactive2"
print_conc_tests "reactive2"



declare [[testgen_wrapper=false]]
declare [[
  testgen_dataconv_code="
    fun sendToServer event Unity = let
      fun toServerData Data = server.Data
      fun toServerVars X    = server.X
        | toServerVars Y    = server.Y
      fun fromServerData server.Data = Data
      fun fromServerVars server.X    = X
        | fromServerVars server.Y    = Y
      fun convert_InEvent (req x)    = server.req x
        | convert_InEvent (send (x,y))  
                                = server.send  (toServerData x,y)
        | convert_InEvent stop      = server.stop 
      fun convert_OutEvent (server.port x)  = Some(port x,Unity)
        | convert_OutEvent server.ack       = Some(ack,Unity)
    in 
      convert_OutEvent (server.read (convert_InEvent event))
    end
"]]

generate_test_script "reactive2"

(* TODO Achim >>> 
code_const ioprog (SML "ioprog")

export_code reactive2.test_script in SML module_name Seq file "seq_script.sml"
 <<< TODO *)

text{* 
  Within the timeframe of 1 minute, we get trace lengths of about 40
  in the stimulation input protocol, which corresponds to traces of 80
  in the standard protocol. The examples shows, that it is not the
  length of traces that is a limiting factor of our approach. The main
  problem is the complexity in the stimulation automaton (size,
  branching-factors, possible instantiations of parameter input).
*}


end
