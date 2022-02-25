
(*****************************************************************************
 * HOL-TestGen --- theorem-prover based test case generation
 *                 http://www.brucker.ch/projects/hol-testgen/
 *                                                                            
 * clocks.ML  --- time measurements
 * This file is part of HOL-TestGen.
 *
 * Copyright (c) 2010 University Paris-Sud, France
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

signature CLOCKENV =
sig
    type clockenv
  
    val mt_clockenv        : clockenv
    val merge_clockenv     : clockenv * clockenv -> clockenv

    val text_stats         : clockenv -> string
    val latex_stats        : clockenv -> string

    val start_clock        : string -> clockenv -> clockenv
    val stop_clock         : string -> clockenv -> clockenv
    val next_clock         : clockenv -> clockenv

    val rename_clock       : string -> string -> clockenv -> clockenv
end

structure ClockEnv : CLOCKENV =
struct

structure IDtab =
  Table(type key = (string * int) list val ord = list_ord (prod_ord fast_string_ord int_ord));

val next_time_id = Unsynchronized.ref 0

fun add_time tab key time = let
    val fresh_id = !next_time_id
    val _ = next_time_id := !next_time_id + 1
in
    IDtab.map_default (key, Inttab.empty) (fn stats => Inttab.update_new (fresh_id, time) stats) tab
end

fun sum_times tab = let
    fun fold_tab stats = Inttab.fold (fn (_,time) => fn sum => time + sum) stats Time.zeroTime
    val tab' = IDtab.map (K fold_tab) tab
in
    IDtab.dest tab'
end

type clockinfo = {
     timer_stack   : Timer.real_timer list,
     id_stack      : (string * int) list,
     timetab       : Time.time Inttab.table IDtab.table,
     error_occurred : bool
}

datatype clockenv = Clockenv of clockinfo

fun rep_clockenv (Clockenv X) = X;
fun mk_clockenv  (X:clockinfo)= Clockenv X

val mt_clockenv = Clockenv{timer_stack = [],
			   id_stack = [],
			   timetab = IDtab.empty,
			   error_occurred = false};

fun merge_clockenv
   (Clockenv{timer_stack = ts,
	     id_stack = ids,
	     timetab = tt,
	     error_occurred = e},
    Clockenv{timer_stack = ts',
	     id_stack = ids',
	     timetab = tt',
	     error_occurred = e'}) = let

    fun merge_stats tab1 tab2 = Inttab.join (fn time_id => fn (x, y) => x) (tab1, tab2)
					    (* here we always have x = y for the same time_id *) 

in
    Clockenv{timer_stack = [],
	     id_stack = [],
	     timetab = IDtab.join (fn key => fn (x, y) => merge_stats x y) (tt, tt'),
	     error_occurred = e orelse e'}
end

fun clean str = String.translate (fn #" " =>  "_" | ch => String.str ch) str

fun string_of_id (name,n) = 
    if n = 0 then
	clean name
    else
	(clean name) ^ "_" ^ (Int.toString n)

fun text_stats' (Clockenv{timetab = tt,...}) = let
    fun string_of_ids ids = String.concatWith "/" (map string_of_id (rev ids))
    val maxlen = List.foldl Int.max 0 (map (size o string_of_ids) (IDtab.keys tt))
    val string_of_ids' = (StringCvt.padRight #" " maxlen) o string_of_ids
    fun string_of_entry (ids, time) = "Total time spent in " ^ (string_of_ids' ids) ^": " ^ (Time.toString time)
in
    String.concatWith "\n" (map string_of_entry (sum_times tt))
end

fun latex_tab entries = let
    fun string_of_ids ids = "\\protect\\path{" ^ (String.concatWith "/" (map string_of_id (rev ids))) ^ "}"
    fun string_of_entry (ids, time) = (string_of_ids ids) ^ " & " ^ (Time.toString time) ^ "\\\\ \n"
    val inner = String.concat (map string_of_entry entries)
    val headers = "Location & Time\\\\ \\hline\n"
in
    "\\begin{tabular}{l|r}\n" ^ headers ^ inner ^ "\\end{tabular}\n"
end

fun latex_stats' (Clockenv{timetab = tt,...}) = let
    val entries = sum_times tt
    fun toplevel_name entry = (fst o List.last o fst) entry
    val toplevel_names = distinct (op =) (map toplevel_name entries)
    fun has_name name entry = (toplevel_name entry) = name
    val sorted_entries = map (fn name => (name, filter (has_name name) entries)) toplevel_names
    fun latex_unit (name, entries) = "\\begin{table}\n\\centering"^ (latex_tab entries)
				     ^"\\caption{Time consumed by \\protect\\path{" ^ (clean name) ^ "}"
				     ^"\\label{tab:" ^ (clean name) ^ "}}\n\\end{table}\n%%%\n"
 
in
    (String.concatWith "\n%%%\n" (map latex_unit sorted_entries))^"\n"
end

fun check_error f clockenv =
    if #error_occurred (rep_clockenv clockenv) then
	"An error occurred during profiling."
    else
	f clockenv

val text_stats = check_error text_stats'
val latex_stats = check_error latex_stats'

fun start_id (Clockenv{timer_stack = ts, id_stack = ids, timetab= tt, error_occurred = e}) newid = 
    Clockenv{timer_stack = (Timer.startRealTimer ()) :: ts,
	     id_stack = newid :: ids,
	     timetab = tt,
	     error_occurred = e};

fun stop_id (Clockenv{timer_stack = ts, id_stack = ids, timetab= tt, error_occurred = e}) = let
    val (timer::timers) = ts
    val elapsed = Timer.checkRealTimer timer
    val (id::remaining_ids) = ids
in
    Clockenv{timer_stack = timers,
	     id_stack = remaining_ids,
	     timetab = add_time tt ids elapsed,
	     error_occurred = e}
end

fun rewrite_list find replace x = let
    val r = rev x
    val prefix = List.take (r, Int.min(length find, length r))
in
    if prefix = find then
	rev (replace @ (List.drop (r, length find)))
    else
	x
end

fun rename_id str (Clockenv{timer_stack = ts, id_stack = ids, timetab= tt, error_occurred = e}) = let
    val ((name, n)::remaining_ids) = ids
    val new_ids = (str,n)::remaining_ids
    fun rewrite_entry (key, value) = (rewrite_list ids new_ids key, value) 
in
    Clockenv{timer_stack = ts,
	     id_stack = new_ids,
	     timetab = IDtab.make (map rewrite_entry (IDtab.dest tt)),
	     error_occurred = e}
end


fun add_error (Clockenv{timer_stack = ts, id_stack = ids, timetab= tt, error_occurred = e}) =
    Clockenv{timer_stack = ts,
	     id_stack = ids,
	     timetab = tt,
	     error_occurred = true};

fun start_clock clockname clockenv = start_id clockenv (clockname, 0)

fun stop_clock clockname clockenv =
    if null (#timer_stack (rep_clockenv clockenv)) then
	add_error clockenv
    else let
	    val ((idname,_)::ids) = #id_stack (rep_clockenv clockenv)
	in
	    if idname = clockname then
		stop_id clockenv
	    else
		add_error clockenv
	end

fun next_clock clockenv =
    if null (#timer_stack (rep_clockenv clockenv)) then
	add_error clockenv
    else let
	    val ((clockname,n)::ids) = #id_stack (rep_clockenv clockenv)
	in
	    start_id (stop_id clockenv)(clockname,n+1)
	end

fun rename_clock oldname newname clockenv =
    if null (#timer_stack (rep_clockenv clockenv)) then
	add_error clockenv
    else let
	    val ((idname,_)::ids) = #id_stack (rep_clockenv clockenv)
	in
	    if idname = oldname then
		rename_id newname clockenv
	    else
		add_error clockenv
	end

end;

structure Clocks_DataManagement = Generic_Data
(
  type T = ClockEnv.clockenv
  val empty = ClockEnv.mt_clockenv
  fun extend T = T
  val merge = ClockEnv.merge_clockenv
);

(* FIXME ignored
  fun print sg ce = 
      (writeln "Runtime statistics:";
       writeln (ClockEnv.text_stats ce));
*)
     
signature CLOCKS =
sig
    val init_clocks     : theory -> unit
    val flush_clocks    : theory -> theory

    val start_clock     : string -> unit
    val stop_clock      : string -> unit
    val next_clock      : unit -> unit

    val start_clock_tac : string -> tactic
    val stop_clock_tac  : string -> tactic
    val next_clock_tac  : unit -> tactic

    val string_of_clocks: theory -> string
    val write_clocks    : theory -> string -> unit

    val rename_clock    : string -> string -> unit
end

structure Clocks : CLOCKS =
struct

val env_ref = Unsynchronized.ref ClockEnv.mt_clockenv

fun init_clocks thy = env_ref := Clocks_DataManagement.get(Context.Theory thy)

fun flush_clocks thy = Context.theory_of (Clocks_DataManagement.put (!env_ref) (Context.Theory thy))

fun start_clock name = env_ref := ClockEnv.start_clock name (!env_ref)

fun stop_clock name = env_ref := ClockEnv.stop_clock name (!env_ref)

fun next_clock () = env_ref := ClockEnv.next_clock (!env_ref)

fun start_clock_tac clockname thm = (start_clock clockname; all_tac thm)

fun stop_clock_tac clockname thm = (stop_clock clockname; all_tac thm)

fun next_clock_tac () thm = (next_clock (); all_tac thm)

fun rename_clock oldname newname = env_ref := ClockEnv.rename_clock oldname newname (!env_ref)

fun write_clocks thy fname = let
    val _ = init_clocks thy
    val to_write = ClockEnv.latex_stats (!env_ref)
    val _    = File.write (Path.explode fname) to_write;
in
    ()
end

fun string_of_clocks thy = (init_clocks thy; ClockEnv.text_stats (!env_ref))

fun start_clock_command clockname thy = let
    val result = Context.theory_of (Clocks_DataManagement.map (ClockEnv.start_clock clockname) (Context.Theory thy))
in
    (init_clocks result; result)
end

val _ = Outer_Syntax.command @{command_spec "start_clock"} "starts a clock for measuring runtime" 
			    (Parse.string >> (Toplevel.theory o start_clock_command));

fun stop_clock_command clockname thy = let
    val result = Context.theory_of (Clocks_DataManagement.map (ClockEnv.stop_clock clockname) (Context.Theory thy))
in
    (init_clocks result; result)
end

val _ = Outer_Syntax.command @{command_spec "stop_clock"} "stops a clock for measuring runtime" 
			    	(Parse.string >> (Toplevel.theory o stop_clock_command));

fun next_clock_command thy = let
    val result = Context.theory_of (Clocks_DataManagement.map ClockEnv.next_clock (Context.Theory thy))
in
    (init_clocks result; result)
end

val _ = Outer_Syntax.command @{command_spec "next_clock"} "increments the ID of the current clock" 
			    (Scan.succeed (Toplevel.theory next_clock_command));

fun print_clocks_command thy = (writeln (string_of_clocks thy); init_clocks thy; thy)

val _ = Outer_Syntax.command @{command_spec "print_clocks"} "print runtime statistics" 
			    (Scan.succeed (Toplevel.theory print_clocks_command));

fun write_clocks_command fname thy = (write_clocks thy fname; init_clocks thy; thy)

val _ = Outer_Syntax.command @{command_spec "write_clocks"} "write a table with the total runtimes measured to a file" 
			    (Parse.string >> (Toplevel.theory o write_clocks_command));
				    
end;
