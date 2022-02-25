theory Code_C_pthread
imports Main "../TestLib"
keywords  "gen_C_pthread" :: "qed_global"
begin

subsection {*C pthread Header term*}

ML {*

val next_line    = @{term "''~''"};

val stdio_term   = @{term "''#include <stdio.h>''"};
val stdlib_term  = @{term "''#include <stdlib.h>''"};
val pthread_term = @{term "''#include <pthread.h>''"}

val C_pthread_header = stdio_term $ stdlib_term $ pthread_term;

*}

subsection {*C instructions term*}
(*A C instruction can be a variable declaration or a call to another existing function or 
  affectation or conditional or a loop*)

subsection {*C functions term*}

ML {*
val next_instr    = @{term "'';''"};
val open_bracket  = @{term "''{''"};
val close_bracket = @{term "''}''"};
val next_arg      = @{term "'',''"}
val open_par      = @{term "''(''"};
val close_par     = @{term "'')''"};


fun C_function_header fun_type fun_name fun_args = fun_type $ fun_name $ fun_args;

fun discharge_intrs []                  = @{term"''/**/''"}
|   discharge_intrs [C_instr]           = C_instr $ next_instr $ next_line 
|   discharge_intrs (C_instr::C_instrs) = C_instr $ next_instr $ next_line $
                                          discharge_intrs C_instrs;

fun discharge_args []              = @{term"''/**/''"}
|   discharge_args [C_arg]         = C_arg $ next_arg  
|   discharge_args (C_arg::C_args) = C_arg $ next_arg $
                                          discharge_args C_args;

fun C_function fun_type fun_name fun_args C_instrs = 
      C_function_header fun_type fun_name (open_par $ discharge_args fun_args $ close_par) $ next_line $ 
      open_bracket $ next_line $  
      discharge_intrs C_instrs $ next_line $ 
      close_bracket $ next_line ;

fun C_void_function fun_name fun_args C_instrs = 
     C_function @{term"''void''"} fun_name fun_args C_instrs;

fun C_int_function fun_name fun_args C_instrs = 
     C_function @{term"''int''"} fun_name fun_args C_instrs;

fun C_string_function fun_name fun_args C_instrs = 
     C_function @{term"''string''"} fun_name fun_args C_instrs;

*}


subsection {*C File term*}

ML {*

fun discharge_funs []              = @{term"''/**/''"}
|   discharge_funs [C_fun]         = C_fun $ next_line  
|   discharge_funs (C_fun::C_funs) = C_fun $ next_line $
                                          discharge_funs C_funs;

fun C_file C_header C_funs  = C_header $ discharge_funs C_funs ;

*}

subsection {*Jump to the next line*}

ML {*  fun replace_next_line nil = [] 
      |  replace_next_line (x::xs) = (if x = #"~"    
                                      then replace_next_line (#"\n"::xs) 
                                      else x::replace_next_line xs); 
   *}

end
