theory Code_gdb_script
imports Main "../TestLib"
(*keywords  "gen_gdb_script" :: "qed_global"*)
begin

datatype  gdb_comand =     
   break string gdb_comand
 | commands gdb_comand
 | silent  gdb_comand
 | continue gdb_comand
 | thread   gdb_comand
 | "end"    gdb_comand 
 | sharp string
 |start

datatype gdb_option =
  logging gdb_option
 |on
 |off
 |pagination gdb_option
 |"file" string
 |print gdb_option

              

subsection {*writing on file using Isabelle/ML*}
ML{*
     val file_path_try = "../../add-ons/OS-IFP-test/OS_kernel_model/IPC/example_gdb_impl/c/yakoub.gdb"
                         |> Path.explode 
                         |> Path.append (Resources.master_directory @{theory });
    val file_check =  file_path_try |> File.exists; 
    (*val file_write = File.write file_path_office "#yakoub";*) 

*}

(*Generation of a set of gdb files*)

ML{*
    fun writeFiles  _ _ [] = []  
   |   writeFiles  filePath fileExtension (gdb_script :: gdb_script_list) = 
         ([filePath] @ [(gdb_script :: gdb_script_list) |> length |> Int.toString] @ 
          [fileExtension] |> String.concat |> Path.explode |> File.write_list) gdb_script::
         writeFiles filePath fileExtension gdb_script_list;
   *}
(*master parth*)
ML{* (*Thy_Load.master_directory*)
  Resources.master_directory @{theory};
    *}
ML {*Resources.master_directory @{theory};
   fun masterPath_add theory  Path = Path
                            |> Path.explode 
                            |> Path.append (Resources.master_directory theory)
                            |> Path.implode;
   *}

subsection {*Printing a list of terms in column using Pretty*}
ML{*
    fun pretty_terms' context terms = terms |> (Syntax.pretty_term context 
                                            |> List.map)
                                            |> Pretty.chunks;

     Pretty.writeln (pretty_terms' @{context} [@{term "2::int"}, @{term "2::int"}]);    
  *}

subsection {*Going from a list of terms to ASCII string*}
ML {*(*fun render_thm ctxt thm =
     Print_Mode.setmp ["xsymbols"]
    (fn _ => Display.pretty_thm ctxt thm
             |> Pretty.str_of
             |> YXML.parse_body
             |> XML.content_of) ();
    render_thm @{context} @{thm "conjI"};*)
    fun render_term ctxt term =
     Print_Mode.setmp ["xsymbols"]
    (fn _ =>  Syntax.pretty_term ctxt term
             |> Pretty.string_of
             |> YXML.parse_body
             |> XML.content_of) ();

   render_term @{context} @{term "1::int"};

   fun render_term_list ctxt term =
     Print_Mode.setmp ["xsymbols"]
    (fn _ =>  pretty_terms' ctxt term
             |> Pretty.string_of
             |> YXML.parse_body
             |> XML.content_of) ();
   render_term_list @{context} [@{term "1::int"}, @{term "1::int"}];  
*}

subsection {*GDB terms script to control scheduler*}

ML {*val gdb_header =  
         @{term "''#setting gdb options''"} $ @{term "''{''"} $
         @{term "set"} $ @{term "logging (file ''Example_sequential.log'')"} $ @{term "''{''"} $
         @{term "set"} $ @{term "logging on"} $ @{term "''{''"} $
         @{term "set"} $ @{term "pagination off"} $ @{term "''{''"} $
         @{term "set ''target-async''"} $ @{term " on"} $ @{term "''{''"} $
         @{term "set ''non-stop''"} $ @{term " on"} $ @{term "''{''"} $
         @{term "set ''print thread-events off''"} $ @{term "''{''"} $ @{term "''{''"}
         ;
 
     fun gdb_break_point_entry fun_nam_term thread_id_term = 
         @{term "''#setting thread entry''"} $ @{term "''{''"} $
         @{term "break"}  $ fun_nam_term $ @{term "''{''"} $ 
         @{term "commands"} $ @{term "''{''"} $ 
         @{term "silent"} $ @{term "''{''"} $  
         @{term "thread"} $ thread_id_term $ @{term "''{''"} $
         @{term "continue"} $ @{term "''{''"} $
         @{term "end"} $ @{term "''{''"} $ @{term "''{''"};
      
   
     fun gdb_break_point_exist line_number_term thread_id_term = 
         @{term "''#setting thread exit''"} $ @{term "''{''"} $
         @{term "break"}  $ line_number_term $ @{term "''{''"} $ 
         @{term "commands"} $ @{term "''{''"} $ 
         @{term "silent"} $ @{term "''{''"} $  
         @{term "thread"} $ thread_id_term $ @{term "''{''"} $
         @{term "continue"} $ @{term "''{''"} $
         @{term "end"} $ @{term "''{''"} $ @{term "''{''"};
    
     fun gdb_break_main_entry fun_nam_term  = 
         @{term "''#setting main thread entry''"} $ @{term "''{''"} $
         @{term "break"}  $ fun_nam_term $ @{term "''{''"} $ 
         @{term "commands"} $ @{term "''{''"} $ 
         @{term "silent"} $ @{term "''{''"} $  
         @{term "set"} $ @{term "''scheduler-locking''"} $ @{term " on"} $ @{term "''{''"} $
         @{term "continue"} $ @{term "''{''"} $
         @{term "end"} $ @{term "''{''"} $ @{term "''{''"};
      
      fun gdb_break_main_exit line_number_term thread_id_term = 
         @{term "''#wait for thread creation''"} $ @{term "''{''"} $
         @{term "break"}  $ line_number_term $ @{term "''{''"} $ 
         @{term "commands"} $ @{term "''{''"} $ 
         @{term "silent"} $ @{term "''{''"} $  
         @{term "thread"} $ thread_id_term $ @{term "''{''"} $
         @{term "continue"} $ @{term "''{''"} $
         @{term "end"} $ @{term "''{''"} $ @{term "''{''"};
      
     val gdb_start_term = @{term "start"} $ @{term "''{''"};
     
     val gdb_endFile =  @{term "''#endFile''"}

*}
 
ML {* gdb_header*}

subsection {*removing quotes and parentheses from ASCII string*}
ML {*  fun remove_char nil = [] 
      |  remove_char (x::xs) = (if ((x = #"(" orelse x = #")") orelse x = #"'")   
                                then remove_char xs 
                                else x::remove_char xs); 
   *}

subsection {*Jump to the next line*}

ML {*  fun next_line nil = [] 
      |  next_line (x::xs) = (if x = #"{"    
                              then next_line (#"\n"::xs) 
                              else x::next_line xs); 
   *}

subsection {*Going from a simple list to a list of terms*}

ML {*render_term_list @{context} [@{term " ''{''"}]*}

subsection {*Terms constructors and scheme destructors*}

ML{*
  fun thm_to_term thm = thm 
                        |> Thm.concl_of |> HOLogic.dest_Trueprop;
  fun thms_to_terms thms = thms 
                           |> (thm_to_term |> map);
 
  fun dest_valid_SE_term terms = terms |> ((fn term => case term of 
                                            ((Const(@{const_name "valid_SE"},_) $ _) 
                                             $(Const(@{const_name "bind_SE"},_) $ T $ _)) => T
                                                       | _ => term) 
                                           |> map);

  fun dest_mbind_term terms = terms |> ((fn term => case term of 
                                                   Const (@{const_name "mbind"}, _) 
                                                   $ LIST $ _ => LIST
                                                    |_ => term )
                                       |> map);

  fun dest_mbind_term' terms = terms |> ((fn term => case term of 
                                                   Const (@{const_name "mbind'"}, _) 
                                                   $ LIST $ _ => LIST
                                                    |_ => term )
                                       |> map);

  fun dest_List_term terms = terms |> ((fn term => HOLogic.dest_list term) |> map);
 
  *}

subsection {*From a test thm to terms of input sequences*}

ML {*fun thm_to_inputSeqTerms test_facts = 
          test_facts  
          |> thms_to_terms |> dest_valid_SE_term 
          |> dest_mbind_term |> dest_List_term;

    fun thm_to_inputSeqTerms' test_facts = 
          test_facts  
          |> thms_to_terms |> dest_valid_SE_term 
          |> dest_mbind_term' |> dest_List_term;
  *}
subsection {*from input seuquences to strings*}

ML {* fun inputSeq_to_gdbStrings actTerm_to_gdbTerm inputSeqTerms  = 
          inputSeqTerms
          |> ((fn terms => [gdb_header] 
                           @(terms |> (actTerm_to_gdbTerm |> map))
                           @[gdb_start_term]
                           |> (render_term @{context} |> map)) 
                                |> map);

   fun 
   breakpoint_setup (term::terms) = 
   ((term::terms) |> length) :: (terms |> breakpoint_setup)   ;  
  
  *}

ML {*open List*}
ML {*open HOLogic;*}
subsection {*from sequeces of strings to a gdb script*}

ML {* fun gdbStrings_to_gdbScripts gdbStrings =
          gdbStrings     
          |> ((fn strings => strings
                             |> (String.implode o next_line o 
                                 remove_char o String.explode |> map)) 
               |> map);
  *}


subsection{*concat terms*}
ML {*
fun add_entry_exist_terms [] [] = []
    |   add_entry_exist_terms terms [] = terms
    |   add_entry_exist_terms [] terms = terms
    |   add_entry_exist_terms (term :: terms) (term'::terms') = 
        term $ term':: add_entry_exist_terms terms terms';

    fun add_entry_exist_termsS [] [] = []
    |   add_entry_exist_termsS termsS [] = termsS
    |   add_entry_exist_termsS [] termsS = termsS
    |   add_entry_exist_termsS (terms :: termsS) (terms'::termsS') = 
        add_entry_exist_terms terms terms'::add_entry_exist_termsS termsS termsS';

    fun add_entry_exist_termsS' [] [] = []
    |   add_entry_exist_termsS' termsS [] = termsS
    |   add_entry_exist_termsS' [] termsS = termsS
    |   add_entry_exist_termsS' (terms :: termsS) (terms'::termsS') = 
        (terms @ terms')::add_entry_exist_termsS' termsS termsS';

*}

subsection {*from thms to gdb scripts*}

ML {*
fun thms_to_gdbScripts inputSeq_to_gdbEn inputSeq_to_gdbEx inputSeq_to_gdbMain infos thms =
    thms 
    |> thm_to_inputSeqTerms
    |> ((fn terms => inputSeq_to_gdbMain infos terms) |> map)
    |> add_entry_exist_termsS'
       (thms |> thm_to_inputSeqTerms |> ((fn terms => inputSeq_to_gdbEx infos terms)|> map))
    |> add_entry_exist_termsS
       (thms |> thm_to_inputSeqTerms |> ((fn terms => inputSeq_to_gdbEn infos terms)|> map))
    |> inputSeq_to_gdbStrings (fn term => term)
                      |> gdbStrings_to_gdbScripts;

fun thms_to_gdbScripts' inputSeq_to_gdbEn inputSeq_to_gdbEx inputSeq_to_gdbMain infos thms =
    thms 
    |> thm_to_inputSeqTerms'
    |> ((fn terms => inputSeq_to_gdbMain infos terms) |> map)
    |> add_entry_exist_termsS'
       (thms |> thm_to_inputSeqTerms' |> ((fn terms => inputSeq_to_gdbEx infos terms)|> map))
    |> add_entry_exist_termsS
       (thms |> thm_to_inputSeqTerms' |> ((fn terms => inputSeq_to_gdbEn infos terms)|> map))
    |> inputSeq_to_gdbStrings (fn term => term)
                      |> gdbStrings_to_gdbScripts;

*}



subsection {*isa markup*}

ML {*  

    fun gen_gdb_scripts 
        inputSeq_to_gdbEn inputSeq_to_gdbEx inputSeq_to_gdbMain infos theory path thms =
        thms 
        |> thms_to_gdbScripts inputSeq_to_gdbEn inputSeq_to_gdbEx inputSeq_to_gdbMain infos
        |> writeFiles (path |> masterPath_add theory) ".gdb";


    (*For mbind'*)
    fun gen_gdb_scripts' 
        inputSeq_to_gdbEn inputSeq_to_gdbEx inputSeq_to_gdbMain infos theory path thms =
        thms 
        |> thms_to_gdbScripts' inputSeq_to_gdbEn inputSeq_to_gdbEx inputSeq_to_gdbMain infos
        |> writeFiles (path |> masterPath_add theory) ".gdb";
    

 (* val _ = Outer_Syntax.command  
              @{command_spec "gen_gdb_script"} 
              "store test state (theorem)"
              ;*)

  (*For mbind*)

  (*val gen_gdb_script = @{thms mykeos_simple.test_data} 
                          |> thm_to_inputSeqTerms 
                          |> inputSeq_to_gdbStrings actTerm_to_gdbTerm
                          |> gdbStrings_to_gdbScripts*)

*}

end
