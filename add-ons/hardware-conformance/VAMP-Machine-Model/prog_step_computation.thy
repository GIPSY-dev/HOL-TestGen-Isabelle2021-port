(**
 * Copyright (c) 2005-2007 Dirk Leinenbach, Alexandra Tsyban.
 * Some rights reserved, Saarland University.
 *
 * This work is licensed under the German-Jurisdiction Creative Commons
 * Attribution Non-commercial Share Alike 2.0 License.
 * See the file LIZENZ for a full copy of the license.
**)
(* $Id: prog_step_computation.thy 23139 2008-04-15 09:23:56Z AlexandraTsyban $ *)
theory prog_step_computation imports ASMcore_consis begin

declare Let_def[simp]

section {* moved from @{text prog_step_computation} for C0A semantics *}

definition is_not_contr_flow_instr :: "instr \<Rightarrow> bool"
where
  "is_not_contr_flow_instr iw \<equiv> \<exists> RD rs RS1 RS2 SA imm. 
                          iw \<in> {Iaddo RD RS1 RS2, Iadd RD RS1 RS2, Iaddio RD rs imm, Iaddi RD rs imm, 
                                Isubo RD RS1 RS2, Isub RD RS1 RS2, Isubio RD rs imm, Isubi RD rs imm, 
                                Iand RD RS1 RS2, Iandi RD rs imm, Ior RD RS1 RS2, Iori RD rs imm, Ixor RD RS1 RS2, Ixori RD rs imm, 
                                Isgr RD RS1 RS2, Iseq RD RS1 RS2, Isge RD RS1 RS2, Isls RD RS1 RS2, Isne RD RS1 RS2, Isle RD RS1 RS2,
                                Islsi RD rs imm,
                                Isll RD RS1 RS2, Islli RD rs SA, Isrl RD RS1 RS2, Isrli RD rs SA,
                                Ilhgi RD imm,
                                Ilw RD rs imm, Isw RD rs imm,
                                Imovi2s SA rs, Imovs2i RD SA}"

definition  is_ass_seq_instr :: "instr \<Rightarrow> bool"
where
  "is_ass_seq_instr iw \<equiv> is_instr iw \<and> is_not_contr_flow_instr iw \<and> (is_Imovi2s iw \<longrightarrow> sa_arg iw \<noteq> SPR_MODE)"

primrec rd_form :: "[regname, instr, int, int, int, int, int] \<Rightarrow> int"
where
  "rd_form r (Iaddo rd rs1 rs2) rs1p rs2p rp sr cell = ( if r = 0 then 0 else if r = rd then int_add rs1p rs2p else rp )"
 | "rd_form r (Iadd rd rs1 rs2) rs1p rs2p rp sr cell = ( if r = 0 then 0 else if r = rd then int_add rs1p rs2p else rp )"
 | "rd_form r (Iaddio rd rs imm) rs1p rs2p rp sr cell = ( if r = 0 then 0 else if r = rd then int_add rs1p imm  else rp )"
 | "rd_form r (Iaddi rd rs imm) rs1p rs2p rp sr cell = ( if r = 0 then 0 else if r = rd then int_add rs1p imm  else rp )"
 | "rd_form r (Isubo rd rs1 rs2) rs1p rs2p rp sr cell = ( if r = 0 then 0 else if r = rd then int_sub rs1p rs2p else rp )"
 | "rd_form r (Isub rd rs1 rs2) rs1p rs2p rp sr cell = ( if r = 0 then 0 else if r = rd then int_sub rs1p rs2p else rp )"
|  "rd_form r (Isubio rd rs imm) rs1p rs2p rp sr cell = ( if r = 0 then 0 else if r = rd then int_sub rs1p imm  else rp )"
 | "rd_form r (Isubi rd rs imm) rs1p rs2p rp sr cell = ( if r = 0 then 0 else if r = rd then int_sub rs1p imm  else rp )"

 | "rd_form r (Iand rd rs1 rs2) rs1p rs2p rp sr cell = ( if r = 0 then 0 else if r = rd then s_and rs1p rs2p else rp )"
 | "rd_form r (Iandi rd rs imm) rs1p rs2p rp sr cell = ( if r = 0 then 0 else if r = rd then s_and rs1p imm  else rp )"
 | "rd_form r (Ior rd rs1 rs2)  rs1p rs2p rp sr cell = ( if r = 0 then 0 else if r = rd then s_or  rs1p rs2p else rp )"
 | "rd_form r (Iori rd rs imm)  rs1p rs2p rp sr cell = ( if r = 0 then 0 else if r = rd then s_or  rs1p imm  else rp )"
 | "rd_form r (Ixor rd rs1 rs2) rs1p rs2p rp sr cell = ( if r = 0 then 0 else if r = rd then s_xor rs1p rs2p else rp )"
 | "rd_form r (Ixori rd rs imm) rs1p rs2p rp sr cell = ( if r = 0 then 0 else if r = rd then s_xor rs1p imm  else rp )"

 | "rd_form r (Isgr rd rs1 rs2) rs1p rs2p rp sr cell = ( if r = 0 then 0 else if r = rd then (if rs2p < rs1p then 1 else 0) else rp )"
 | "rd_form r (Iseq rd rs1 rs2) rs1p rs2p rp sr cell = ( if r = 0 then 0 else if r = rd then (if rs1p = rs2p then 1 else 0) else rp )"
 | "rd_form r (Isge rd rs1 rs2) rs1p rs2p rp sr cell = ( if r = 0 then 0 else if r = rd then (if rs2p \<le> rs1p then 1 else 0) else rp )"
 | "rd_form r (Isls rd rs1 rs2) rs1p rs2p rp sr cell = ( if r = 0 then 0 else if r = rd then (if rs1p < rs2p then 1 else 0) else rp )"
 | "rd_form r (Isne rd rs1 rs2) rs1p rs2p rp sr cell = ( if r = 0 then 0 else if r = rd then (if rs1p \<noteq> rs2p then 1 else 0) else rp )"
 | "rd_form r (Isle rd rs1 rs2) rs1p rs2p rp sr cell = ( if r = 0 then 0 else if r = rd then (if rs1p \<le> rs2p then 1 else 0) else rp )"
 | "rd_form r (Islsi rd rs imm) rs1p rs2p rp sr cell = ( if r = 0 then 0 else if r = rd then (if rs1p < imm  then 1 else 0) else rp )"

 | "rd_form r (Isll rd rs1 rs2) rs1p rs2p rp sr cell = ( if r = 0 then 0 else if r = rd then rs1p \<lless>\<^bsub>s/32\<^esub> intwd_as_nat rs2p mod 32 else rp )"
 | "rd_form r (Islli rd rs sa)  rs1p rs2p rp sr cell = ( if r = 0 then 0 else if r = rd then rs1p \<lless>\<^bsub>s/32\<^esub> sa else rp )"
 | "rd_form r (Isrl rd rs1 rs2) rs1p rs2p rp sr cell = ( if r = 0 then 0 else if r = rd then rs1p \<ggreater>\<^bsub>s/32\<^esub> intwd_as_nat rs2p mod 32 else rp )"
 | "rd_form r (Isrli rd rs sa)  rs1p rs2p rp sr cell = ( if r = 0 then 0 else if r = rd then rs1p \<ggreater>\<^bsub>s/32\<^esub> sa else rp )"

 | "rd_form r (Ilhgi rd imm) rs1p rs2p rp sr cell = (if r = 0 then 0 else if r = rd then imm * 2^16 else rp)"

 | "rd_form r (Ilw rd rs imm) rs1p rs2p rp sr cell = ( if r = 0 then 0 else if r = rd then cell else rp )"
 | "rd_form r (Isw rd rs imm) rs1p rs2p rp sr cell = rp"

 | "rd_form r (Imovi2s sa rs) rs1p rs2p rp sr cell = rp"
 | "rd_form r (Imovs2i rd sa) rs1p rs2p rp sr cell = ( if r = 0 then 0 else if r = rd then sr else rp )"

primrec cell_form :: "[nat, instr, int, int, int] \<Rightarrow> int"
where
  "cell_form ad (Iaddo rd rs1 rs2) rsp rdp cell = cell"
 | "cell_form ad (Iadd rd rs1 rs2) rsp rdp cell = cell"
 | "cell_form ad (Iaddio rd rs imm) rsp rdp cell = cell"
 | "cell_form ad (Iaddi rd rs imm) rsp rdp cell = cell"
 | "cell_form ad (Isubo rd rs1 rs2) rsp rdp cell = cell"
 | "cell_form ad (Isub rd rs1 rs2) rsp rdp cell = cell"
 | "cell_form ad (Isubio rd rs imm) rsp rdp cell = cell"
 | "cell_form ad (Isubi rd rs imm) rsp rdp cell = cell"

 | "cell_form ad (Iand rd rs1 rs2) rsp rdp cell = cell"
 | "cell_form ad (Iandi rd rs imm) rsp rdp cell = cell"
 | "cell_form ad (Ior rd rs1 rs2)  rsp rdp cell = cell"
 | "cell_form ad (Iori rd rs imm)  rsp rdp cell = cell"
 | "cell_form ad (Ixor rd rs1 rs2) rsp rdp cell = cell"
 | "cell_form ad (Ixori rd rs imm) rsp rdp cell = cell"

 | "cell_form ad (Isgr rd rs1 rs2) rsp rdp cell = cell"
 | "cell_form ad (Iseq rd rs1 rs2) rsp rdp cell = cell"
 | "cell_form ad (Isge rd rs1 rs2) rsp rdp cell = cell"
 | "cell_form ad (Isls rd rs1 rs2) rsp rdp cell = cell"
 | "cell_form ad (Isne rd rs1 rs2) rsp rdp cell = cell"
 | "cell_form ad (Isle rd rs1 rs2) rsp rdp cell = cell"
 | "cell_form ad (Islsi rd rs imm) rsp rdp cell = cell"

 | "cell_form ad (Isll rd rs1 rs2) rsp rdp cell = cell"
 | "cell_form ad (Islli rd rs sa)  rsp rdp cell = cell"
 | "cell_form ad (Isrl rd rs1 rs2) rsp rdp cell = cell"
 | "cell_form ad (Isrli rd rs sa)  rsp rdp cell = cell"

 | "cell_form ad (Ilhgi rd imm)    rsp rdp cell = cell"

 | "cell_form ad (Ilw rd rs imm)   rsp rdp cell = cell"
 | "cell_form ad (Isw rd rs imm)   rsp rdp cell = ( if ad = fit_nat (intwd_as_nat rsp + intwd_as_nat imm) then rdp else cell )"

 | "cell_form ad (Imovi2s sa rs)   rsp rdp cell = cell"
 | "cell_form ad (Imovs2i rd sa)   rsp rdp cell = cell"

primrec sr_form :: "[nat, instr, int, int] \<Rightarrow> int"
where
  "sr_form r (Iaddo rd rs1 rs2) rsp sr = sr"
 | "sr_form r (Iadd rd rs1 rs2) rsp sr = sr"
 | "sr_form r (Iaddio rd rs imm) rsp sr = sr"
 | "sr_form r (Iaddi rd rs imm) rsp sr = sr"
 | "sr_form r (Isubo rd rs1 rs2) rsp sr = sr"
 | "sr_form r (Isub rd rs1 rs2) rsp sr = sr"
 | "sr_form r (Isubio rd rs imm) rsp sr = sr"
 | "sr_form r (Isubi rd rs imm) rsp sr = sr"

 | "sr_form r (Iand rd rs1 rs2) rsp sr = sr"
 | "sr_form r (Iandi rd rs imm) rsp sr = sr"
 | "sr_form r (Ior rd rs1 rs2)  rsp sr = sr"
 | "sr_form r (Iori rd rs imm)  rsp sr = sr"
 | "sr_form r (Ixor rd rs1 rs2) rsp sr = sr"
|  "sr_form r (Ixori rd rs imm) rsp sr = sr"

 | "sr_form r (Isgr rd rs1 rs2) rsp sr = sr"
 | "sr_form r (Iseq rd rs1 rs2) rsp sr = sr"
 | "sr_form r (Isge rd rs1 rs2) rsp sr = sr"
 | "sr_form r (Isls rd rs1 rs2) rsp sr = sr"
 | "sr_form r (Isne rd rs1 rs2) rsp sr = sr"
 | "sr_form r (Isle rd rs1 rs2) rsp sr = sr"
 | "sr_form r (Islsi rd rs imm) rsp sr = sr"

 | "sr_form r (Isll rd rs1 rs2) rsp sr = sr"
 | "sr_form r (Islli rd rs sa)  rsp sr = sr"
 | "sr_form r (Isrl rd rs1 rs2) rsp sr = sr"
  |"sr_form r (Isrli rd rs sa)  rsp sr = sr"

 | "sr_form r (Ilhgi rd imm)    rsp sr = sr"

  |"sr_form r (Ilw rd rs imm)   rsp sr = sr"
  |"sr_form r (Isw rd rs imm)   rsp sr = sr"

 | "sr_form r (Imovi2s sa rs)   rsp sr = ( if r = sa then rsp else sr )"
 | "sr_form r (Imovs2i rd sa)   rsp sr = sr"

primrec reg_or_mem_cont_rec :: "[ASMcore_t, regname, regname, nat, instr list, bool, bool] \<Rightarrow> int"
where
  "reg_or_mem_cont_rec d gr sr ad [] gpr_not_spr reg_not_mem =
   (
     case reg_not_mem of
       True 
         \<Rightarrow> (
              case gpr_not_spr of
                True \<Rightarrow> reg (gprs d) gr
              |
                False \<Rightarrow> (sprs d) ! sr
            )
     |
       False \<Rightarrow> data_mem_read (mm d) ad
   )"
 | "reg_or_mem_cont_rec d gr sr ad (y # ys) gpr_not_spr reg_not_mem =
   (
     let
       rs1p  = reg_or_mem_cont_rec d (RS1_arg y) 0 0 ys True True;
       rs2p  = reg_or_mem_cont_rec d (RS2_arg y) 0 0 ys True True;
       rdp   = reg_or_mem_cont_rec d (RD_arg y)  0 0 ys True True;
       rp    = reg_or_mem_cont_rec d gr 0 0 ys True True;
       sri   = reg_or_mem_cont_rec d 0 (sa_arg y) 0 ys False True;
       srp   = reg_or_mem_cont_rec d 0 sr 0 ys False True;
       celli = reg_or_mem_cont_rec d 0 0 (fit_nat (intwd_as_nat rs1p + intwd_as_nat (imm_arg y))) ys False False;
       cellp = reg_or_mem_cont_rec d 0 0 ad ys False False
     in
       (
         case reg_not_mem of
           True
             \<Rightarrow> (
                  case gpr_not_spr of
                    True \<Rightarrow> rd_form gr y rs1p rs2p rp sri celli
                  |
                    False \<Rightarrow> sr_form sr y rs1p srp
                )
         |
           False \<Rightarrow> cell_form ad y rs1p rdp cellp
       )
   )"

definition reg_or_mem_cont :: "[ASMcore_t, regname, regname, nat, instr list, bool, bool] \<Rightarrow> int"
where
  "reg_or_mem_cont d gr sr ad ys gpr_not_spr reg_not_mem \<equiv> reg_or_mem_cont_rec d gr sr ad ys gpr_not_spr reg_not_mem"

definition is_loadw :: "instr \<Rightarrow> bool"
where
 "is_loadw iw \<equiv> \<exists> rd rs imm. iw = Ilw rd rs imm"

primrec not_change_code :: "[ASMcore_t, nat, nat, instr list, instr list] \<Rightarrow> bool"
where
  "not_change_code d low_border code_size ys [] = True"
 | "not_change_code d low_border code_size ys (x#xs) =
     (
        (
          let
            target = fit_nat (intwd_as_nat (reg_or_mem_cont d (RS1_arg x) 0 0 ys True True) + intwd_as_nat (imm_arg x))
          in
            (is_storew x \<longrightarrow> low_border + code_size \<le> target \<or> target < low_border)
           \<and>
            ((is_storew x \<or> is_loadw x) \<longrightarrow> 4 dvd target)
        )
      \<and>
        not_change_code d low_border code_size (x # ys) xs
     )"

definition  not_change_seq_code :: "[ASMcore_t, nat, nat, nat] \<Rightarrow> bool"
where
  "not_change_seq_code d low_border code_size n \<equiv> 
     (
       low_border + code_size + 8 \<le> 2^wlen_bit
     \<and>
       dpc d + 4 * n \<le> low_border + code_size
     \<and>
       low_border \<le> dpc d
     \<and>
       ( 
         let 
           code = get_instr_list (mm d) (dpc d) n
         in
           list_all is_ass_seq_instr code
          \<and>
           not_change_code d low_border code_size [] code
       )
     )"

definition gpr_consis :: "[ASMcore_t, instr list, registers] \<Rightarrow> bool"
where
  "gpr_consis d ys gpr_d \<equiv> (\<forall> r. reg gpr_d r = reg_or_mem_cont d r 0 0 ys True True)"

definition  spr_consis :: "[ASMcore_t, instr list, registers] \<Rightarrow> bool"
where  "spr_consis d ys spr_d \<equiv> (\<forall> r. spr_d ! r = reg_or_mem_cont d 0 r 0 ys False True)"

definition mem_consis :: "[ASMcore_t, instr list, mem_t] \<Rightarrow> bool"
where
  "mem_consis d ys mm_d \<equiv> (\<forall> ad. mm_d ad = data2cell (reg_or_mem_cont d 0 0 (4 * ad) ys False False))"

subsection {* Program steps computation *}

subsubsection {* Lemmas for predicate *}

lemma get_instr_list_Suc_def: "get_instr_list mm_d st (Suc n) = cell2instr (mm_d (st div 4)) # get_instr_list mm_d (st + 4) n"
apply (simp add: get_instr_list_def)
apply (subst div_add1_eq)
apply simp
done

lemma get_instr_list_Suc[rule_format]: "get_instr_list mm_d st (Suc n) = (get_instr_list mm_d st n) @ [cell2instr (mm_d (n + st div 4))]"
apply (simp only: get_instr_list_Suc)
apply clarsimp
apply (simp add: get_instr_list_def)
done

lemma not_change_code_append[rule_format]: "! zs. not_change_code d low_border code_size zs (xs@ys) 
                   \<longrightarrow> (not_change_code d low_border code_size ((rev xs) @ zs) ys)"
apply (induct_tac xs)
 apply simp
apply (intro allI impI)
apply simp
done

lemma not_change_code_append1[rule_format]: "! zs. not_change_code d low_border code_size zs (xs @ ys) \<longrightarrow> not_change_code d low_border code_size zs xs"
apply (induct_tac xs)
 apply simp
apply (intro allI impI)
apply simp
done

lemma not_change_seq_code_SucD: "not_change_seq_code d low_border code_size (Suc n) \<Longrightarrow> not_change_seq_code d low_border code_size n"
apply (simp add: not_change_seq_code_def)
apply (elim conjE)
apply (simp add: get_instr_list_Suc)
apply (erule not_change_code_append1)
done

subsubsection {* Some additional lemmas *}

lemma dvd_impl_mod_zero: "4 dvd x \<Longrightarrow> x mod 4 = (0::nat)"
by (clarsimp simp add: dvd_def)

lemma sa_from_Isrli: "is_instr (Isrli RD rs SA) \<Longrightarrow> SA < 32"
by (simp add: is_instr_def asm_sa_def wlen_bit_def)

lemma intwd_as_nat_int_less_32: "SA < 32 \<Longrightarrow> intwd_as_nat (int SA) = SA"
by (simp add: intwd_as_nat_def wlen_bit_def)

lemma data_mem_read_store_exec: "\<lbrakk> is_ASMcore d; 4 dvd fit_nat (intwd_as_nat r + intwd_as_nat i); rd < 32 \<rbrakk>
       \<Longrightarrow> data_mem_read (mm (store_exec d r i 4 rd)) (fit_nat (intwd_as_nat r + intwd_as_nat i)) = reg (gprs d) rd"
apply (simp add: store_exec_def store_to_mem_def is_ASMcore_def)
apply (drule dvd_impl_mod_zero)
apply (rotate_tac -1, erule ssubst)
apply (elim conjE)
apply (rotate_tac -1, erule_tac x = "fit_nat (intwd_as_nat r + intwd_as_nat i)" in allE)
apply (drule asm_nat_intwd_as_nat)
apply (rotate_tac -1, drule div_wlen_bit_is_zero)
apply (erule_tac x = "rd" in allE)
apply (drule mp, assumption)
apply (frule asm_nat_intwd_as_nat)
apply (rotate_tac -1, drule mod_wlen_bit_is_same)
apply (drule intwd2natwd2intwd)
apply (simp add: data_mem_read_def data_mem_write_def data2cell2data wlen_bit_def)
done

lemma store_exec_word_correct[rule_format]: "\<lbrakk> is_ASMcore d; 4 dvd fit_nat (intwd_as_nat r + intwd_as_nat i); rd < 32 \<rbrakk>
                                         \<Longrightarrow> mm (store_exec d r i 4 rd) = (mm d) ((fit_nat (intwd_as_nat r + intwd_as_nat i)) div 4 := data2cell (reg (gprs d) rd))"
apply (simp add: store_exec_def store_to_mem_def is_ASMcore_def)
apply (drule dvd_impl_mod_zero)
apply (rotate_tac -1, erule ssubst)
apply clarsimp
apply (rotate_tac -1, erule_tac x = "fit_nat (intwd_as_nat r + intwd_as_nat i)" in allE)
apply (erule_tac x="rd" in allE)
apply clarsimp
apply (drule asm_nat_intwd_as_nat)
apply (rotate_tac -1, drule div_wlen_bit_is_zero)
apply (frule asm_nat_intwd_as_nat)
apply (rotate_tac -1, drule mod_wlen_bit_is_same)
apply (drule intwd2natwd2intwd)
apply (simp add: data_mem_read_def data_mem_write_def data2cell2data wlen_bit_def)
done

lemma gprs_load_exec: "\<lbrakk> is_ASMcore d; 4 dvd fit_nat (intwd_as_nat r + intwd_as_nat i); rd < 32 \<rbrakk> 
           \<Longrightarrow> gprs (load_exec d sxt_wd r i 4 rd) ! rd = data_mem_read (mm d) (fit_nat (intwd_as_nat r + intwd_as_nat i))"
apply (simp add: load_exec_def)
apply (frule_tac x="fit_nat (intwd_as_nat r + intwd_as_nat i)" in correct_load_from_mem_word)
apply (subgoal_tac "fit_nat (intwd_as_nat r + intwd_as_nat i) mod 4 = 0")
 apply clarsimp
 apply (simp add: is_ASMcore_def)
apply (simp add: dvd_impl_mod_zero)
done

subsubsection {* Computation of some parts *}

lemma pc_computation: "pc + 4 < 2^wlen_bit \<Longrightarrow> fit_nat (pc + intwd_as_nat 4) = pc + 4"
apply (simp add: fit_nat_def)
apply (subgoal_tac "intwd_as_nat 4 = 4")
 apply (rotate_tac -1, erule ssubst)
 apply (erule mod_less)
apply (simp (no_asm) add: intwd_as_nat_def wlen_bit_def)
done

lemma reg_computation: 
       "\<lbrakk> is_ass_seq_instr iw; (sprs d) ! SPR_MODE = 0; pcp d + 4 < 2^wlen_bit \<rbrakk>
    \<Longrightarrow> dpc (exec_instr d iw) = pcp d \<and>
        pcp (exec_instr d iw) = pcp d + 4 \<and>
        sprs (exec_instr d iw) ! SPR_MODE = 0"
apply (drule pc_computation)
apply (simp only: is_ass_seq_instr_def is_not_contr_flow_instr_def)
apply (elim conjE exE)
apply clarsimp
apply (elim disjE)
apply (simp add: arith_exec_def comp_exec_def load_exec_def store_exec_def inc_pcs_st_def inc_pcp_by_def wlen_byte_def)+

apply clarsimp
apply (simp add: is_system_mode_def)

apply clarsimp
apply (simp add: is_system_mode_def)
apply (clarsimp simp add: inc_pcs_st_def inc_pcp_by_def wlen_byte_def)
done

lemma mem_part_word_access_update2[rule_format]: "! st. ad < st \<longrightarrow>
            mem_part_word_access ((mm d)(ad := val)) st len = mem_part_word_access (mm d) st len"
apply (induct_tac len)
 apply simp
apply (intro allI impI)
apply simp
done

lemma mem_computation:
   "\<lbrakk> is_ass_seq_instr iw; (sprs d) ! SPR_MODE = 0; 
      is_storew iw \<longrightarrow> 4 * low_border_words + code_size \<le> fit_nat (intwd_as_nat (reg (gprs d) (RS1_arg iw)) + intwd_as_nat (imm_arg iw)) \<or>
                       fit_nat (intwd_as_nat (reg (gprs d) (RS1_arg iw)) + intwd_as_nat (imm_arg iw)) < 4 * low_border_words \<rbrakk>
            \<Longrightarrow> mem_part_access (mm (exec_instr d iw)) (4 * low_border_words) code_size = mem_part_access (mm d) (4 * low_border_words) code_size"
apply (simp only: is_ass_seq_instr_def is_not_contr_flow_instr_def)
apply (elim exE conjE)
apply simp
apply (subgoal_tac "iw \<noteq> Isw RD rs imm \<longrightarrow> mm (exec_instr d iw) = mm d")
 apply (case_tac "iw = Isw RD rs imm")
  apply (simp add: is_storew_def store_exec_def store_to_mem_def data_mem_write_def mem_part_access_def)
  apply (erule disjE)
   apply (rule mem_part_word_access_update)
   apply (rule_tac j = "(4 * low_border_words + code_size) div 4" in le_trans)
    apply (subst div_add1_eq)
    apply simp
   apply (erule div_le_mono)
  apply (rule mem_part_word_access_update2)
  apply (subgoal_tac "low_border_words = (4 * low_border_words) div 4")
   prefer 2
   apply simp
  apply (rotate_tac -1, erule ssubst)
  apply (rule_tac b = "4" in less_div)
      apply simp
     apply simp
    apply simp
   apply (rule_tac j = "fit_nat (intwd_as_nat (reg (gprs d) rs) + intwd_as_nat imm)" in le_less_trans)
    apply (subst mult_commute)
    apply (subst mult_div_cancel)
    apply simp
   apply assumption
  apply simp
 apply simp
apply (rule impI)
apply simp
apply (elim disjE)
apply (simp add: arith_exec_def comp_exec_def load_exec_def inc_pcs_st_def)+
done

declare Let_def[simp del]

end
