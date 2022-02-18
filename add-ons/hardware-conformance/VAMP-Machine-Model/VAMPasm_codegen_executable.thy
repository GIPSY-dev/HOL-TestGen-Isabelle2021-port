(**
 * Copyright (c) 2007 Dirk Leinenbach, Hristo Tzigarov.
 * Some rights reserved, Saarland University.
 *
 * This work is licensed under the German-Jurisdiction Creative Commons
 * Attribution Non-commercial Share Alike 2.0 License.
 * See the file LIZENZ for a full copy of the license.
**)
(* $Id: VAMPasm_codegen_executable.thy 19921 2007-10-18 15:15:05Z MarkHillebrand $ *)
theory VAMPasm_codegen_executable
imports
  Step
begin

lemma [code]: "is_instr iw = ((if is_regimm16 iw \<or> is_imm16 iw \<or> is_Ilhgi iw then (asm_imm16 (imm_arg iw)) else True) \<and>
                              (if is_imm26 iw then ( asm_imm26 (imm_arg iw)) else True) \<and>
                              (if is_regsa iw then (asm_sa (sa_arg iw)) else True) \<and>
                              (if is_2reg iw \<or> is_regimm16 iw \<or> is_regsa iw \<or> is_Ilhgi iw \<or> is_Imovs2i iw \<or> is_Ilhg iw \<or> is_onlyrd iw  then ( RD_arg iw < 32) else True) \<and>
                              (if is_2reg iw \<or> is_regimm16 iw \<or> is_regsa iw \<or> is_Imovi2s iw \<or> is_notrd iw \<or> is_imm16 iw then (RS1_arg iw < 32) else True) \<and>
                              (if is_2reg iw \<or> is_Ilhg iw then (RS2_arg iw < 32) else True) \<and>
                              (if is_Imovi2s iw \<or> is_Imovs2i iw then (sa_arg iw < 32) else True))"
apply (cases iw)
apply (simp add: is_instr_def)+
done

end
