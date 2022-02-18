(**
 * Copyright (c) 2005-2007 Alexandra Tsyban.
 * Some rights reserved, Saarland University.
 *
 * This work is licensed under the German-Jurisdiction Creative Commons
 * Attribution Non-commercial Share Alike 2.0 License.
 * See the file LIZENZ for a full copy of the license.
**)
(* $Id: instr_types.thy 22840 2008-03-26 17:32:49Z MarkHillebrand $ *)
theory instr_types imports Instr begin

datatype instr_type =
    Itype
  | Rtype
  | Jtype

primrec get_instr_type :: "instr \<Rightarrow> instr_type"
where
  "get_instr_type (Ilb RD rs imm) = Itype"
 | "get_instr_type (Ilh RD rs imm) = Itype"
 | "get_instr_type (Ilw RD rs imm) = Itype"
 | "get_instr_type (Ilbu RD rs imm) = Itype"
 | "get_instr_type (Ilhu RD rs imm) = Itype"
|  "get_instr_type (Isb RD rs imm) = Itype"
 | "get_instr_type (Ish RD rs imm) = Itype"
 | "get_instr_type (Isw RD rs imm) = Itype"

 | "get_instr_type (Ilhgi RD imm) = Itype"
 | "get_instr_type (Ilhg RD rs) = Rtype"

 | "get_instr_type (Imovs2i RD SA) = Rtype"
 | "get_instr_type (Imovi2s SA rs) = Rtype"

 | "get_instr_type (Iaddio RD rs imm) = Itype" 
 | "get_instr_type (Iaddi RD rs imm) = Itype"
 | "get_instr_type (Isubio RD rs imm) = Itype" 
 | "get_instr_type (Isubi RD rs imm) = Itype"
 | "get_instr_type (Iandi RD rs imm) = Itype"
 | "get_instr_type (Iori RD rs imm) = Itype"
 | "get_instr_type (Ixori RD rs imm) = Itype"

  |"get_instr_type (Iaddo RD RS1 RS2) = Rtype" 
  |"get_instr_type (Iadd RD RS1 RS2) = Rtype"
 | "get_instr_type (Isubo RD RS1 RS2) = Rtype" 
 | "get_instr_type (Isub RD RS1 RS2) = Rtype"
 | "get_instr_type (Iand RD RS1 RS2) = Rtype"
 | "get_instr_type (Ior RD RS1 RS2) = Rtype"
 | "get_instr_type (Ixor RD RS1 RS2) = Rtype"

 | "get_instr_type (Iclri RD) = Itype"
 | "get_instr_type (Isgri RD rs imm) = Itype"
 | "get_instr_type (Iseqi RD rs imm) = Itype"
 | "get_instr_type (Isgei RD rs imm) = Itype"
 | "get_instr_type (Islsi RD rs imm) = Itype"
 | "get_instr_type (Isnei RD rs imm) = Itype"
 | "get_instr_type (Islei RD rs imm) = Itype"
 | "get_instr_type (Iseti RD) = Itype"

 | "get_instr_type (Iclr RD) = Rtype"
 | "get_instr_type (Isgr RD RS1 RS2) = Rtype"
 | "get_instr_type (Iseq RD RS1 RS2) = Rtype"
 | "get_instr_type (Isge RD RS1 RS2) = Rtype"
 | "get_instr_type (Isls RD RS1 RS2) = Rtype"
 | "get_instr_type (Isne RD RS1 RS2) = Rtype"
 | "get_instr_type (Isle RD RS1 RS2) = Rtype"
 | "get_instr_type (Iset RD) = Rtype"

 | "get_instr_type (Islli RD rs sa) = Rtype"
 | "get_instr_type (Isrli RD rs sa) = Rtype"
 | "get_instr_type (Israi RD rs sa) = Rtype"
 | "get_instr_type (Isll RD RS1 RS2) = Rtype"
 | "get_instr_type (Isrl RD RS1 RS2) = Rtype"
 | "get_instr_type (Isra RD RS1 RS2) = Rtype"

 | "get_instr_type (Ibeqz rs imm) = Itype"
 | "get_instr_type (Ibnez rs imm) = Itype"
 | "get_instr_type (Ijr rs) = Itype"
 | "get_instr_type (Ijalr rs) = Itype"

 | "get_instr_type (Ij imm) = Jtype"
 | "get_instr_type (Ijal imm) = Jtype"

 | "get_instr_type (Itrap imm) = Jtype"
 | "get_instr_type (Irfe) = Jtype"

primrec instr_type2id :: "instr_type \<Rightarrow> nat"
where

  "instr_type2id Itype = 0"
 | "instr_type2id Rtype = 1"
 | "instr_type2id Jtype = 2"

end
