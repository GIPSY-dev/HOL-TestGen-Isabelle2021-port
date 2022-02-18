(**
 * Copyright (c) 2004-2009 Matthias Daum, Thomas In der Rieden,
 * Dirk Leinenbach, Alexandra Tsyban.
 * Some rights reserved, Saarland University.
 *
 * This work is licensed under the German-Jurisdiction Creative Commons
 * Attribution Non-commercial Share Alike 2.0 License.
 * See the file LIZENZ for a full copy of the license.
**)
(* $Id: Instr.thy 30724 2010-03-03 10:27:08Z MareikeSchmidt $ *)
chapter {* Instruction Set *}

theory Instr imports Types begin

datatype instr = 
  -- {* data transfer (memory) *}
    Ilb regname regname immed
  | Ilh regname regname immed
  | Ilw regname regname immed
  | Ilbu regname regname immed
  | Ilhu regname regname immed
  | Isb regname regname immed
  | Ish regname regname immed
  | Isw regname regname immed
  -- {* data transfer (constant) *}
  | Ilhgi regname immed
  | Ilhg regname regname
  -- {* data transfer (registers) *}
  | Imovs2i regname regname
  | Imovi2s regname regname
  -- {* arithmetic / logical operations *}
  | Iaddio regname regname immed
  | Iaddi regname regname immed
  | Isubio regname regname immed
  | Isubi regname regname immed
  | Iandi regname regname immed
  | Iori regname regname immed
  | Ixori regname regname immed
  | Iaddo regname regname regname
  | Iadd regname regname regname
  | Isubo regname regname regname
  | Isub regname regname regname
  | Iand regname regname regname
  | Ior regname regname regname
  | Ixor regname regname regname

  -- {* test operations *}
  | Iclri regname 
  | Isgri regname regname immed
  | Iseqi regname regname immed
  | Isgei regname regname immed
  | Islsi regname regname immed
  | Isnei regname regname immed
  | Islei regname regname immed
  | Iseti regname 
  | Iclr regname 
  | Isgr regname regname regname
  | Iseq regname regname regname
  | Isge regname regname regname
  | Isls regname regname regname
  | Isne regname regname regname
  | Isle regname regname regname
  | Iset regname

  -- {* shift operations *}
  | Islli regname regname shift_amount
  | Isrli regname regname shift_amount
  | Israi regname regname shift_amount
  | Isll regname regname regname  
  | Isrl regname regname regname
  | Isra regname regname regname
  -- {* control operations *}
  | Ibeqz regname immed
  | Ibnez regname immed
  | Ijal immed
  | Ijalr regname
  | Ij immed
  | Ijr regname
  -- {* interrupt *}
  | Itrap immed
  | Irfe


definition Inop :: instr
where
  "Inop \<equiv> Iori 1 1 0"

primrec imm_arg :: "instr \<Rightarrow> immed"
where
   "imm_arg (Ilb RD rs imm) = imm"
 | "imm_arg (Ilh RD rs imm) = imm"
 | "imm_arg (Ilw RD rs imm) = imm"
 | "imm_arg (Ilbu RD rs imm) = imm"
 | "imm_arg (Ilhu RD rs imm) = imm"
 | "imm_arg (Isb RD rs imm) = imm"
 | "imm_arg (Ish RD rs imm) = imm"
 | "imm_arg (Isw RD rs imm) = imm"
 | "imm_arg (Ilhgi RD imm) = imm"
 | "imm_arg (Iaddio RD rs imm) = imm"
 | "imm_arg (Iaddi RD rs imm) = imm"
 | "imm_arg (Isubio RD rs imm) = imm"
|  "imm_arg (Isubi RD rs imm) = imm"
 | "imm_arg (Iandi RD rs imm) = imm"
|  "imm_arg (Iori RD rs imm) = imm"
 | "imm_arg (Ixori RD rs imm) = imm"
 | "imm_arg (Isgri RD rs imm) = imm"
 | "imm_arg (Iseqi RD rs imm) = imm"
 | "imm_arg (Isgei RD rs imm) = imm"
 | "imm_arg (Islsi RD rs imm) = imm"
 | "imm_arg (Isnei RD rs imm) = imm"
 | "imm_arg (Islei RD rs imm) = imm"
 | "imm_arg (Ibeqz rs imm) = imm"
 | "imm_arg (Ibnez rs imm) = imm"
 | "imm_arg (Ijal imm) = imm"
 | "imm_arg (Ij imm) = imm"
 | "imm_arg (Itrap imm) = imm"


primrec RD_arg :: "instr \<Rightarrow> regname"
where
  "RD_arg (Ilb RD rs imm) = RD"
 | "RD_arg (Ilh RD rs imm) = RD"
 | "RD_arg (Ilw RD rs imm) = RD"
 | "RD_arg (Ilbu RD rs imm) = RD"
 | "RD_arg (Ilhu RD rs imm) = RD"
 | "RD_arg (Isb RD rs imm) = RD"
 | "RD_arg (Ish RD rs imm) = RD"
 | "RD_arg (Isw RD rs imm) = RD"
 | "RD_arg (Ilhgi RD imm) = RD"
 | "RD_arg (Ilhg RD rs) = RD"
 | "RD_arg (Imovs2i RD SA) = RD"
 | "RD_arg (Iaddio RD rs imm) = RD"
 | "RD_arg (Iaddi RD rs imm) = RD"
 | "RD_arg (Isubio RD rs imm) = RD"
 | "RD_arg (Isubi RD rs imm) = RD"
 | "RD_arg (Iandi RD rs imm) = RD"
 | "RD_arg (Iori RD rs imm) = RD"
 | "RD_arg (Ixori RD rs imm) = RD"
 | "RD_arg (Iaddo RD RS1 RS2) = RD"
 | "RD_arg (Iadd RD RS1 RS2) = RD"
 | "RD_arg (Isubo RD RS1 RS2) = RD"
 | "RD_arg (Isub RD RS1 RS2) = RD"
 | "RD_arg (Iand RD RS1 RS2) = RD"
 | "RD_arg (Ior RD RS1 RS2) = RD"
 | "RD_arg (Ixor RD RS1 RS2) = RD"
 | "RD_arg (Iclri RD) = RD"
 | "RD_arg (Isgri RD rs imm) = RD"
 | "RD_arg (Iseqi RD rs imm) = RD"
 | "RD_arg (Isgei RD rs imm) = RD"
 | "RD_arg (Islsi RD rs imm) = RD"
 | "RD_arg (Isnei RD rs imm) = RD"
 | "RD_arg (Islei RD rs imm) = RD"
 | "RD_arg (Iseti RD) = RD"
 | "RD_arg (Iclr RD) = RD"
 | "RD_arg (Isgr RD RS1 RS2) = RD"
 | "RD_arg (Iseq RD RS1 RS2) = RD"
 | "RD_arg (Isge RD RS1 RS2) = RD"
 | "RD_arg (Isls RD RS1 RS2) = RD"
 | "RD_arg (Isne RD RS1 RS2) = RD"
 | "RD_arg (Isle RD RS1 RS2) = RD"
 | "RD_arg (Iset RD) = RD"
 | "RD_arg (Islli RD rs sa) = RD"
 | "RD_arg (Isrli RD rs sa) = RD"
 | "RD_arg (Israi RD rs sa) = RD"
 | "RD_arg (Isll RD RS1 RS2) = RD"
 | "RD_arg (Isrl RD RS1 RS2) = RD"
 | "RD_arg (Isra RD RS1 RS2) = RD"


primrec RS1_arg :: "instr \<Rightarrow> regname"
where
  "RS1_arg (Ilb RD rs imm) = rs"
 | "RS1_arg (Ilh RD rs imm) = rs"
 | "RS1_arg (Ilw RD rs imm) = rs"
 | "RS1_arg (Ilbu RD rs imm) = rs"
 | "RS1_arg (Ilhu RD rs imm) = rs"
 | "RS1_arg (Isb RD rs imm) = rs"
 | "RS1_arg (Ish RD rs imm) = rs"
 | "RS1_arg (Isw RD rs imm) = rs"
 | "RS1_arg (Imovi2s SA rs) = rs"
 | "RS1_arg (Iaddio RD rs imm) = rs"
 | "RS1_arg (Iaddi RD rs imm) = rs"
 | "RS1_arg (Isubio RD rs imm) = rs"
 | "RS1_arg (Isubi RD rs imm) = rs"
 | "RS1_arg (Iandi RD rs imm) = rs"
 | "RS1_arg (Iori RD rs imm) = rs"
 | "RS1_arg (Ixori RD rs imm) = rs"
 | "RS1_arg (Iaddo RD RS1 RS2) = RS1"
 | "RS1_arg (Iadd RD RS1 RS2) = RS1"
 | "RS1_arg (Isubo RD RS1 RS2) = RS1"
 | "RS1_arg (Isub RD RS1 RS2) = RS1"
 | "RS1_arg (Iand RD RS1 RS2) = RS1"
 | "RS1_arg (Ior RD RS1 RS2) = RS1"
 | "RS1_arg (Ixor RD RS1 RS2) = RS1"
 | "RS1_arg (Isgri RD rs imm) = rs"
 | "RS1_arg (Iseqi RD rs imm) = rs"
 | "RS1_arg (Isgei RD rs imm) = rs"
 | "RS1_arg (Islsi RD rs imm) = rs"
 | "RS1_arg (Isnei RD rs imm) = rs"
 | "RS1_arg (Islei RD rs imm) = rs"
 | "RS1_arg (Isgr RD RS1 RS2) = RS1"
 | "RS1_arg (Iseq RD RS1 RS2) = RS1"
 | "RS1_arg (Isge RD RS1 RS2) = RS1"
 | "RS1_arg (Isls RD RS1 RS2) = RS1"
 | "RS1_arg (Isne RD RS1 RS2) = RS1"
 | "RS1_arg (Isle RD RS1 RS2) = RS1"
 | "RS1_arg (Islli RD rs sa) = rs"
 | "RS1_arg (Isrli RD rs sa) = rs"
 | "RS1_arg (Israi RD rs sa) = rs"
 | "RS1_arg (Isll RD RS1 RS2) = RS1"
 | "RS1_arg (Isrl RD RS1 RS2) = RS1"
 | "RS1_arg (Isra RD RS1 RS2) = RS1"
 | "RS1_arg (Ibeqz rs imm) = rs"
 | "RS1_arg (Ibnez rs imm) = rs"
 | "RS1_arg (Ijalr rs) = rs"
 | "RS1_arg (Ijr rs) = rs"

primrec RS2_arg :: "instr \<Rightarrow> regname"
where
  "RS2_arg (Ilhg RD rs) = rs" 
 | "RS2_arg (Iaddo RD RS1 RS2) = RS2"
 | "RS2_arg (Iadd RD RS1 RS2) = RS2"
 | "RS2_arg (Isubo RD RS1 RS2) = RS2"
 | "RS2_arg (Isub RD RS1 RS2) = RS2"
 | "RS2_arg (Iand RD RS1 RS2) = RS2"
 | "RS2_arg (Ior RD RS1 RS2) = RS2"
 | "RS2_arg (Ixor RD RS1 RS2) = RS2"
 | "RS2_arg (Isgr RD RS1 RS2) = RS2"
 | "RS2_arg (Iseq RD RS1 RS2) = RS2"
 | "RS2_arg (Isge RD RS1 RS2) = RS2"
 | "RS2_arg (Isls RD RS1 RS2) = RS2"
 | "RS2_arg (Isne RD RS1 RS2) = RS2"
 | "RS2_arg (Isle RD RS1 RS2) = RS2"
 | "RS2_arg (Isll RD RS1 RS2) = RS2" 
 | "RS2_arg (Isrl RD RS1 RS2) = RS2" 
 | "RS2_arg (Isra RD RS1 RS2) = RS2"

primrec sa_arg :: "instr \<Rightarrow> shift_amount"
where
  "sa_arg (Islli RD rs sa) = sa"
 | "sa_arg (Isrli RD rs sa) = sa"
 | "sa_arg (Israi RD rs sa) = sa"
 | "sa_arg (Imovi2s SA rs) = SA"
 | "sa_arg (Imovs2i RD SA) = SA"

primrec is_2reg :: "instr \<Rightarrow> bool"
where
  "is_2reg (Ilb RD rs imm) = False"
 | "is_2reg (Ilh RD rs imm) = False"
 | "is_2reg (Ilw RD rs imm) = False"
 | "is_2reg (Ilbu RD rs imm) = False"
 | "is_2reg (Ilhu RD rs imm) = False"
 | "is_2reg (Isb RD rs imm) = False"
 | "is_2reg (Ish RD rs imm) = False"
 | "is_2reg (Isw RD rs imm) = False"

 | "is_2reg (Ilhgi RD imm) = False"
 | "is_2reg (Ilhg RD rs) = False"

 | "is_2reg (Imovs2i RD SA) = False"
 | "is_2reg (Imovi2s SA rs) = False"

 | "is_2reg (Iaddio RD rs imm) = False"
 | "is_2reg (Iaddi RD rs imm) = False"
 | "is_2reg (Isubio RD rs imm) = False"
 | "is_2reg (Isubi RD rs imm) = False"
 | "is_2reg (Iandi RD rs imm) = False"
|  "is_2reg (Iori RD rs imm) = False"
 | "is_2reg (Ixori RD rs imm) = False"

 | "is_2reg (Iaddo RD RS1 RS2) = True"
 | "is_2reg (Iadd RD RS1 RS2) = True"
 | "is_2reg (Isubo RD RS1 RS2) = True"
 | "is_2reg (Isub RD RS1 RS2) = True"
 | "is_2reg (Iand RD RS1 RS2) = True"
 | "is_2reg (Ior RD RS1 RS2) = True"
 | "is_2reg (Ixor RD RS1 RS2) = True"

 | "is_2reg (Iclri RD) = False"
 | "is_2reg (Isgri RD rs imm) = False"
 | "is_2reg (Iseqi RD rs imm) = False"
 | "is_2reg (Isgei RD rs imm) = False"
 | "is_2reg (Islsi RD rs imm) = False"
 | "is_2reg (Isnei RD rs imm) = False"
 | "is_2reg (Islei RD rs imm) = False"
 | "is_2reg (Iseti RD) = False"

 | "is_2reg (Iclr RD) = False"
 | "is_2reg (Isgr RD RS1 RS2) = True"
 | "is_2reg (Iseq RD RS1 RS2) = True"
 | "is_2reg (Isge RD RS1 RS2) = True"
 | "is_2reg (Isls RD RS1 RS2) = True"
 | "is_2reg (Isne RD RS1 RS2) = True"
 | "is_2reg (Isle RD RS1 RS2) = True"
 | "is_2reg (Iset RD) = False"

 | "is_2reg (Islli RD rs sa) = False"
 | "is_2reg (Isrli RD rs sa) = False"
 | "is_2reg (Israi RD rs sa) = False"
 | "is_2reg (Isll RD RS1 RS2) = True"
|  "is_2reg (Isrl RD RS1 RS2) = True"
|  "is_2reg (Isra RD RS1 RS2) = True"

 | "is_2reg (Ibeqz rs imm) = False"
 | "is_2reg (Ibnez rs imm) = False"
 | "is_2reg (Ijal imm) = False"
 | "is_2reg (Ijalr rs) = False"
 | "is_2reg (Ij imm) = False"
 | "is_2reg (Ijr rs) = False"

 | "is_2reg (Itrap imm) = False"
 | "is_2reg (Irfe) = False"


primrec is_regimm16 :: "instr \<Rightarrow> bool"
where
  "is_regimm16 (Ilb RD rs imm) = True"
 | "is_regimm16 (Ilh RD rs imm) = True"
 | "is_regimm16 (Ilw RD rs imm) = True"
 | "is_regimm16 (Ilbu RD rs imm) = True"
 | "is_regimm16 (Ilhu RD rs imm) = True"
 | "is_regimm16 (Isb RD rs imm) = True"
 | "is_regimm16 (Ish RD rs imm) = True"
 | "is_regimm16 (Isw RD rs imm) = True"

 | "is_regimm16 (Ilhgi RD imm) = False"
 | "is_regimm16 (Ilhg RD rs) = False"

 | "is_regimm16 (Imovs2i RD SA) = False"
 | "is_regimm16 (Imovi2s SA rs) = False"

 | "is_regimm16 (Iaddio RD rs imm) = True"
 | "is_regimm16 (Iaddi RD rs imm) = True"
 | "is_regimm16 (Isubio RD rs imm) = True"
 | "is_regimm16 (Isubi RD rs imm) = True"
 | "is_regimm16 (Iandi RD rs imm) = True"
 | "is_regimm16 (Iori RD rs imm) = True"
 | "is_regimm16 (Ixori RD rs imm) = True"

 | "is_regimm16 (Iaddo RD RS1 RS2) = False"
 | "is_regimm16 (Iadd RD RS1 RS2) = False"
 | "is_regimm16 (Isubo RD RS1 RS2) = False"
 | "is_regimm16 (Isub RD RS1 RS2) = False"
 | "is_regimm16 (Iand RD RS1 RS2) = False"
 | "is_regimm16 (Ior RD RS1 RS2) = False"
 | "is_regimm16 (Ixor RD RS1 RS2) = False"

 | "is_regimm16 (Iclri RD) = False"
 | "is_regimm16 (Isgri RD rs imm) = True"
 | "is_regimm16 (Iseqi RD rs imm) = True"
 | "is_regimm16 (Isgei RD rs imm) = True"
 | "is_regimm16 (Islsi RD rs imm) = True"
 | "is_regimm16 (Isnei RD rs imm) = True"
 | "is_regimm16 (Islei RD rs imm) = True"
|  "is_regimm16 (Iseti RD) = False"

 | "is_regimm16 (Iclr RD) = False"
 | "is_regimm16 (Isgr RD RS1 RS2) = False"
 | "is_regimm16 (Iseq RD RS1 RS2) = False"
 | "is_regimm16 (Isge RD RS1 RS2) = False"
 | "is_regimm16 (Isls RD RS1 RS2) = False"
 | "is_regimm16 (Isne RD RS1 RS2) = False"
 | "is_regimm16 (Isle RD RS1 RS2) = False"
 | "is_regimm16 (Iset RD) = False"

 | "is_regimm16 (Islli RD rs sa) = False"
 | "is_regimm16 (Isrli RD rs sa) = False"
 | "is_regimm16 (Israi RD rs sa) = False"
 | "is_regimm16 (Isll RD RS1 RS2) = False"
 | "is_regimm16 (Isrl RD RS1 RS2) = False"
 | "is_regimm16 (Isra RD RS1 RS2) = False"

 | "is_regimm16 (Ibeqz rs imm) = False"
 | "is_regimm16 (Ibnez rs imm) = False"
 | "is_regimm16 (Ijal imm) = False"
 | "is_regimm16 (Ijalr rs) = False"
 | "is_regimm16 (Ij imm) = False"
|  "is_regimm16 (Ijr rs) = False"

 | "is_regimm16 (Itrap imm) = False"
 | "is_regimm16 (Irfe) = False"

primrec is_regsa :: "instr \<Rightarrow> bool"
where
  "is_regsa (Ilb RD rs imm) = False"
 | "is_regsa (Ilh RD rs imm) = False"
 | "is_regsa (Ilw RD rs imm) = False"
 | "is_regsa (Ilbu RD rs imm) = False"
 | "is_regsa (Ilhu RD rs imm) = False"
 | "is_regsa (Isb RD rs imm) = False"
 | "is_regsa (Ish RD rs imm) = False"
 | "is_regsa (Isw RD rs imm) = False"

 | "is_regsa (Ilhgi RD imm) = False"
 | "is_regsa (Ilhg RD rs) = False"

 | "is_regsa (Imovs2i RD SA) = False"
 | "is_regsa (Imovi2s SA rs) = False"

 | "is_regsa (Iaddio RD rs imm) = False"
 | "is_regsa (Iaddi RD rs imm) = False"
 | "is_regsa (Isubio RD rs imm) = False"
 | "is_regsa (Isubi RD rs imm) = False"
 | "is_regsa (Iandi RD rs imm) = False"
 | "is_regsa (Iori RD rs imm) = False"
 | "is_regsa (Ixori RD rs imm) = False"

 | "is_regsa (Iaddo RD RS1 RS2) = False"
 | "is_regsa (Iadd RD RS1 RS2) = False"
 | "is_regsa (Isubo RD RS1 RS2) = False"
 | "is_regsa (Isub RD RS1 RS2) = False"
 | "is_regsa (Iand RD RS1 RS2) = False"
 | "is_regsa (Ior RD RS1 RS2) = False"
 | "is_regsa (Ixor RD RS1 RS2) = False"

  |"is_regsa (Iclri RD) = False"
 | "is_regsa (Isgri RD rs imm) = False"
 | "is_regsa (Iseqi RD rs imm) = False"
 | "is_regsa (Isgei RD rs imm) = False"
 | "is_regsa (Islsi RD rs imm) = False"
 | "is_regsa (Isnei RD rs imm) = False"
 | "is_regsa (Islei RD rs imm) = False"
 | "is_regsa (Iseti RD) = False"

  |"is_regsa (Iclr RD) = False"
 | "is_regsa (Isgr RD RS1 RS2) = False"
 | "is_regsa (Iseq RD RS1 RS2) = False"
 | "is_regsa (Isge RD RS1 RS2) = False"
 | "is_regsa (Isls RD RS1 RS2) = False"
 | "is_regsa (Isne RD RS1 RS2) = False"
 | "is_regsa (Isle RD RS1 RS2) = False"
 | "is_regsa (Iset RD) = False"

 | "is_regsa (Islli RD rs sa) = True"
 | "is_regsa (Isrli RD rs sa) = True"
 | "is_regsa (Israi RD rs sa) = True"
 | "is_regsa (Isll RD RS1 RS2) = False"
 | "is_regsa (Isrl RD RS1 RS2) = False"
 | "is_regsa (Isra RD RS1 RS2) = False"

 | "is_regsa (Ibeqz rs imm) = False"
 | "is_regsa (Ibnez rs imm) = False"
 | "is_regsa (Ijal imm) = False"
 | "is_regsa (Ijalr rs) = False"
|  "is_regsa (Ij imm) = False"
 | "is_regsa (Ijr rs) = False"

 | "is_regsa (Itrap imm) = False"
 | "is_regsa (Irfe) = False"


primrec is_imm26 :: "instr \<Rightarrow> bool"
where
  "is_imm26 (Ilb RD rs imm) = False"
  |"is_imm26 (Ilh RD rs imm) = False"
  |"is_imm26 (Ilw RD rs imm) = False"
  |"is_imm26 (Ilbu RD rs imm) = False"
 | "is_imm26 (Ilhu RD rs imm) = False"
 | "is_imm26 (Isb RD rs imm) = False"
 | "is_imm26 (Ish RD rs imm) = False"
 | "is_imm26 (Isw RD rs imm) = False"

 | "is_imm26 (Ilhgi RD imm) = False"
 | "is_imm26 (Ilhg RD rs) = False"

  |"is_imm26 (Imovs2i RD SA) = False"
  |"is_imm26 (Imovi2s SA rs) = False"

 | "is_imm26 (Iaddio RD rs imm) = False"
 | "is_imm26 (Iaddi RD rs imm) = False"
 | "is_imm26 (Isubio RD rs imm) = False"
 | "is_imm26 (Isubi RD rs imm) = False"
 | "is_imm26 (Iandi RD rs imm) = False"
 | "is_imm26 (Iori RD rs imm) = False"
 | "is_imm26 (Ixori RD rs imm) = False"

 | "is_imm26 (Iaddo RD RS1 RS2) = False"
  |"is_imm26 (Iadd RD RS1 RS2) = False"
 | "is_imm26 (Isubo RD RS1 RS2) = False"
 | "is_imm26 (Isub RD RS1 RS2) = False"
 | "is_imm26 (Iand RD RS1 RS2) = False"
 | "is_imm26 (Ior RD RS1 RS2) = False"
 | "is_imm26 (Ixor RD RS1 RS2) = False"

 | "is_imm26 (Iclri RD) = False"
 | "is_imm26 (Isgri RD rs imm) = False"
 | "is_imm26 (Iseqi RD rs imm) = False"
 | "is_imm26 (Isgei RD rs imm) = False"
|  "is_imm26 (Islsi RD rs imm) = False"
 | "is_imm26 (Isnei RD rs imm) = False"
 | "is_imm26 (Islei RD rs imm) = False"
 | "is_imm26 (Iseti RD) = False"

 | "is_imm26 (Iclr RD) = False"
 | "is_imm26 (Iseq RD RS1 RS2) = False"
 | "is_imm26 (Isge RD RS1 RS2) = False"
 | "is_imm26 (Isls RD RS1 RS2) = False"
  |"is_imm26 (Isne RD RS1 RS2) = False"
 | "is_imm26 (Isle RD RS1 RS2) = False"
 | "is_imm26 (Iset RD) = False"

 | "is_imm26 (Islli RD rs sa) = False"
 | "is_imm26 (Isrli RD rs sa) = False"
  |"is_imm26 (Israi RD rs sa) = False"
 | "is_imm26 (Isll RD RS1 RS2) = False"
 | "is_imm26 (Isrl RD RS1 RS2) = False"
 | "is_imm26 (Isra RD RS1 RS2) = False"

 | "is_imm26 (Ibeqz rs imm) = False"
 | "is_imm26 (Ibnez rs imm) = False"
 | "is_imm26 (Ijal imm) = True"
 | "is_imm26 (Ijalr rs) = False"
 | "is_imm26 (Ij imm) = True"
 | "is_imm26 (Ijr rs) = False"

 | "is_imm26 (Itrap imm) = True"
 | "is_imm26 (Irfe) = False"

primrec is_Ilhgi :: "instr \<Rightarrow> bool"
where
  "is_Ilhgi (Ilb RD rs imm) = False"
 | "is_Ilhgi (Ilh RD rs imm) = False"
 | "is_Ilhgi (Ilw RD rs imm) = False"
 | "is_Ilhgi (Ilbu RD rs imm) = False"
 | "is_Ilhgi (Ilhu RD rs imm) = False"
 | "is_Ilhgi (Isb RD rs imm) = False"
 | "is_Ilhgi (Ish RD rs imm) = False"
 | "is_Ilhgi (Isw RD rs imm) = False"

 | "is_Ilhgi (Ilhgi RD imm) = True"
 | "is_Ilhgi (Ilhg RD rs) = False"

 | "is_Ilhgi (Imovs2i RD SA) = False"
 | "is_Ilhgi (Imovi2s SA rs) = False"

 | "is_Ilhgi (Iaddio RD rs imm) = False"
 | "is_Ilhgi (Iaddi RD rs imm) = False"
 | "is_Ilhgi (Isubio RD rs imm) = False"
 | "is_Ilhgi (Isubi RD rs imm) = False"
 | "is_Ilhgi (Iandi RD rs imm) = False"
 | "is_Ilhgi (Iori RD rs imm) = False"
 | "is_Ilhgi (Ixori RD rs imm) = False"

 | "is_Ilhgi (Iaddo RD RS1 RS2) = False"
  |"is_Ilhgi (Iadd RD RS1 RS2) = False"
 | "is_Ilhgi (Isubo RD RS1 RS2) = False"
 | "is_Ilhgi (Isub RD RS1 RS2) = False"
 | "is_Ilhgi (Iand RD RS1 RS2) = False"
|  "is_Ilhgi (Ior RD RS1 RS2) = False"
 | "is_Ilhgi (Ixor RD RS1 RS2) = False"

 | "is_Ilhgi (Iclri RD) = False"
 | "is_Ilhgi (Isgri RD rs imm) = False"
 | "is_Ilhgi (Iseqi RD rs imm) = False"
 | "is_Ilhgi (Isgei RD rs imm) = False"
 | "is_Ilhgi (Islsi RD rs imm) = False"
 | "is_Ilhgi (Isnei RD rs imm) = False"
 | "is_Ilhgi (Islei RD rs imm) = False"
 | "is_Ilhgi (Iseti RD) = False"

 | "is_Ilhgi (Iclr RD) = False"
 | "is_Ilhgi (Isgr RD RS1 RS2) = False"
 | "is_Ilhgi (Iseq RD RS1 RS2) = False"
 | "is_Ilhgi (Isge RD RS1 RS2) = False"
 | "is_Ilhgi (Isls RD RS1 RS2) = False"
 | "is_Ilhgi (Isne RD RS1 RS2) = False"
 | "is_Ilhgi (Isle RD RS1 RS2) = False"
|  "is_Ilhgi (Iset RD) = False"

 | "is_Ilhgi (Islli RD rs sa) = False"
 | "is_Ilhgi (Isrli RD rs sa) = False"
 | "is_Ilhgi (Israi RD rs sa) = False"
 | "is_Ilhgi (Isll RD RS1 RS2) = False"
 | "is_Ilhgi (Isrl RD RS1 RS2) = False"
 | "is_Ilhgi (Isra RD RS1 RS2) = False"

 | "is_Ilhgi (Ibeqz rs imm) = False"
 | "is_Ilhgi (Ibnez rs imm) = False"
 | "is_Ilhgi (Ijal imm) = False"
 | "is_Ilhgi (Ijalr rs) = False"
 | "is_Ilhgi (Ij imm) = False"
|  "is_Ilhgi (Ijr rs) = False"

 | "is_Ilhgi (Itrap imm) = False"
 | "is_Ilhgi (Irfe) = False"

primrec is_imm16 :: "instr \<Rightarrow> bool"
where
  "is_imm16 (Ilb RD rs imm) = False"
 | "is_imm16 (Ilh RD rs imm) = False"
 | "is_imm16 (Ilw RD rs imm) = False"
 | "is_imm16 (Ilbu RD rs imm) = False"
 | "is_imm16 (Ilhu RD rs imm) = False"
 | "is_imm16 (Isb RD rs imm) = False"
 | "is_imm16 (Ish RD rs imm) = False"
 | "is_imm16 (Isw RD rs imm) = False"

 | "is_imm16 (Ilhgi RD imm) = False"
 | "is_imm16 (Ilhg RD rs) = False"

 | "is_imm16 (Imovs2i RD SA) = False"
 | "is_imm16 (Imovi2s SA rs) = False"

 | "is_imm16 (Iaddio RD rs imm) = False"
 | "is_imm16 (Iaddi RD rs imm) = False"
 | "is_imm16 (Isubio RD rs imm) = False"
 | "is_imm16 (Isubi RD rs imm) = False"
 | "is_imm16 (Iandi RD rs imm) = False"
 | "is_imm16 (Iori RD rs imm) = False"
 | "is_imm16 (Ixori RD rs imm) = False"

 | "is_imm16 (Iaddo RD RS1 RS2) = False"
  |"is_imm16 (Iadd RD RS1 RS2) = False"
 | "is_imm16 (Isubo RD RS1 RS2) = False"
 | "is_imm16 (Isub RD RS1 RS2) = False"
 | "is_imm16 (Iand RD RS1 RS2) = False"
 | "is_imm16 (Ior RD RS1 RS2) = False"
 | "is_imm16 (Ixor RD RS1 RS2) = False"

 | "is_imm16 (Iclri RD) = False"
 | "is_imm16 (Isgri RD rs imm) = False"
 | "is_imm16 (Iseqi RD rs imm) = False"
 | "is_imm16 (Isgei RD rs imm) = False"
 | "is_imm16 (Islsi RD rs imm) = False"
 | "is_imm16 (Isnei RD rs imm) = False"
 | "is_imm16 (Islei RD rs imm) = False"
 | "is_imm16 (Iseti RD) = False"

 | "is_imm16 (Iclr RD) = False"
 | "is_imm16 (Isgr RD RS1 RS2) = False"
 | "is_imm16 (Iseq RD RS1 RS2) = False"
 | "is_imm16 (Isge RD RS1 RS2) = False"
 | "is_imm16 (Isls RD RS1 RS2) = False"
 | "is_imm16 (Isne RD RS1 RS2) = False"
 | "is_imm16 (Isle RD RS1 RS2) = False"
 | "is_imm16 (Iset RD) = False"

 | "is_imm16 (Islli RD rs sa) = False"
 | "is_imm16 (Isrli RD rs sa) = False"
 | "is_imm16 (Israi RD rs sa) = False"
 | "is_imm16 (Isll RD RS1 RS2) = False"
 | "is_imm16 (Isrl RD RS1 RS2) = False"
 | "is_imm16 (Isra RD RS1 RS2) = False"

  |"is_imm16 (Ibeqz rs imm) = True"
 | "is_imm16 (Ibnez rs imm) = True"
 | "is_imm16 (Ijal imm) = False"
 | "is_imm16 (Ijalr rs) = False"
 | "is_imm16 (Ij imm) = False"
|  "is_imm16 (Ijr rs) = False"

 | "is_imm16 (Itrap imm) = False"
 | "is_imm16 (Irfe) = False"

primrec is_Imovs2i :: "instr \<Rightarrow> bool"
where
  "is_Imovs2i (Ilb RD rs imm) = False"
 | "is_Imovs2i (Ilh RD rs imm) = False"
 | "is_Imovs2i (Ilw RD rs imm) = False"
 | "is_Imovs2i (Ilbu RD rs imm) = False"
 | "is_Imovs2i (Ilhu RD rs imm) = False"
 | "is_Imovs2i (Isb RD rs imm) = False"
 | "is_Imovs2i (Ish RD rs imm) = False"
 | "is_Imovs2i (Isw RD rs imm) = False"

 | "is_Imovs2i (Ilhgi RD imm) = False"
 | "is_Imovs2i (Ilhg RD rs) = False"

 | "is_Imovs2i (Imovs2i RD SA) = True"
 | "is_Imovs2i (Imovi2s SA rs) = False"

 | "is_Imovs2i (Iaddio RD rs imm) = False"
 | "is_Imovs2i (Iaddi RD rs imm) = False"
 | "is_Imovs2i (Isubio RD rs imm) = False"
 | "is_Imovs2i (Isubi RD rs imm) = False"
 | "is_Imovs2i (Iandi RD rs imm) = False"
 | "is_Imovs2i (Iori RD rs imm) = False"
 | "is_Imovs2i (Ixori RD rs imm) = False"

 | "is_Imovs2i (Iaddo RD RS1 RS2) = False"
 | "is_Imovs2i (Iadd RD RS1 RS2) = False"
 | "is_Imovs2i (Isubo RD RS1 RS2) = False"
 | "is_Imovs2i (Isub RD RS1 RS2) = False"
 | "is_Imovs2i (Iand RD RS1 RS2) = False"
 | "is_Imovs2i (Ior RD RS1 RS2) = False"
 | "is_Imovs2i (Ixor RD RS1 RS2) = False"

 | "is_Imovs2i (Iclri RD) = False"
 | "is_Imovs2i (Isgri RD rs imm) = False"
 | "is_Imovs2i (Iseqi RD rs imm) = False"
 | "is_Imovs2i (Isgei RD rs imm) = False"
 | "is_Imovs2i (Islsi RD rs imm) = False"
 | "is_Imovs2i (Isnei RD rs imm) = False"
|  "is_Imovs2i (Islei RD rs imm) = False"
 | "is_Imovs2i (Iseti RD) = False"

 | "is_Imovs2i (Iclr RD) = False"
 | "is_Imovs2i (Isgr RD RS1 RS2) = False"
 | "is_Imovs2i (Iseq RD RS1 RS2) = False"
 | "is_Imovs2i (Isge RD RS1 RS2) = False"
 | "is_Imovs2i (Isls RD RS1 RS2) = False"
 | "is_Imovs2i (Isne RD RS1 RS2) = False"
 | "is_Imovs2i (Isle RD RS1 RS2) = False"
 | "is_Imovs2i (Iset RD) = False"

 | "is_Imovs2i (Islli RD rs sa) = False"
 | "is_Imovs2i (Isrli RD rs sa) = False"
 | "is_Imovs2i (Israi RD rs sa) = False"
 | "is_Imovs2i (Isll RD RS1 RS2) = False"
 | "is_Imovs2i (Isrl RD RS1 RS2) = False"
 | "is_Imovs2i (Isra RD RS1 RS2) = False"

  |"is_Imovs2i (Ibeqz rs imm) = False"
 | "is_Imovs2i (Ibnez rs imm) = False"
 | "is_Imovs2i (Ijal imm) = False"
 | "is_Imovs2i (Ijalr rs) = False"
 | "is_Imovs2i (Ij imm) = False"
 | "is_Imovs2i (Ijr rs) = False"

 | "is_Imovs2i (Itrap imm) = False"
 | "is_Imovs2i (Irfe) = False"

lemma is_Imovs2i_deff: "is_Imovs2i iw = (\<exists> sa rd. iw = Imovs2i rd sa)"
  by (case_tac iw, simp_all)

primrec is_Imovi2s :: "instr \<Rightarrow> bool"
where
  "is_Imovi2s (Ilb RD rs imm) = False"
 | "is_Imovi2s (Ilh RD rs imm) = False"
 | "is_Imovi2s (Ilw RD rs imm) = False"
 | "is_Imovi2s (Ilbu RD rs imm) = False"
 | "is_Imovi2s (Ilhu RD rs imm) = False"
 | "is_Imovi2s (Isb RD rs imm) = False"
 | "is_Imovi2s (Ish RD rs imm) = False"
 | "is_Imovi2s (Isw RD rs imm) = False"

 | "is_Imovi2s (Ilhgi RD imm) = False"
 | "is_Imovi2s (Ilhg RD rs) = False"

 | "is_Imovi2s (Imovs2i RD SA) = False"
 | "is_Imovi2s (Imovi2s SA rs) = True"

 | "is_Imovi2s (Iaddio RD rs imm) = False"
 | "is_Imovi2s (Iaddi RD rs imm) = False"
 | "is_Imovi2s (Isubio RD rs imm) = False"
 | "is_Imovi2s (Isubi RD rs imm) = False"
 | "is_Imovi2s (Iandi RD rs imm) = False"
 | "is_Imovi2s (Iori RD rs imm) = False"
 | "is_Imovi2s (Ixori RD rs imm) = False"

 | "is_Imovi2s (Iaddo RD RS1 RS2) = False"
 | "is_Imovi2s (Iadd RD RS1 RS2) = False"
 | "is_Imovi2s (Isubo RD RS1 RS2) = False"
 | "is_Imovi2s (Isub RD RS1 RS2) = False"
 | "is_Imovi2s (Iand RD RS1 RS2) = False"
|  "is_Imovi2s (Ior RD RS1 RS2) = False"
 | "is_Imovi2s (Ixor RD RS1 RS2) = False"

  |"is_Imovi2s (Iclri RD) = False"
 | "is_Imovi2s (Isgri RD rs imm) = False"
 | "is_Imovi2s (Iseqi RD rs imm) = False"
 | "is_Imovi2s (Isgei RD rs imm) = False"
 | "is_Imovi2s (Islsi RD rs imm) = False"
 | "is_Imovi2s (Isnei RD rs imm) = False"
 | "is_Imovi2s (Islei RD rs imm) = False"
|  "is_Imovi2s (Iseti RD) = False"

 | "is_Imovi2s (Iclr RD) = False"
 | "is_Imovi2s (Isgr RD RS1 RS2) = False"
 | "is_Imovi2s (Iseq RD RS1 RS2) = False"
 | "is_Imovi2s (Isge RD RS1 RS2) = False"
 | "is_Imovi2s (Isls RD RS1 RS2) = False"
 | "is_Imovi2s (Isne RD RS1 RS2) = False"
 | "is_Imovi2s (Isle RD RS1 RS2) = False"
 | "is_Imovi2s (Iset RD) = False"

 | "is_Imovi2s (Islli RD rs sa) = False"
 | "is_Imovi2s (Isrli RD rs sa) = False"
 | "is_Imovi2s (Israi RD rs sa) = False"
 | "is_Imovi2s (Isll RD RS1 RS2) = False"
 | "is_Imovi2s (Isrl RD RS1 RS2) = False"
|  "is_Imovi2s (Isra RD RS1 RS2) = False"

 | "is_Imovi2s (Ibeqz rs imm) = False"
 | "is_Imovi2s (Ibnez rs imm) = False"
 | "is_Imovi2s (Ijal imm) = False"
 | "is_Imovi2s (Ijalr rs) = False"
 | "is_Imovi2s (Ij imm) = False"
 | "is_Imovi2s (Ijr rs) = False"

 | "is_Imovi2s (Itrap imm) = False"
 | "is_Imovi2s (Irfe) = False"

lemma is_Imovi2s_deff: "(is_Imovi2s iw) = (\<exists> rs sa. iw = Imovi2s sa rs)"
apply (case_tac iw, simp_all)
done

primrec is_Ilhg :: "instr \<Rightarrow> bool"
where
  "is_Ilhg (Ilb RD rs imm) = False"
 | "is_Ilhg (Ilh RD rs imm) = False"
 | "is_Ilhg (Ilw RD rs imm) = False"
 | "is_Ilhg (Ilbu RD rs imm) = False"
 | "is_Ilhg (Ilhu RD rs imm) = False"
 | "is_Ilhg (Isb RD rs imm) = False"
 | "is_Ilhg (Ish RD rs imm) = False"
 | "is_Ilhg (Isw RD rs imm) = False"

 | "is_Ilhg (Ilhgi RD imm) = False"
 | "is_Ilhg (Ilhg RD rs) = True"

 | "is_Ilhg (Imovs2i RD SA) = False"
 | "is_Ilhg (Imovi2s SA rs) = False"

 | "is_Ilhg (Iaddio RD rs imm) = False"
 | "is_Ilhg (Iaddi RD rs imm) = False"
 | "is_Ilhg (Isubio RD rs imm) = False"
 | "is_Ilhg (Isubi RD rs imm) = False"
 | "is_Ilhg (Iandi RD rs imm) = False"
 | "is_Ilhg (Iori RD rs imm) = False"
 | "is_Ilhg (Ixori RD rs imm) = False"

 | "is_Ilhg (Iaddo RD RS1 RS2) = False"
 | "is_Ilhg (Iadd RD RS1 RS2) = False"
 | "is_Ilhg (Isubo RD RS1 RS2) = False"
 | "is_Ilhg (Isub RD RS1 RS2) = False"
 | "is_Ilhg (Iand RD RS1 RS2) = False"
 | "is_Ilhg (Ior RD RS1 RS2) = False"
 | "is_Ilhg (Ixor RD RS1 RS2) = False"

 | "is_Ilhg (Iclri RD) = False"
 | "is_Ilhg (Isgri RD rs imm) = False"
 | "is_Ilhg (Iseqi RD rs imm) = False"
 | "is_Ilhg (Isgei RD rs imm) = False"
 | "is_Ilhg (Islsi RD rs imm) = False"
 | "is_Ilhg (Isnei RD rs imm) = False"
 | "is_Ilhg (Islei RD rs imm) = False"
 | "is_Ilhg (Iseti RD) = False"

 | "is_Ilhg (Iclr RD) = False"
 | "is_Ilhg (Isgr RD RS1 RS2) = False"
 | "is_Ilhg (Iseq RD RS1 RS2) = False"
 | "is_Ilhg (Isge RD RS1 RS2) = False"
 | "is_Ilhg (Isls RD RS1 RS2) = False"
 | "is_Ilhg (Isne RD RS1 RS2) = False"
 | "is_Ilhg (Isle RD RS1 RS2) = False"
 | "is_Ilhg (Iset RD) = False"

 | "is_Ilhg (Islli RD rs sa) = False"
 | "is_Ilhg (Isrli RD rs sa) = False"
 | "is_Ilhg (Israi RD rs sa) = False"
 | "is_Ilhg (Isll RD RS1 RS2) = False"
 | "is_Ilhg (Isrl RD RS1 RS2) = False"
 | "is_Ilhg (Isra RD RS1 RS2) = False"

 | "is_Ilhg (Ibeqz rs imm) = False"
 | "is_Ilhg (Ibnez rs imm) = False"
 | "is_Ilhg (Ijal imm) = False"
 | "is_Ilhg (Ijalr rs) = False"
 | "is_Ilhg (Ij imm) = False"
 | "is_Ilhg (Ijr rs) = False"

 | "is_Ilhg (Itrap imm) = False"
 | "is_Ilhg (Irfe) = False"

primrec is_notrd :: "instr \<Rightarrow> bool"
where
  "is_notrd (Ilb RD rs imm) = False"
 | "is_notrd (Ilh RD rs imm) = False"
 | "is_notrd (Ilw RD rs imm) = False"
 | "is_notrd (Ilbu RD rs imm) = False"
 | "is_notrd (Ilhu RD rs imm) = False"
 | "is_notrd (Isb RD rs imm) = False"
 | "is_notrd (Ish RD rs imm) = False"
 | "is_notrd (Isw RD rs imm) = False"

 | "is_notrd (Ilhgi RD imm) = False"
 | "is_notrd (Ilhg RD rs) = False"

 | "is_notrd (Imovs2i RD SA) = False"
 | "is_notrd (Imovi2s SA rs) = False"

 | "is_notrd (Iaddio RD rs imm) = False"
 | "is_notrd (Iaddi RD rs imm) = False"
 | "is_notrd (Isubio RD rs imm) = False"
 | "is_notrd (Isubi RD rs imm) = False"
 | "is_notrd (Iandi RD rs imm) = False"
 | "is_notrd (Iori RD rs imm) = False"
 | "is_notrd (Ixori RD rs imm) = False"

 | "is_notrd (Iaddo RD RS1 RS2) = False"
 | "is_notrd (Iadd RD RS1 RS2) = False"
 | "is_notrd (Isubo RD RS1 RS2) = False"
 | "is_notrd (Isub RD RS1 RS2) = False"
 | "is_notrd (Iand RD RS1 RS2) = False"
 | "is_notrd (Ior RD RS1 RS2) = False"
 | "is_notrd (Ixor RD RS1 RS2) = False"

 | "is_notrd (Iclri RD) = False"
 | "is_notrd (Isgri RD rs imm) = False"
 | "is_notrd (Iseqi RD rs imm) = False"
 | "is_notrd (Isgei RD rs imm) = False"
 | "is_notrd (Islsi RD rs imm) = False"
 | "is_notrd (Isnei RD rs imm) = False"
|  "is_notrd (Islei RD rs imm) = False"
 | "is_notrd (Iseti RD) = False"

 | "is_notrd (Iclr RD) = False"
 | "is_notrd (Isgr RD RS1 RS2) = False"
 | "is_notrd (Iseq RD RS1 RS2) = False"
 | "is_notrd (Isge RD RS1 RS2) = False"
 | "is_notrd (Isls RD RS1 RS2) = False"
 | "is_notrd (Isne RD RS1 RS2) = False"
 | "is_notrd (Isle RD RS1 RS2) = False"
 | "is_notrd (Iset RD) = False"

 | "is_notrd (Islli RD rs sa) = False"
 | "is_notrd (Isrli RD rs sa) = False"
 | "is_notrd (Israi RD rs sa) = False"
 | "is_notrd (Isll RD RS1 RS2) = False"
 | "is_notrd (Isrl RD RS1 RS2) = False"
 | "is_notrd (Isra RD RS1 RS2) = False"

 | "is_notrd (Ibeqz rs imm) = False"
 | "is_notrd (Ibnez rs imm) = False"
 | "is_notrd (Ijal imm) = False"
 | "is_notrd (Ijalr rs) = True"
 | "is_notrd (Ij imm) = False"
|  "is_notrd (Ijr rs) = True"

 | "is_notrd (Itrap imm) = False"
 | "is_notrd (Irfe) = False"

primrec is_onlyrd :: "instr \<Rightarrow> bool"
where
  "is_onlyrd (Ilb RD rs imm) = False"
  |"is_onlyrd (Ilh RD rs imm) = False"
 | "is_onlyrd (Ilw RD rs imm) = False"
 | "is_onlyrd (Ilbu RD rs imm) = False"
 | "is_onlyrd (Ilhu RD rs imm) = False"
 | "is_onlyrd (Isb RD rs imm) = False"
 | "is_onlyrd (Ish RD rs imm) = False"
 | "is_onlyrd (Isw RD rs imm) = False"

 | "is_onlyrd (Ilhgi RD imm) = False"
 | "is_onlyrd (Ilhg RD rs) = False"

 | "is_onlyrd (Imovs2i RD SA) = False"
 | "is_onlyrd (Imovi2s SA rs) = False"

 | "is_onlyrd (Iaddio RD rs imm) = False"
 | "is_onlyrd (Iaddi RD rs imm) = False"
 | "is_onlyrd (Isubio RD rs imm) = False"
 | "is_onlyrd (Isubi RD rs imm) = False"
 | "is_onlyrd (Iandi RD rs imm) = False"
 | "is_onlyrd (Iori RD rs imm) = False"
 | "is_onlyrd (Ixori RD rs imm) = False"

 | "is_onlyrd (Iaddo RD RS1 RS2) = False"
 | "is_onlyrd (Iadd RD RS1 RS2) = False"
 | "is_onlyrd (Isubo RD RS1 RS2) = False"
 | "is_onlyrd (Isub RD RS1 RS2) = False"
 | "is_onlyrd (Iand RD RS1 RS2) = False"
 | "is_onlyrd (Ior RD RS1 RS2) = False"
 | "is_onlyrd (Ixor RD RS1 RS2) = False"

 | "is_onlyrd (Iclri RD) = True"
 | "is_onlyrd (Isgri RD rs imm) = False"
 | "is_onlyrd (Iseqi RD rs imm) = False"
 | "is_onlyrd (Isgei RD rs imm) = False"
 | "is_onlyrd (Islsi RD rs imm) = False"
 | "is_onlyrd (Isnei RD rs imm) = False"
 | "is_onlyrd (Islei RD rs imm) = False"
|  "is_onlyrd (Iseti RD) = True"

 | "is_onlyrd (Iclr RD) = True"
 | "is_onlyrd (Isgr RD RS1 RS2) = False"
 | "is_onlyrd (Iseq RD RS1 RS2) = False"
 | "is_onlyrd (Isge RD RS1 RS2) = False"
 | "is_onlyrd (Isls RD RS1 RS2) = False"
 | "is_onlyrd (Isne RD RS1 RS2) = False"
 | "is_onlyrd (Isle RD RS1 RS2) = False"
 | "is_onlyrd (Iset RD) = True"

 | "is_onlyrd (Islli RD rs sa) = False"
 | "is_onlyrd (Isrli RD rs sa) = False"
 | "is_onlyrd (Israi RD rs sa) = False"
 | "is_onlyrd (Isll RD RS1 RS2) = False"
 | "is_onlyrd (Isrl RD RS1 RS2) = False"
 | "is_onlyrd (Isra RD RS1 RS2) = False"

 | "is_onlyrd (Ibeqz rs imm) = False"
 | "is_onlyrd (Ibnez rs imm) = False"
 | "is_onlyrd (Ijal imm) = False"
 | "is_onlyrd (Ijalr rs) = False"
|  "is_onlyrd (Ij imm) = False"
 | "is_onlyrd (Ijr rs) = False"

 | "is_onlyrd (Itrap imm) = False"
 | "is_onlyrd (Irfe) = False"

definition is_instr :: "instr \<Rightarrow> bool"
where  "is_instr iw == (is_regimm16 iw \<or> is_imm16 iw \<or> is_Ilhgi iw \<longrightarrow> asm_imm16 (imm_arg iw)) \<and>
                  (is_imm26 iw \<longrightarrow> asm_imm26 (imm_arg iw)) \<and>
                  (is_regsa iw \<longrightarrow> asm_sa (sa_arg iw)) \<and>
                  (is_2reg iw \<or> is_regimm16 iw \<or> is_regsa iw \<or> is_Ilhgi iw \<or> is_Imovs2i iw \<or> is_Ilhg iw \<or> is_onlyrd iw  \<longrightarrow> RD_arg iw < 32) \<and>
                  (is_2reg iw \<or> is_regimm16 iw \<or> is_regsa iw \<or> is_Imovi2s iw \<or> is_notrd iw \<or> is_imm16 iw \<longrightarrow> RS1_arg iw < 32) \<and>
                  (is_2reg iw \<or> is_Ilhg iw \<longrightarrow> RS2_arg iw < 32) \<and>
                  (is_Imovi2s iw \<or> is_Imovs2i iw \<longrightarrow> sa_arg iw < 32)"

lemma nop_is_instr[simp]: "is_instr Inop"
apply (simp add: is_instr_def Inop_def)
apply (simp add: asm_imm16_def)
done

definition is_asm_prog :: "instr list \<Rightarrow> bool"
where
  "is_asm_prog asm_prog \<equiv> list_all is_instr asm_prog"

primrec is_not_branch_and_store :: "instr \<Rightarrow> bool"
where
  "is_not_branch_and_store (Ilb RD rs imm) = True"
 | "is_not_branch_and_store (Ilh RD rs imm) = True"
 | "is_not_branch_and_store (Ilw RD rs imm) = True"
 | "is_not_branch_and_store (Ilbu RD rs imm) = True"
 | "is_not_branch_and_store (Ilhu RD rs imm) = True"
 | "is_not_branch_and_store (Isb RD rs imm) = False"
 | "is_not_branch_and_store (Ish RD rs imm) = False"
 | "is_not_branch_and_store (Isw RD rs imm) = False"

 | "is_not_branch_and_store (Ilhgi RD imm) = True"
 | "is_not_branch_and_store (Ilhg RD rs) = True"

 | "is_not_branch_and_store (Imovs2i RD SA) = False"
 | "is_not_branch_and_store (Imovi2s SA rs) = False"

 | "is_not_branch_and_store (Iaddio RD rs imm) = True"
 | "is_not_branch_and_store (Iaddi RD rs imm) = True"
 | "is_not_branch_and_store (Isubio RD rs imm) = True"
 | "is_not_branch_and_store (Isubi RD rs imm) = True"
 | "is_not_branch_and_store (Iandi RD rs imm) = True"
 | "is_not_branch_and_store (Iori RD rs imm) = True"
  |"is_not_branch_and_store (Ixori RD rs imm) = True"

 | "is_not_branch_and_store (Iaddo RD RS1 RS2) = True" 
 | "is_not_branch_and_store (Iadd RD RS1 RS2) = True"
 | "is_not_branch_and_store (Isubo RD RS1 RS2) = True"
 | "is_not_branch_and_store (Isub RD RS1 RS2) = True"
 | "is_not_branch_and_store (Iand RD RS1 RS2) = True"
 | "is_not_branch_and_store (Ior RD RS1 RS2) = True"
 | "is_not_branch_and_store (Ixor RD RS1 RS2) = True"

 | "is_not_branch_and_store (Iclri RD) = True"
 | "is_not_branch_and_store (Isgri RD rs imm) = True"
 | "is_not_branch_and_store (Iseqi RD rs imm) = True"
 | "is_not_branch_and_store (Isgei RD rs imm) = True"
 | "is_not_branch_and_store (Islsi RD rs imm) = True"
 | "is_not_branch_and_store (Isnei RD rs imm) = True"
 | "is_not_branch_and_store (Islei RD rs imm) = True"
 | "is_not_branch_and_store (Iseti RD) = True"

 | "is_not_branch_and_store (Iclr RD) = True"
 | "is_not_branch_and_store (Isgr RD RS1 RS2) = True"
 | "is_not_branch_and_store (Iseq RD RS1 RS2) = True"
 | "is_not_branch_and_store (Isge RD RS1 RS2) = True"
 | "is_not_branch_and_store (Isls RD RS1 RS2) = True"
 | "is_not_branch_and_store (Isne RD RS1 RS2) = True"
 | "is_not_branch_and_store (Isle RD RS1 RS2) = True"
 | "is_not_branch_and_store (Iset RD) = True"

 | "is_not_branch_and_store (Islli RD rs sa) = True"
 | "is_not_branch_and_store (Isrli RD rs sa) = True"
  |"is_not_branch_and_store (Israi RD rs sa) = True"
 | "is_not_branch_and_store (Isll RD RS1 RS2) = True"
 | "is_not_branch_and_store (Isrl RD RS1 RS2) = True"
 | "is_not_branch_and_store (Isra RD RS1 RS2) = True"

 | "is_not_branch_and_store (Ibeqz rs imm) = False"
 | "is_not_branch_and_store (Ibnez rs imm) = False"
 | "is_not_branch_and_store (Ijal imm) = False"
 | "is_not_branch_and_store (Ijalr rs) = False"
 | "is_not_branch_and_store (Ij imm) = False"
 | "is_not_branch_and_store (Ijr rs) = False"

 | "is_not_branch_and_store (Itrap imm) = False"
 | "is_not_branch_and_store (Irfe) = False"

definition is_not_branch_and_store_list :: "instr list \<Rightarrow> bool"
where
"is_not_branch_and_store_list l == list_all is_not_branch_and_store l"

primrec is_ovf_instr :: "instr \<Rightarrow> bool"
where
  "is_ovf_instr (Ilb RD rs imm) = False"
 | "is_ovf_instr (Ilh RD rs imm) = False"
 | "is_ovf_instr (Ilw RD rs imm) = False"
 | "is_ovf_instr (Ilbu RD rs imm) = False"
 | "is_ovf_instr (Ilhu RD rs imm) = False"
 | "is_ovf_instr (Isb RD rs imm) = False"
 | "is_ovf_instr (Ish RD rs imm) = False"
 | "is_ovf_instr (Isw RD rs imm) = False"

 | "is_ovf_instr (Ilhgi RD imm) = False"
  |"is_ovf_instr (Ilhg RD rs) = False"

 | "is_ovf_instr (Imovs2i RD SA) = False"
 | "is_ovf_instr (Imovi2s SA rs) = False"

 | "is_ovf_instr (Iaddio RD rs imm) = True"
 | "is_ovf_instr (Iaddi RD rs imm) = False"
 | "is_ovf_instr (Isubio RD rs imm) = True"
 | "is_ovf_instr (Isubi RD rs imm) = False"
 | "is_ovf_instr (Iandi RD rs imm) = False"
 | "is_ovf_instr (Iori RD rs imm) = False"
 | "is_ovf_instr (Ixori RD rs imm) = False"

 | "is_ovf_instr (Iaddo RD RS1 RS2) = True" 
 | "is_ovf_instr (Iadd RD RS1 RS2) = False"
 | "is_ovf_instr (Isubo RD RS1 RS2) = True"
 | "is_ovf_instr (Isub RD RS1 RS2) = False"
 | "is_ovf_instr (Iand RD RS1 RS2) = False"
 | "is_ovf_instr (Ior RD RS1 RS2) = False"
 | "is_ovf_instr (Ixor RD RS1 RS2) = False"

 | "is_ovf_instr (Iclri RD) = False"
 | "is_ovf_instr (Isgri RD rs imm) = False"
 | "is_ovf_instr (Iseqi RD rs imm) = False"
 | "is_ovf_instr (Isgei RD rs imm) = False"
 | "is_ovf_instr (Islsi RD rs imm) = False"
 | "is_ovf_instr (Isnei RD rs imm) = False"
 | "is_ovf_instr (Islei RD rs imm) = False"
 | "is_ovf_instr (Iseti RD) = False"

 | "is_ovf_instr (Iclr RD) = False"
 | "is_ovf_instr (Isgr RD RS1 RS2) = False"
 | "is_ovf_instr (Iseq RD RS1 RS2) = False"
 | "is_ovf_instr (Isge RD RS1 RS2) = False"
 | "is_ovf_instr (Isls RD RS1 RS2) = False"
 | "is_ovf_instr (Isne RD RS1 RS2) = False"
 | "is_ovf_instr (Isle RD RS1 RS2) = False"
 | "is_ovf_instr (Iset RD) = False"

 | "is_ovf_instr (Islli RD rs sa) = False"
 | "is_ovf_instr (Isrli RD rs sa) = False"
 | "is_ovf_instr (Israi RD rs sa) = False"
 | "is_ovf_instr (Isll RD RS1 RS2) = False"
 | "is_ovf_instr (Isrl RD RS1 RS2) = False"
 | "is_ovf_instr (Isra RD RS1 RS2) = False"

 | "is_ovf_instr (Ibeqz rs imm) = False"
 | "is_ovf_instr (Ibnez rs imm) = False"
 | "is_ovf_instr (Ijal imm) = False"
 | "is_ovf_instr (Ijalr rs) = False"
 | "is_ovf_instr (Ij imm) = False"
 | "is_ovf_instr (Ijr rs) = False"

 | "is_ovf_instr (Itrap imm) = False"
 | "is_ovf_instr (Irfe) = False"

lemma is_ovf_instr_deff:
 "is_ovf_instr i \<equiv>
  (\<exists>nat1 nat2 int. i = Iaddio nat1 nat2 int) \<or>
  (\<exists>nat1 nat2 int. i = Isubio nat1 nat2 int) \<or>
  (\<exists>nat1 nat2 nat3. i = Iaddo nat1 nat2 nat3) \<or>
  (\<exists>nat1 nat2 nat3. i = Isubo nat1 nat2 nat3)"
 by (rule eq_reflection) (case_tac i, simp_all)

definition is_instr_non_ovf :: "instr \<Rightarrow> bool"
where  "is_instr_non_ovf i \<equiv> is_instr i \<and> \<not> is_ovf_instr i"

definition is_store :: "instr \<Rightarrow> bool"
where
  "is_store iw == \<exists> rd rs imm. iw \<in> {Isb rd rs imm, Ish rd rs imm, Isw rd rs imm}"

definition is_storew :: "instr \<Rightarrow> bool"
where
  "is_storew iw == \<exists> rd rs imm. iw = Isw rd rs imm"

definition is_load_store_word :: "instr \<Rightarrow> bool"
where
  "is_load_store_word iw \<equiv> (\<exists> rd rs imm. iw \<in> {Ilw rd rs imm, Isw rd rs imm})"

definition is_load_store_hword:: "instr \<Rightarrow> bool"
where
"is_load_store_hword iw \<equiv> (\<exists> rd rs imm. iw \<in> {Ilh rd rs imm, Ilhu rd rs imm, Ish rd rs imm})"

definition  is_load_store_byte :: "instr \<Rightarrow> bool"
where
  "is_load_store_byte iw \<equiv> (\<exists> rd rs imm. iw \<in> {Ilb rd rs imm, Ilbu rd rs imm, Isb rd rs imm})"

definition is_load_store :: "instr \<Rightarrow> bool"
where
  "is_load_store iw \<equiv> is_load_store_word iw \<or> is_load_store_hword iw \<or> is_load_store_byte iw"

definition load_store_access_width :: "instr \<Rightarrow> nat"
where
  "load_store_access_width i \<equiv> 
   (
     if is_load_store_word i then 4
     else if is_load_store_hword i then 2
     else 1
   )
  "

definition is_Itrap :: "instr \<Rightarrow> bool"
where
  "is_Itrap i \<equiv> (\<exists> x. i = Itrap x)"

definition is_Irfe :: "instr \<Rightarrow> bool"
where
  "is_Irfe i \<equiv> (i=Irfe)"

definition is_system_instr :: "instr \<Rightarrow> bool"
where
  "is_system_instr i \<equiv> is_Imovs2i i \<or> is_Imovi2s i \<or> is_Itrap i \<or> is_Irfe i"

definition is_not_branch_and_mem_access :: "instr \<Rightarrow> bool"
where
  "is_not_branch_and_mem_access i \<equiv> is_not_branch_and_store i \<and> \<not> is_load_store i"

lemma is_instr_non_ovf_imp_is_instr:
assumes "list_all is_instr_non_ovf x"
  shows "list_all is_instr x"
using assms
by (simp add: list_all_eq_all_nth is_instr_non_ovf_def)


definition is_arith :: "instr \<Rightarrow> bool"
where
"is_arith i = (\<exists> RD rs imm RS1 RS2. i \<in> {(Iaddio RD rs imm), (Iaddi RD rs imm), (Isubio RD rs imm),
                                         (Isubi RD rs imm), (Iaddo RD RS1 RS2), (Iadd RD RS1 RS2),
                                         (Isubo RD RS1 RS2), (Isub RD RS1 RS2)})"

definition is_logic :: "instr \<Rightarrow> bool"
where
"is_logic i = (\<exists> RD rs imm RS1 RS2. i \<in> {(Iandi RD rs imm), (Iori RD rs imm), (Ixori RD rs imm),
                                         (Iand RD RS1 RS2), (Ior RD RS1 RS2), (Ixor RD RS1 RS2)})"



end
