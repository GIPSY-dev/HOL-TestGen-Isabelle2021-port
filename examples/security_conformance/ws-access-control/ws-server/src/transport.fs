
module transport

open core

let public toEntryStatus x =
  match x with
    | "Open"   -> Open
    | "open"   -> Open
    | "Closed" -> Closed
    | "closed" -> Closed
    | _        -> Open    // default

let public toUserRole x = 
  match x with
    | "Clerical"              -> Clerical
    | "clerical"              -> Clerical
    | "Nurse"                 -> Nurse
    | "nurse"                 -> Nurse
    | "ClinicalPractitioner"  -> ClinicalPractitioner
    | "clinicalpractitioner"  -> ClinicalPractitioner
    | "Clinical Practitioner" -> ClinicalPractitioner
    | "clinical practitioner" -> ClinicalPractitioner
    | _ -> Clerical
