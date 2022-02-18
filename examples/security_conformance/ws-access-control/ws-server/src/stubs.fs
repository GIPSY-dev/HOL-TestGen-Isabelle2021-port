
module stubs

open System.Web.Services.Protocols

type User = int
type Patient = int
type EntryId = int
type LrId = int

type EntryStatus = Open
                 | Closed
                                                          
type Role = ClinicalPractitioner 
          | Nurse 
          | Clerical 

type Entry = EntryStatus * (User * string)

let fromEntryStatus x =
  match x with
    | Open   -> "Open"
    | Closed -> "Closed"

let fromUserRole x =
  match x with
    | Clerical             -> "Clerical"
    | Nurse                -> "Nurse"
    | ClinicalPractitioner -> "ClinicalPractitioner"


type 'a decision = Allow of 'a
                 | Deny of 'a

let guard (x : 'a Lazy) : unit decision =
  try ignore <| x.Force ()
      Allow ()
  with
    | e -> Deny ()

let dummyContent : string = "dummyContent";;

let hc = new HealthCare()

let createSCR (user:User) (role:Role) (patient:Patient) =
  guard <| lazy (hc.createSCR (user, fromUserRole role, patient))

let appendEntry (user:User) (role:Role) (patient:Patient) (entry_id:EntryId)
                (entry: Entry) =
  match entry with
    | (status, (creator, content)) ->
      guard <| lazy (hc.appendEntry (user, fromUserRole role, patient, entry_id,
                                     fromEntryStatus status, creator, content))

let deleteEntry (user:User) (role:Role) (patient:Patient) (entry_id:EntryId) =
  guard <| lazy (hc.deleteEntry (user, fromUserRole role, patient, entry_id))

let readEntry (user:User) (role:Role) (patient:Patient) (entry_id:EntryId) =
  guard <| lazy (hc.readEntry (user, fromUserRole role, patient, entry_id))

let readSCR (user:User) (role:Role) (patient:Patient) =
  guard <| lazy (hc.readSCR (user, fromUserRole role, patient))

let changeStatus (user:User) (role:Role) (patient:Patient) (entry_id:EntryId)
                 (status:EntryStatus) =
  guard <| lazy (hc.changeStatus (user, fromUserRole role, patient, entry_id,
                                  fromEntryStatus status))

let deleteSCR (user:User) (role:Role) (patient:Patient) =
  guard <| lazy (hc.deleteSCR (user, fromUserRole role, patient))

let editEntry (user:User) (role:Role) (patient:Patient) (entry_id:EntryId)
              (entry:Entry) =
  match entry with
    | (status, (creator, content)) ->
      guard <| lazy (hc.editEntry (user, fromUserRole role, patient, entry_id,
                                   content))

let addLR (user:User) (role:Role) (patient:Patient) (lr_id:LrId)
          (users: User Set) =
  guard <| lazy (hc.addLR (user, fromUserRole role, lr_id, patient,
                           Set.toArray users))

let removeLR (user:User) (role:Role) (patient:Patient) lr_id =
  guard <| lazy (hc.removeLR (user, fromUserRole role, lr_id))

let reset () =
  hc.reset ()

