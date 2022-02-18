
module main

open core

let alice = 1
let bob = 2
let charlie = 3

let users = [(alice, [Nurse]);
             (bob,  [ClinicalPractitioner]);
             (charlie, [Clerical])];

let public createSCR scrID =
  modifyScrs <| Map.add scrID emptySCR
  |> guard <| (byUsers users <&&> byRoles [Clerical]
               <&&> (wNot <| scrExists scrID))


let public appendEntry scrID entryID (status:EntryStatus) creator data =
  modifyEntries scrID <| Map.add entryID ({ data = data
                                            status = status
                                            creator = creator
                                          } : ScrEntry)
  |> guard <| (byUsers users <&&> byRoles [ClinicalPractitioner] <&&> byLR scrID
               <&&> scrExists scrID <&&> (wNot <| entryExists scrID entryID))

let public deleteEntry scrID entryID =
  modifyEntries scrID <| Map.remove entryID
  |> guard <| (byUsers users <&&> byRoles [ClinicalPractitioner]
               <&&> byCreator scrID entryID <&&> entryExists scrID entryID)
            
let public readEntry scrID entryID =
  gets (getScrs >> Map.find scrID >>
        getEntries >> Map.find entryID >>
        getData)
  |> guard <| (byUsers users <&&> byRoles [Nurse; ClinicalPractitioner]
               <&&> byLR scrID
               <&&> (byCreator scrID entryID <||> byStatus scrID entryID Open)
               <&&> entryExists scrID entryID)

let public readScr scrID =
  reads getUserID >>= fun creator ->
  gets (getScrs >> Map.find scrID >>
        getEntries >> Map.toArray >>
        Array.map snd >>
        Array.filter (fun entry -> entry.status = Open ||
                                   entry.creator = creator) >>
        Array.map getData)
  |> guard <| (byUsers users <&&> byRoles [Nurse; ClinicalPractitioner] <&&>
               byLR scrID <&&> scrExists scrID)

let public addLR lrID scrID userIDs = 
  modifyLRs <| Map.add lrID { scrId   = scrID
                              userIds = Set.ofArray userIDs
                            }
  |> guard <| (byUsers users <&&> byRoles [Clerical] <&&>
               (wNot <| lrExists lrID))

let public removeLR lrID = 
  modifyLRs <| Map.remove lrID
  |> guard <| (byUsers users <&&> byRoles [Clerical] <&&> lrExists lrID)

let public changeStatus scrID entryID status =
  modifyEntry scrID entryID <| fun entry ->
                               { entry with status = status }
  |> guard <| (byUsers users <&&> byRoles [ClinicalPractitioner] <&&>
               byCreator scrID entryID <&&> entryExists scrID entryID)

let public deleteSCR scrID =
  modifyScrs <| Map.remove scrID
  |> guard <| (byUsers users <&&> byRoles [Clerical] <&&> byLR scrID <&&>
               scrExists scrID)

let public editEntry scrID entryID data =
  modifyEntry scrID entryID <| fun entry ->
                               { entry with data = data }
  |> guard <| (byUsers users <&&> byRoles [ClinicalPractitioner] <&&>
               byCreator scrID entryID <&&> entryExists scrID entryID)


(*************************************
 Backdoor access
 *************************************)

let encode = System.Web.HttpUtility.HtmlEncode

let userToString x =
  if x = alice    then "Alice"   else
  if x = bob      then "Bob"     else
  if x = charlie  then "Charlie" else
                       "Unnamed"

let public dumpLRs wstate (template : string) =
  let step accm user = match accm with
                        | "" -> userToString user
                        | l  -> l + ", " + userToString user
  let dumpSet s = Set.fold step "" s
  let dump (id,lr : LR) =
    template.Replace("%lrid", encode <| id.ToString())
            .Replace("%users", dumpSet lr.userIds)
            .Replace("%scrid", encode <| lr.scrId.ToString())
  wstate.lrs
  |> Map.toArray |> Array.map dump
  |> Array.fold (+) ""

let public dumpSCRids wstate =
  wstate.scrs
  |> Map.toArray 
  |> Array.map fst

let public dumpSCR wstate scrID (template : string) =
  let dumpStatus s =
    match s with
    | Open   -> "Open"
    | Closed -> "Closed"

  let dump (id, entry) =
    template.Replace("%id", encode <| id.ToString())
            .Replace("%creator", encode <| userToString entry.creator)
            .Replace("%status", dumpStatus entry.status)
            .Replace("%data", encode <| entry.data)
  wstate.scrs
  |> Map.find scrID 
  |> getEntries
  |> Map.toArray
  |> Array.map dump
  |> Array.fold (+) ""
  



let public initialState = emptyState

