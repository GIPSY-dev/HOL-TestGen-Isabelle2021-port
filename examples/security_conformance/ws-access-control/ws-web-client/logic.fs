
module logic


open System.Web
open System.Web.UI.HtmlControls

// first one is the default user
let users     = ["Alice";    "Bob";                   "Charlie"    ]
let userRole  = ["Nurse";    "Clinical Practitioner"; "Clerical"   ]
let userStyle = ["blue.css"; "red.css";               "orange.css" ]
let patients  = ["Smith"; "Johnson"; "Williams"; "Jones"; "Brown"; "Davis";
                 "Miller"; "Wilson"; "Moore"; "Taylor"; "Anderson"; "Thomas";
                 "Jackson"; "White"; "Harris"; "Martin"; "Thompson"; "Garcia";
                 "Martinez"; "Robinson"; "Clark"; "Rodriguez"; "Lewis"; "Lee";
                 "Walker"; "Hall"; "Allen"; "Young"; "Hernandez"; "King";
                 "Wright"; "Lopez"; "Hill"; "Scott"; "Green"; "Adams"; "Baker";
                 "Gonzalez"; "Nelson"; "Carter"; "Mitchell"; "Perez"; "Roberts";
                 "Turner"; "Phillips"; "Campbell"; "Parker"; "Evans"; "Edwards";
                 "Collins"; "Stewart"; "Sanchez"; "Morris"; "Rogers"; "Reed";
                 "Cook"; "Morgan"; "Bell"; "Murphy"; "Bailey"; "Rivera";
                 "Cooper"; "Richardson"; "Cox"; "Howard"; "Ward"; "Torres";
                 "Peterson"; "Gray"; "Ramirez"; "James"; "Watson"; "Brooks";
                 "Kelly"; "Sanders"; "Price"; "Bennett"; "Wood"; "Barnes";
                 "Ross"; "Henderson"; "Coleman"; "Jenkins"; "Perry"; "Powell";
                 "Long"; "Patterson"; "Hughes"; "Flores"; "Washington";
                 "Butler"; "Simmons"; "Foster"; "Gonzales"; "Bryant";
                 "Alexander"; "Russell"; "Griffin"; "Diaz"; "Hayes" ]

let lookup b bs cs =
  List.zip bs cs
  |> List.tryFind (fst >> ((=) b))
  |> function 
     | Some u -> snd u
     | None   -> List.head cs

let getStyle (user : string) = lookup user users userStyle
let getRole (user : string) = lookup user users userRole
let getPatient (id : int) = if id > patients.Length || id < 0
                              then id.ToString ()
                              else patients.[id]

let userToID (user : string) =
  List.tryFindIndex ((=) user) users
  |> function
     | Some u -> u + 1
     | None   -> -1

let entryToID (entry : string) = int(entry)

let patientToID (p : string) : int =
  List.tryFindIndex ((=) p) patients
  |> function
     | Some u -> u
     | None   -> -1

let createLink arg value all labels =
  let printLine (v,l) = if v = value
                          then "<li class=\"selected\">"
                          else "<li>"
                        + "<a href=\"?" + arg + "=" + v + "\">" + l + "</a></li>"
  in List.zip all labels
     |> List.map printLine
     |> List.fold (+) ""

let createUserLink (current : string) = createLink "user" current users users

let groupSeq (f : 'a -> bool) (a : 'a list) : 'a list list = 
  let step u (v::vs) = if f u then (u :: v) :: vs
                              else ([] :: v :: vs)
  List.foldBack step a [[]]
  |> List.filter ((<>) [])

let parseUsers (users : string) =
  let isAlphaNumeric c = 'a' <= c && c <= 'z' ||
                         'A' <= c && c <= 'Z' ||
                         '0' <= c && c <= '9'
  List.ofSeq users
  |> groupSeq isAlphaNumeric
  |> List.map (fun x -> userToID (new string(Seq.toArray x)))
  |> Array.ofList

let encode = HttpUtility.HtmlEncode

let evalResultEnc (res : HtmlGenericControl) (f: 'a -> string) (enc: bool) (x : 'a Lazy) : 'a option =
              try let v = x.Force ()
                  in res.InnerHtml <- (if enc then encode <| f v
                                              else f v);
                     res.Attributes.["class"] <- "success";
                     Some v
              with
                | _ -> res.InnerHtml <- "Failed"
                       res.Attributes.["class"] <- "failed"
                       None

let evalResult (res : HtmlGenericControl) (f: 'a -> string) (x : 'a Lazy) : 'a option =
    evalResultEnc res f false x

let eval (res : HtmlGenericControl) (x : 'a Lazy) : 'a option
  = evalResult res (fun _ -> "Success") x


let h = new HealthCare();

let createSCR user role scrID res =
  eval res <| lazy (h.createSCR (userToID user, role, scrID))

let deleteSCR user role scrID res =
  eval res <| lazy (h.deleteSCR (userToID user, role, scrID))

let addLR (user : string)  (role : string) (lrID : int) (lrScrID : int) (lrUserIDs : int []) res =
  eval res <| lazy (h.addLR (userToID user, role, lrID, lrScrID, lrUserIDs))

let removeLR user role lrID res =
  eval res <| lazy (h.removeLR (userToID user, role, lrID))

let appendEntry user role scrID entryID data status res =
  eval res <| lazy (h.appendEntry (userToID user, role, scrID,
                                   entryToID entryID, status, userToID user,
                                   data)); 

let deleteEntry user role scrID entryID res =
  eval res <| lazy (h.deleteEntry (userToID user, role, scrID,
                                   entryToID entryID))

let changeStatus user role scrID entryID status res =
  eval res <| lazy (h.changeStatus(userToID user, role, scrID, entryToID entryID,
                                   status))

let editEntry user role scrID entryID data res =
  eval res <| lazy (h.editEntry(userToID user, role, scrID, entryToID entryID,
                                data))

let readEntry user role scrID entryID res =
  evalResultEnc res id true <| lazy (h.readEntry(userToID user, role, scrID,
                                                 entryToID entryID))

let readSCR user role scrID res =
  let print = Array.map (fun x -> "<li>" + encode x + "</li>") 
              >> Array.fold (+) "Success:<ul>"
              >> fun x -> x + "</ul>"
  in evalResult res print <| lazy (h.readSCR(userToID user, role, scrID))


// View State operation
let views =     [ "lr";       "scr";       "all"      ]
let viewTitle = [ "View LRs"; "View SCRs"; "View all" ]

let createViewLink (view : string) = createLink "view" view views viewTitle

type View = LR  = 1
          | SCR = 2
          | ALL = 4

let determinateView view =
  match view with
  | "scr" -> View.SCR
  | "all" -> View.ALL
  | _     -> View.LR


let showAt (view : View) (current : View) content =
  if (int view &&& int current) <> 0
    then content
    else ""

let replaceScrIDs s =
  let replaceID (x : string) (id, name) = x.Replace("$" + id.ToString () + "$", name)
  List.zip [0..patients.Length-1] patients
  |> List.fold replaceID s
  |> fun x -> x.Replace("$", "")

let dumpLRs () =
  h.dumpLRs("<tr><td>%lrid</td><td>$%scrid$</td><td>%users</td></tr>")
  |> replaceScrIDs

let dumpSCR scrID =
  h.dumpSCR(scrID, "<tr><td>%id</td><td>%creator</td><td>%status</td><td>%data</td></tr>")

let printSCRidLinks () =
  h.dumpSCRids ()
  |> Array.map (fun id -> "<li><a href=\"?view=scr&amp;id=" + id.ToString() + "\">"
                          + id.ToString() + "</a></li>")
  |> Array.fold (+) ""
  |> fun content -> "<ul class=\"scrlinks\">" + content + "</ul>"
  

let printTable cap headers body =
  let head = headers
             |> List.map (fun x -> "<th>" + x + "</th>")
             |> List.fold (+) ""
  "<table><caption>" + cap + "</caption><thead>" + head + "</thead><tbody>"
  + body + "</tbody></table>" 

let printLrTable () =
  let head = [ "Legitimate Relationship ID"; "Patient"; "Authorized Users" ]
  printTable "Legitimate Relationships" head (dumpLRs ())

let printScrTable id =
  let head = ["Entry id"; "Creator"; "Entry status"; "Entry data"]
  printTable (getPatient id) head (dumpSCR id)

let printScrTables () =
  h.dumpSCRids ()
  |> Array.map printScrTable
  |> Array.fold (+) ""
