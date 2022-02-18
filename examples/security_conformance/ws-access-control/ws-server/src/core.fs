
module core

open System
open monad

// Helper functions
let elemOf x xs = List.exists ((=) x) xs
let flip f x y = f y x

type EntryStatus = Open
                 | Closed

type ScrID = int
type UserID = int
type LrID = int
type EntryID = int

// Summary Healthcare Record
type SCR = {
  entries : Map<EntryID, ScrEntry>
}
and ScrEntry = {
  data : string
  status : EntryStatus
  creator : UserID
}

let public emptySCR = { entries = new Map<EntryID, ScrEntry>([])
                      } : SCR

let public getEntries scr = scr.entries

let public getData entry = entry.data
let public getCreator entry = entry.creator
let public getStatus entry = entry.status

// Each user is in excactly one of these roles
type UserRole = Clerical
              | Nurse
              | ClinicalPractitioner

// Legitimate Relationship between a user and a Care Record
type LR = {
  userIds : UserID Set
  scrId : ScrID
}

let public getLrUserId lr = lr.userIds
let public getLrScrId lr = lr.scrId

// Reader type of the W Monad
type WRead = {
  userID: UserID;
  userRole: UserRole;
}

let public getUserID wread = wread.userID;
let public getUserRole wread = wread.userRole;

let public createWRead userId role = { userID = userId;
                                       userRole = role;
                                     }

// State of the W Monad
type WState = {
  scrs : Map<ScrID, SCR>
  lrs: Map<LrID, LR>
}

let public emptyState = { 
                          scrs = new Map<ScrID, SCR>([]);
                          lrs = new Map<LrID, LR>([]);
                        } : WState

let public getScrs wstate = wstate.scrs
let public getLRs wstate = wstate.lrs

// W Monad
type public 'a W = private W of (WRead -> WState -> ('a * WState) option)

let unW (W x) = x

let ret x = W <| pureReaderT (pureStateT pureOption) x
let (>>=) (W x) wy = W <| bindReaderT (bindStateT bindOption) x (wy >> unW)
let (>>-) x y = x >>= fun _ -> y

type WBuilder() =
  member b.Return x = ret x
  member b.Bind (x,f) = x >>= f

let wDo = WBuilder()

type WResult<'a> = {
  value : 'a
  state : WState
}

let getResult p =
  match p with
    | Some (r,s) -> { value = r; state = s }
    | None       -> raise (new UnauthorizedAccessException ("Failed to pass guard"))


let runW r s (W x) = getResult (runReaderT r x |> runStateT s)

let read = W <| readT (pureStateT pureOption)
let reads f = read >>= (f >> ret)
let get  = W <| liftReaderT (getT pureOption)
let gets f = get >>= (f >> ret)
let put s = W <| liftReaderT (putT pureOption s)
let modify f = get >>= (f >> put)

let abort () : 'a W = W <| pureReaderT (pureStateT (fun _ -> None) ())

let liftW f a = a >>= (f >> ret)
let liftW2 f a b = a >>= fun a' -> b >>= fun b' -> ret (f a' b')

let modifyScrs f = modify <| fun state -> { state with scrs = f state.scrs }
let modifyLRs f  = modify <| fun state -> { state with lrs = f state.lrs }
let modifyScr scrID f =
  modifyScrs <| fun scrs ->
                Map.add scrID (Map.find scrID scrs |> f) scrs

let modifyEntries scrID f =
  modifyScr scrID <| fun scr ->
                     { scr with entries = f scr.entries }

let modifyEntry scrID entryID f =
  modifyEntries scrID <| fun entries ->
                         Map.add entryID (Map.find entryID entries |> f) entries

let userRoleToString x =
  match x with
    | Clerical             -> "Clerical"
    | Nurse                -> "Nurse"
    | ClinicalPractitioner -> "ClinicalPractitioner"


// Policy enforcer function
let guard action b =
  b >>= fun b' ->
  if b'
    then action
    else abort ()

let (<&&>) = liftW2 (&&)
let (<||>) = liftW2 (||)
let wNot = liftW not

let byUsers (users : (UserID * (UserRole list)) list) =
  reads <| fun wr ->
             let userMap = Map.ofList users
             match Map.tryFind wr.userID userMap with
             | Some roles -> List.exists ((=) wr.userRole) roles
             | None       -> false

let byRoles (roles : UserRole list) = reads (getUserRole >> flip elemOf roles)

let byLR (scrID : ScrID) =
  reads getUserID >>= fun userID ->
  let validLR _ lr = getLrScrId lr = scrID &&
                     Set.contains userID (getLrUserId lr)
  gets (getLRs >> Map.exists validLR)

let byCreator scrID entryID =
  liftW2 (=)
          <| reads getUserID
          <| gets (getScrs >> Map.find scrID >>
                   getEntries >> Map.find entryID >>
                   getCreator)

let byStatus scrID entryID status =
  liftW ((=) status)
        <| gets (getScrs >> Map.find scrID >>
                 getEntries >> Map.find entryID >>
                 getStatus)

let scrExists scrID =
  gets (getScrs >> Map.containsKey scrID)

let entryExists scrID entryID =
  scrExists scrID <&&> gets (getScrs >> Map.find scrID >>
                             getEntries >> Map.containsKey entryID)


let lrExists lrID =
  gets (getLRs >> Map.containsKey lrID)
