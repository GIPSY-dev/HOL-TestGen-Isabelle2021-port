module myList

open Microsoft.FSharp.Collections;

let sort (l:int List) = List.ofArray (csList.sort (List.toArray l));
