 
  (********************************************************)
  (* This file is generated automatically. Do not edit    *)
  (********************************************************)


structure Datatypes : sig
  datatype int = Int_of_integer of IntInf.int
  datatype nat = Nat of IntInf.int
  datatype in_c = Alloc of int * int * nat | Release of int * int * nat |
    Status of int * int
  datatype out_c = Alloc_ok | Release_ok | Status_ok of nat
  val zero_int : int
  val program_dum : int -> in_c -> out_c -> int
end = struct

datatype int = Int_of_integer of IntInf.int;

datatype nat = Nat of IntInf.int;

datatype in_c = Alloc of int * int * nat | Release of int * int * nat |
  Status of int * int;

datatype out_c = Alloc_ok | Release_ok | Status_ok of nat;

val zero_int : int = Int_of_integer 0;

fun program_dum x a outs = zero_int;

end; (*struct Datatypes*)
