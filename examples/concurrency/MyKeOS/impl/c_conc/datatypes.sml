 
  (********************************************************)
  (* This file is generated automatically. Do not edit    *)
  (********************************************************)


structure Datatypes : sig
  type int
  type in_c
  type out_c
  val program_dum_conc :
    (int * int -> int option) -> in_c -> out_c -> int * int -> int option
end = struct

datatype int = Int_of_integer of IntInf.int;

fun integer_of_int (Int_of_integer k) = k;

fun equal_inta k l = (((integer_of_int k) : IntInf.int) = (integer_of_int l));

type 'a equal = {equal : 'a -> 'a -> bool};
val equal = #equal : 'a equal -> 'a -> 'a -> bool;

val equal_int = {equal = equal_inta} : int equal;

fun eq A_ a b = equal A_ a b;

fun equal_proda A_ B_ (x1, x2) (y1, y2) = eq A_ x1 y1 andalso eq B_ x2 y2;

fun equal_prod A_ B_ = {equal = equal_proda A_ B_} : ('a * 'b) equal;

datatype nat = Nat of IntInf.int;

datatype in_c = Send of int * int * nat | Rec of int * int * nat |
  Status of int;

datatype out_c = Send_ok | Rec_ok | Status_ok of nat;

fun fun_upd A_ f a b = (fn x => (if eq A_ x a then b else f x));

val zero_int : int = Int_of_integer (0 : IntInf.int);

fun program_dum_conc sigma a outs =
  fun_upd (equal_prod equal_int equal_int) (fn _ => NONE) (zero_int, zero_int)
    (SOME zero_int);

end; (*struct Datatypes*)
