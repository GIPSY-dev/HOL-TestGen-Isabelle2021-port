 
  (********************************************************)
  (* This file is generated automatically. Do not edit    *)
  (********************************************************)


structure TestScript : sig
  type 'a equal
  val equal : 'a equal -> 'a -> 'a -> bool
  val eq : 'a equal -> 'a -> 'a -> bool
  datatype num = One | Bit0 of num | Bit1 of num
  val integer_of_nat : Datatypes.nat -> IntInf.int
  val plus_nat : Datatypes.nat -> Datatypes.nat -> Datatypes.nat
  val one_nat : Datatypes.nat
  val suc : Datatypes.nat -> Datatypes.nat
  val fun_upd : 'a equal -> ('a -> 'b) -> 'a -> 'b -> 'a -> 'b
  val integer_of_int : Datatypes.int -> IntInf.int
  val equal_inta : Datatypes.int -> Datatypes.int -> bool
  val equal_int : Datatypes.int equal
  val zero_int : Datatypes.int
  val mbind :
    'a list -> ('a -> 'b -> ('c * 'b) option) -> 'b -> ('c list * 'b) option
  val zero_nat : Datatypes.nat
  val equal_nat : Datatypes.nat -> Datatypes.nat -> bool
  type 'a ord
  val less_eq : 'a ord -> 'a -> 'a -> bool
  val less : 'a ord -> 'a -> 'a -> bool
  val max : 'a ord -> 'a -> 'a -> 'a
  val bind_SE :
    ('a -> ('b * 'a) option) ->
      ('b -> 'a -> ('c * 'a) option) -> 'a -> ('c * 'a) option
  val unit_SE : 'a -> 'b -> ('a * 'b) option
  val equal_list : 'a equal -> 'a list -> 'a list -> bool
  val valid_SE : 'a -> ('a -> (bool * 'a) option) -> bool
  val equal_out_ca : Datatypes.out_c -> Datatypes.out_c -> bool
  val equal_out_c : Datatypes.out_c equal
  val equal_proda : 'a equal -> 'b equal -> 'a * 'b -> 'a * 'b -> bool
  val equal_prod : 'a equal -> 'b equal -> ('a * 'b) equal
  val ord_integer : IntInf.int ord
  val nat_of_integer : IntInf.int -> Datatypes.nat
  val test_script : ((unit -> bool) list * (unit -> bool)) list
end = struct

type 'a equal = {equal : 'a -> 'a -> bool};
val equal = #equal : 'a equal -> 'a -> 'a -> bool;

fun eq A_ a b = equal A_ a b;

datatype num = One | Bit0 of num | Bit1 of num;

fun integer_of_nat (Datatypes.Nat ( x )) = x;

fun plus_nat m n =
  (Datatypes.Nat ( (IntInf.+ (integer_of_nat m, integer_of_nat n)) ));

val one_nat : Datatypes.nat = (Datatypes.Nat ( (1 : IntInf.int) ));

fun suc n = plus_nat n one_nat;

fun fun_upd A_ f a b = (fn x => (if eq A_ x a then b else f x));

fun integer_of_int (Datatypes.Int_of_integer ( k )) = k;

fun equal_inta k l = (((integer_of_int k) : IntInf.int) = (integer_of_int l));

val equal_int = {equal = equal_inta} : Datatypes.int equal;

val zero_int : Datatypes.int = (Datatypes.Int_of_integer ( 0 ));

fun mbind [] iostep sigma = SOME ([], sigma)
  | mbind (a :: h) iostep sigma =
    (case iostep a sigma of NONE => SOME ([], sigma)
      | SOME (out, sigmaa) =>
        (case mbind h iostep sigmaa of NONE => SOME ([out], sigmaa)
          | SOME (outs, sigmab) => SOME (out :: outs, sigmab)));

val zero_nat : Datatypes.nat = (Datatypes.Nat ( 0 ));

fun equal_nat m n = (((integer_of_nat m) : IntInf.int) = (integer_of_nat n));

type 'a ord = {less_eq : 'a -> 'a -> bool, less : 'a -> 'a -> bool};
val less_eq = #less_eq : 'a ord -> 'a -> 'a -> bool;
val less = #less : 'a ord -> 'a -> 'a -> bool;

fun max A_ a b = (if less_eq A_ a b then b else a);

fun bind_SE f g =
  (fn sigma => (case f sigma of NONE => NONE | SOME (a, b) => g a b));

fun unit_SE e = (fn sigma => SOME (e, sigma));

fun equal_list A_ (a :: lista) [] = false
  | equal_list A_ [] (a :: lista) = false
  | equal_list A_ (aa :: listaa) (a :: lista) =
    eq A_ aa a andalso equal_list A_ listaa lista
  | equal_list A_ [] [] = true;

fun valid_SE sigma m = (case m sigma of NONE => false | SOME (x, _) => x);

fun equal_out_ca (Datatypes.Status_ok ( nat )) Datatypes.Release_ok  = false
  | equal_out_ca Datatypes.Release_ok  (Datatypes.Status_ok ( nat )) = false
  | equal_out_ca (Datatypes.Status_ok ( nat )) Datatypes.Alloc_ok = false
  | equal_out_ca Datatypes.Alloc_ok (Datatypes.Status_ok ( nat )) = false
  | equal_out_ca Datatypes.Release_ok  Datatypes.Alloc_ok = false
  | equal_out_ca Datatypes.Alloc_ok Datatypes.Release_ok  = false
  | equal_out_ca (Datatypes.Status_ok ( nata )) (Datatypes.Status_ok ( nat )) =
    equal_nat nata nat
  | equal_out_ca Datatypes.Release_ok  Datatypes.Release_ok  = true
  | equal_out_ca Datatypes.Alloc_ok Datatypes.Alloc_ok = true;

val equal_out_c = {equal = equal_out_ca} : Datatypes.out_c equal;

fun equal_proda A_ B_ (aa, ba) (a, b) = eq A_ aa a andalso eq B_ ba b;

fun equal_prod A_ B_ = {equal = equal_proda A_ B_} : ('a * 'b) equal;

val ord_integer =
  {less_eq = (fn a => fn b => IntInf.<= (a, b)),
    less = (fn a => fn b => IntInf.< (a, b))}
  : IntInf.int ord;

fun nat_of_integer k = (Datatypes.Nat ( (max ord_integer 0 k) ));

val test_script : ((unit -> bool) list * (unit -> bool)) list =
  [([], fn () => valid_SE
                   (fun_upd (equal_prod equal_int equal_int) (fn _ => NONE)
                     ((Datatypes.Int_of_integer ( (~8 : IntInf.int) )),
                       (Datatypes.Int_of_integer ( (1 : IntInf.int) )))
                     (SOME (Datatypes.Int_of_integer ( (10 : IntInf.int) ))))
                   (bind_SE
                     (mbind
                       [(Datatypes.Status ( (Datatypes.Int_of_integer ( (~8 : IntInf.int) )) , (Datatypes.Int_of_integer ( (1 : IntInf.int) )) ))]
                       (fn a => fn b => (MykeAdapter.mykeAdapter ( a ) ( b ))))
                     (fn s =>
                       unit_SE
                         (equal_list equal_out_c s
                           [(Datatypes.Status_ok ( (nat_of_integer
             (10 : IntInf.int)) ))])))),
    ([], fn () => valid_SE
                    (fun_upd (equal_prod equal_int equal_int) (fn _ => NONE)
                      ((Datatypes.Int_of_integer ( (~3 : IntInf.int) )),
                        (Datatypes.Int_of_integer ( (1 : IntInf.int) )))
                      (SOME (Datatypes.Int_of_integer ( (10 : IntInf.int) ))))
                    (bind_SE
                      (mbind
                        [(Datatypes.Status ( (Datatypes.Int_of_integer ( (~3 : IntInf.int) )) , (Datatypes.Int_of_integer ( (1 : IntInf.int) )) ))]
                        (fn a => fn b => (MykeAdapter.mykeAdapter ( a ) ( b ))))
                      (fn s =>
                        unit_SE
                          (equal_list equal_out_c s
                            [(Datatypes.Status_ok ( (nat_of_integer
              (10 : IntInf.int)) ))])))),
    ([], fn () => valid_SE
                    (fun_upd (equal_prod equal_int equal_int)
                      (fun_upd (equal_prod equal_int equal_int) (fn _ => NONE)
                        ((Datatypes.Int_of_integer ( (~3 : IntInf.int) )),
                          (Datatypes.Int_of_integer ( (1 : IntInf.int) )))
                        (SOME (Datatypes.Int_of_integer ( (10 : IntInf.int) ))))
                      ((Datatypes.Int_of_integer ( (~3 : IntInf.int) )),
                        zero_int)
                      (SOME (Datatypes.Int_of_integer ( (5 : IntInf.int) ))))
                    (bind_SE
                      (mbind
                        [(Datatypes.Alloc ( (Datatypes.Int_of_integer ( (~3 : IntInf.int) )) , zero_int , (suc
                            (suc (suc (suc zero_nat)))))),
                          (Datatypes.Alloc ( (Datatypes.Int_of_integer ( (~3 : IntInf.int) )) , (Datatypes.Int_of_integer ( (1 : IntInf.int) )) , (suc
                            (suc zero_nat)))),
                          (Datatypes.Status ( (Datatypes.Int_of_integer ( (~3 : IntInf.int) )) , (Datatypes.Int_of_integer ( (1 : IntInf.int) )) ))]
                        (fn a => fn b => (MykeAdapter.mykeAdapter ( a ) ( b ))))
                      (fn s =>
                        unit_SE
                          (equal_list equal_out_c s
                            [Datatypes.Alloc_ok, Datatypes.Alloc_ok,
                              (Datatypes.Status_ok ( (nat_of_integer
               (12 : IntInf.int)) ))]))))];

end; (*struct TestScript*)
