 
  (********************************************************)
  (* This file is generated automatically. Do not edit    *)
  (********************************************************)


structure MykeAdapter : sig
  val mykeAdapter_con :
    Datatypes.in_c ->
      (Datatypes.int * Datatypes.int -> Datatypes.int option) ->
        (Datatypes.out_c *
          (Datatypes.int * Datatypes.int -> Datatypes.int option)) option
end = struct

datatype num = One | Bit0 of num | Bit1 of num;

fun integer_of_nat (Datatypes.Nat ( x )) = x;

fun plus_nat m n =
  (Datatypes.Nat ( (IntInf.+ (integer_of_nat m, integer_of_nat n)) ));

val one_nat : Datatypes.nat = (Datatypes.Nat ( (1 : IntInf.int) ));

fun suc n = plus_nat n one_nat;

fun bind_SE f g =
  (fn sigma => (case f sigma of NONE => NONE | SOME a => let
                   val (aa, b) = a;
                 in
                   g aa b
                 end));

fun unit_SE e = (fn sigma => SOME (e, sigma));

fun the (SOME x2) = x2;

fun fst (x1, x2) = x1;

fun int_of_nat n = (Datatypes.Int_of_integer ( (integer_of_nat n) ));

fun integer_of_int (Datatypes.Int_of_integer ( k )) = k;

fun plus_int k l =
  (Datatypes.Int_of_integer ( (IntInf.+ (integer_of_int
   k, integer_of_int l)) ));

val zero_int : Datatypes.int = (Datatypes.Int_of_integer ( (0 : IntInf.int) ));

val zero_nat : Datatypes.nat = (Datatypes.Nat ( (0 : IntInf.int) ));

fun equal_int k l = (((integer_of_int k) : IntInf.int) = (integer_of_int l));

fun minus_int k l =
  (Datatypes.Int_of_integer ( (IntInf.- (integer_of_int
   k, integer_of_int l)) ));

fun less_eq_int k l = IntInf.<= (integer_of_int k, integer_of_int l);

fun my_nat_conv x =
  (if less_eq_int x zero_int then zero_nat
    else suc (my_nat_conv
               (minus_int x (Datatypes.Int_of_integer ( (1 : IntInf.int) )))));

fun stubs_to_out_conc (Datatypes.Alloc ( task_id , th_id , res)) sigma
  sigma_impl =
  (if equal_int sigma_impl
        (plus_int ((the o sigma) (task_id, th_id)) (int_of_nat res))
    then Datatypes.Alloc_ok else Datatypes.Release_ok )
  | stubs_to_out_conc (Datatypes.Release ( task_id , th_id , res )) sigma
    sigma_impl =
    (if equal_int sigma_impl
          (minus_int ((the o sigma) (task_id, th_id)) (int_of_nat res))
      then Datatypes.Release_ok  else Datatypes.Alloc_ok)
  | stubs_to_out_conc (Datatypes.Status ( task_id , th_id )) sigma sigma_impl =
    (if equal_int sigma_impl ((the o sigma) (task_id, th_id))
      then (Datatypes.Status_ok ( (my_nat_conv sigma_impl) ))
      else Datatypes.Release_ok );

fun mykeAdapter_con (Datatypes.Alloc ( task_id , th_id , res)) sigma =
  bind_SE
    (fn a =>
      (MyKeOSAdapter.get_state ( task_id ) ( th_id ) ( (int_of_nat
                 res) ) ( a )))
    (fn _ =>
      unit_SE
        (stubs_to_out_conc (Datatypes.Alloc ( task_id , th_id , res)) sigma
          ((fst o the)
            (MyKeOSAdapter.get_state ( task_id ) ( th_id ) ( (int_of_nat
                       res) ) ( sigma )))))
    sigma
  | mykeAdapter_con (Datatypes.Release ( task_id , th_id , res )) sigma =
    bind_SE
      (fn a =>
        (MyKeOSAdapter.get_state ( task_id ) ( th_id ) ( (int_of_nat
                   res) ) ( a )))
      (fn _ =>
        unit_SE
          (stubs_to_out_conc (Datatypes.Alloc ( task_id , th_id , res)) sigma
            ((fst o the)
              (MyKeOSAdapter.get_state ( task_id ) ( th_id ) ( (int_of_nat
                         res) ) ( sigma )))))
      sigma
  | mykeAdapter_con (Datatypes.Status ( task_id , th_id )) sigma =
    bind_SE
      (fn a =>
        (MyKeOSAdapter.get_state ( task_id ) ( th_id ) ( (the
                   (sigma (task_id, th_id))) ) ( a )))
      (fn _ =>
        unit_SE
          (Datatypes.Status_ok ( ((my_nat_conv o the)
                                   (sigma (task_id, th_id))) )))
      sigma;

end; (*struct MykeAdapter*)
