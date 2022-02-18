 
  (********************************************************)
  (* This file is generated automatically. Do not edit    *)
  (********************************************************)


structure Example : sig
  datatype bit = Zero_bit | One_bit
  type 'a equal
  val equal : 'a equal -> 'a -> 'a -> bool
  val eq : 'a equal -> 'a -> 'a -> bool
  datatype num = One | Bit0 of num | Bit1 of num
  datatype 'a set = Set of 'a list | Coset of 'a list
  val hd : 'a list -> 'a
  val suc : IntInf.int -> IntInf.int
  datatype instr = Ilb of IntInf.int * IntInf.int * IntInf.int |
    Ilh of IntInf.int * IntInf.int * IntInf.int |
    Ilw of IntInf.int * IntInf.int * IntInf.int |
    Ilbu of IntInf.int * IntInf.int * IntInf.int |
    Ilhu of IntInf.int * IntInf.int * IntInf.int |
    Isb of IntInf.int * IntInf.int * IntInf.int |
    Ish of IntInf.int * IntInf.int * IntInf.int |
    Isw of IntInf.int * IntInf.int * IntInf.int |
    Ilhgi of IntInf.int * IntInf.int | Ilhg of IntInf.int * IntInf.int |
    Imovs2i of IntInf.int * IntInf.int | Imovi2s of IntInf.int * IntInf.int |
    Iaddio of IntInf.int * IntInf.int * IntInf.int |
    Iaddi of IntInf.int * IntInf.int * IntInf.int |
    Isubio of IntInf.int * IntInf.int * IntInf.int |
    Isubi of IntInf.int * IntInf.int * IntInf.int |
    Iandi of IntInf.int * IntInf.int * IntInf.int |
    Iori of IntInf.int * IntInf.int * IntInf.int |
    Ixori of IntInf.int * IntInf.int * IntInf.int |
    Iaddo of IntInf.int * IntInf.int * IntInf.int |
    Iadd of IntInf.int * IntInf.int * IntInf.int |
    Isubo of IntInf.int * IntInf.int * IntInf.int |
    Isub of IntInf.int * IntInf.int * IntInf.int |
    Iand of IntInf.int * IntInf.int * IntInf.int |
    Ior of IntInf.int * IntInf.int * IntInf.int |
    Ixor of IntInf.int * IntInf.int * IntInf.int | Iclri of IntInf.int |
    Isgri of IntInf.int * IntInf.int * IntInf.int |
    Iseqi of IntInf.int * IntInf.int * IntInf.int |
    Isgei of IntInf.int * IntInf.int * IntInf.int |
    Islsi of IntInf.int * IntInf.int * IntInf.int |
    Isnei of IntInf.int * IntInf.int * IntInf.int |
    Islei of IntInf.int * IntInf.int * IntInf.int | Iseti of IntInf.int |
    Iclr of IntInf.int | Isgr of IntInf.int * IntInf.int * IntInf.int |
    Iseq of IntInf.int * IntInf.int * IntInf.int |
    Isge of IntInf.int * IntInf.int * IntInf.int |
    Isls of IntInf.int * IntInf.int * IntInf.int |
    Isne of IntInf.int * IntInf.int * IntInf.int |
    Isle of IntInf.int * IntInf.int * IntInf.int | Iset of IntInf.int |
    Islli of IntInf.int * IntInf.int * IntInf.int |
    Isrli of IntInf.int * IntInf.int * IntInf.int |
    Israi of IntInf.int * IntInf.int * IntInf.int |
    Isll of IntInf.int * IntInf.int * IntInf.int |
    Isrl of IntInf.int * IntInf.int * IntInf.int |
    Isra of IntInf.int * IntInf.int * IntInf.int |
    Ibeqz of IntInf.int * IntInf.int | Ibnez of IntInf.int * IntInf.int |
    Ijal of IntInf.int | Ijalr of IntInf.int | Ij of IntInf.int |
    Ijr of IntInf.int | Itrap of IntInf.int | Irfe
  val map : ('a -> 'b) -> 'a list -> 'b list
  val nth : 'a list -> IntInf.int -> 'a
  val zip : 'a list -> 'b list -> ('a * 'b) list
  datatype 'a aSMcore_t_ext =
    ASMcore_t_ext of
      IntInf.int * IntInf.int * IntInf.int list * IntInf.int list *
        (IntInf.int -> IntInf.int) * 'a
  val mm : 'a aSMcore_t_ext -> IntInf.int -> IntInf.int
  val drop : IntInf.int -> 'a list -> 'a list
  val null : 'a list -> bool
  val take : IntInf.int -> 'a list -> 'a list
  val pcp : 'a aSMcore_t_ext -> IntInf.int
  val reg : IntInf.int list -> IntInf.int -> IntInf.int
  type 'a one
  val one : 'a one -> 'a
  val one_inta : IntInf.int
  val one_int : IntInf.int one
  val foldl : ('a -> 'b -> 'a) -> 'a -> 'b list -> 'a
  val one_nata : IntInf.int
  val one_nat : IntInf.int one
  val membera : 'a equal -> 'a list -> 'a -> bool
  val inserta : 'a equal -> 'a -> 'a list -> 'a list
  val removeAll : 'a equal -> 'a -> 'a list -> 'a list
  val insert : 'a equal -> 'a -> 'a set -> 'a set
  val member : 'a equal -> 'a -> 'a set -> bool
  val gprs : 'a aSMcore_t_ext -> IntInf.int list
  val sprs : 'a aSMcore_t_ext -> IntInf.int list
  val equal_nat : IntInf.int equal
  val bot_set : 'a set
  val sPR_RM : IntInf.int
  val sPR_SR : IntInf.int
  val sPR_ECA : IntInf.int
  val sPR_EPC : IntInf.int
  val sPR_ESR : IntInf.int
  val sPR_FCC : IntInf.int
  val sPR_PTL : IntInf.int
  val sPR_PTO : IntInf.int
  val sPR_EDPC : IntInf.int
  val sPR_MODE : IntInf.int
  val sPR_EData : IntInf.int
  val sPR_EMODE : IntInf.int
  val sPR_IEEEF : IntInf.int
  val used_sprs : IntInf.int set
  val sreg : IntInf.int list -> IntInf.int -> IntInf.int
  val fun_upd : 'a equal -> ('a -> 'b) -> 'a -> 'b -> 'a -> 'b
  type 'a zero
  val zero : 'a zero -> 'a
  val abs_int : IntInf.int -> IntInf.int
  val sgn_int : IntInf.int -> IntInf.int
  val zero_nat : IntInf.int zero
  type 'a times
  val times : 'a times -> 'a -> 'a -> 'a
  type 'a power
  val one_power : 'a power -> 'a one
  val times_power : 'a power -> 'a times
  val powera : 'a -> ('a -> 'a -> 'a) -> 'a -> IntInf.int -> 'a
  val power : 'a power -> 'a -> IntInf.int -> 'a
  val times_nat : IntInf.int times
  val power_nat : IntInf.int power
  val snd : 'a * 'b -> 'b
  val mod_nat : IntInf.int -> IntInf.int -> IntInf.int
  val wlen_bit : IntInf.int
  val fit_nat : IntInf.int -> IntInf.int
  val times_int : IntInf.int times
  val power_int : IntInf.int power
  val intwd_as_nat : IntInf.int -> IntInf.int
  val natwd_as_int : IntInf.int -> IntInf.int
  val int_add : IntInf.int -> IntInf.int -> IntInf.int
  val int_sub : IntInf.int -> IntInf.int -> IntInf.int
  val replicate : IntInf.int -> 'a -> 'a list
  val size_list : 'a list -> IntInf.int
  val bv_msb : bit list -> bit
  val bv_extend : IntInf.int -> bit -> bit list -> bit list
  val fst : 'a * 'b -> 'a
  val div_nat : IntInf.int -> IntInf.int -> IntInf.int
  val nat_to_bv_helper : IntInf.int -> bit list -> bit list
  val nat_to_bv : IntInf.int -> bit list
  val equal_bit : bit -> bit -> bool
  val rem_initial : bit -> bit list -> bit list
  val norm_signed : bit list -> bit list
  val bitNOT_bit : bit -> bit
  val int_to_bv : IntInf.int -> bit list
  val int2bvn : IntInf.int -> IntInf.int -> bit list
  val bv_to_int_aux : bit list -> IntInf.int -> IntInf.int
  val bv_to_int : bit list -> IntInf.int
  val s_lsh : IntInf.int -> IntInf.int -> IntInf.int -> IntInf.int
  val sllog : IntInf.int -> IntInf.int -> IntInf.int
  val apsnd : ('a -> 'b) -> 'c * 'a -> 'c * 'b
  val divmod_int : IntInf.int -> IntInf.int -> IntInf.int * IntInf.int
  val div_int : IntInf.int -> IntInf.int -> IntInf.int
  val srath : IntInf.int -> IntInf.int -> IntInf.int
  type 'a zero_neq_one
  val one_zero_neq_one : 'a zero_neq_one -> 'a one
  val zero_zero_neq_one : 'a zero_neq_one -> 'a zero
  val zero_neq_one_nat : IntInf.int zero_neq_one
  val bitval : 'a zero_neq_one -> bit -> 'a
  val bv_to_nat : bit list -> IntInf.int
  val s_rsh : IntInf.int -> IntInf.int -> IntInf.int -> IntInf.int
  val srlog : IntInf.int -> IntInf.int -> IntInf.int
  val sxt_wd : bit list -> bit list
  val gPR_ret : IntInf.int
  val inc_pcp_by : IntInf.int -> IntInf.int -> IntInf.int
  val dpc_update :
    (IntInf.int -> IntInf.int) -> 'a aSMcore_t_ext -> 'a aSMcore_t_ext
  val pcp_update :
    (IntInf.int -> IntInf.int) -> 'a aSMcore_t_ext -> 'a aSMcore_t_ext
  val wlen_byte : IntInf.int
  val inc_pcs_st : unit aSMcore_t_ext -> unit aSMcore_t_ext
  val list_update : 'a list -> IntInf.int -> 'a -> 'a list
  val gprs_update :
    (IntInf.int list -> IntInf.int list) -> 'a aSMcore_t_ext -> 'a aSMcore_t_ext
  val comp_exec :
    unit aSMcore_t_ext ->
      (IntInf.int -> IntInf.int -> bool) ->
        IntInf.int -> IntInf.int -> IntInf.int -> unit aSMcore_t_ext
  val cell2data : IntInf.int -> IntInf.int
  val data_mem_read : (IntInf.int -> IntInf.int) -> IntInf.int -> IntInf.int
  val load_from_mem :
    (IntInf.int -> IntInf.int) ->
      IntInf.int -> IntInf.int -> IntInf.int -> IntInf.int
  val load_exec :
    unit aSMcore_t_ext ->
      IntInf.int -> IntInf.int -> IntInf.int -> IntInf.int -> unit aSMcore_t_ext
  val arith_exec :
    unit aSMcore_t_ext ->
      (IntInf.int -> IntInf.int -> IntInf.int) ->
        IntInf.int -> IntInf.int -> IntInf.int -> unit aSMcore_t_ext
  val const_load : IntInf.int -> IntInf.int -> IntInf.int
  val load_from_mema :
    (IntInf.int -> IntInf.int) ->
      IntInf.int -> IntInf.int -> IntInf.int -> IntInf.int
  val load_execa :
    unit aSMcore_t_ext ->
      IntInf.int -> IntInf.int -> IntInf.int -> IntInf.int -> unit aSMcore_t_ext
  val mm_update :
    ((IntInf.int -> IntInf.int) -> IntInf.int -> IntInf.int) ->
      'a aSMcore_t_ext -> 'a aSMcore_t_ext
  val data2cell : IntInf.int -> IntInf.int
  val data_mem_write :
    (IntInf.int -> IntInf.int) ->
      IntInf.int -> IntInf.int -> IntInf.int -> IntInf.int
  val store_to_mem :
    (IntInf.int -> IntInf.int) ->
      IntInf.int ->
        IntInf.int -> IntInf.int -> IntInf.int -> IntInf.int -> IntInf.int
  val store_exec :
    unit aSMcore_t_ext ->
      IntInf.int -> IntInf.int -> IntInf.int -> IntInf.int -> unit aSMcore_t_ext
  val sprs_update :
    (IntInf.int list -> IntInf.int list) -> 'a aSMcore_t_ext -> 'a aSMcore_t_ext
  val const_load_imm : IntInf.int -> IntInf.int -> IntInf.int
  val is_system_mode : unit aSMcore_t_ext -> bool
  val s_bitop : (bit -> bit -> bit) -> IntInf.int -> IntInf.int -> IntInf.int
  val bitOR_bit : bit -> bit -> bit
  val bitAND_bit : bit -> bit -> bit
  val bitXOR_bit : bit -> bit -> bit
  val exec_instr : unit aSMcore_t_ext -> instr -> unit aSMcore_t_ext
  val sigma_0 : unit aSMcore_t_ext
end = struct

datatype bit = Zero_bit | One_bit;

type 'a equal = {equal : 'a -> 'a -> bool};
val equal = #equal : 'a equal -> 'a -> 'a -> bool;

fun eq A_ a b = equal A_ a b;

datatype num = One | Bit0 of num | Bit1 of num;

datatype 'a set = Set of 'a list | Coset of 'a list;

fun hd (x :: xs) = x;

fun suc n = IntInf.+ (n, (1 : IntInf.int));

datatype instr = Ilb of IntInf.int * IntInf.int * IntInf.int |
  Ilh of IntInf.int * IntInf.int * IntInf.int |
  Ilw of IntInf.int * IntInf.int * IntInf.int |
  Ilbu of IntInf.int * IntInf.int * IntInf.int |
  Ilhu of IntInf.int * IntInf.int * IntInf.int |
  Isb of IntInf.int * IntInf.int * IntInf.int |
  Ish of IntInf.int * IntInf.int * IntInf.int |
  Isw of IntInf.int * IntInf.int * IntInf.int | Ilhgi of IntInf.int * IntInf.int
  | Ilhg of IntInf.int * IntInf.int | Imovs2i of IntInf.int * IntInf.int |
  Imovi2s of IntInf.int * IntInf.int |
  Iaddio of IntInf.int * IntInf.int * IntInf.int |
  Iaddi of IntInf.int * IntInf.int * IntInf.int |
  Isubio of IntInf.int * IntInf.int * IntInf.int |
  Isubi of IntInf.int * IntInf.int * IntInf.int |
  Iandi of IntInf.int * IntInf.int * IntInf.int |
  Iori of IntInf.int * IntInf.int * IntInf.int |
  Ixori of IntInf.int * IntInf.int * IntInf.int |
  Iaddo of IntInf.int * IntInf.int * IntInf.int |
  Iadd of IntInf.int * IntInf.int * IntInf.int |
  Isubo of IntInf.int * IntInf.int * IntInf.int |
  Isub of IntInf.int * IntInf.int * IntInf.int |
  Iand of IntInf.int * IntInf.int * IntInf.int |
  Ior of IntInf.int * IntInf.int * IntInf.int |
  Ixor of IntInf.int * IntInf.int * IntInf.int | Iclri of IntInf.int |
  Isgri of IntInf.int * IntInf.int * IntInf.int |
  Iseqi of IntInf.int * IntInf.int * IntInf.int |
  Isgei of IntInf.int * IntInf.int * IntInf.int |
  Islsi of IntInf.int * IntInf.int * IntInf.int |
  Isnei of IntInf.int * IntInf.int * IntInf.int |
  Islei of IntInf.int * IntInf.int * IntInf.int | Iseti of IntInf.int |
  Iclr of IntInf.int | Isgr of IntInf.int * IntInf.int * IntInf.int |
  Iseq of IntInf.int * IntInf.int * IntInf.int |
  Isge of IntInf.int * IntInf.int * IntInf.int |
  Isls of IntInf.int * IntInf.int * IntInf.int |
  Isne of IntInf.int * IntInf.int * IntInf.int |
  Isle of IntInf.int * IntInf.int * IntInf.int | Iset of IntInf.int |
  Islli of IntInf.int * IntInf.int * IntInf.int |
  Isrli of IntInf.int * IntInf.int * IntInf.int |
  Israi of IntInf.int * IntInf.int * IntInf.int |
  Isll of IntInf.int * IntInf.int * IntInf.int |
  Isrl of IntInf.int * IntInf.int * IntInf.int |
  Isra of IntInf.int * IntInf.int * IntInf.int |
  Ibeqz of IntInf.int * IntInf.int | Ibnez of IntInf.int * IntInf.int |
  Ijal of IntInf.int | Ijalr of IntInf.int | Ij of IntInf.int |
  Ijr of IntInf.int | Itrap of IntInf.int | Irfe;

fun map f [] = []
  | map f (x :: xs) = f x :: map f xs;

fun nth (x :: xs) n =
  (if ((n : IntInf.int) = 0) then x
    else nth xs (IntInf.max (0, IntInf.- (n, (1 : IntInf.int)))));

fun zip (x :: xs) (y :: ys) = (x, y) :: zip xs ys
  | zip xs [] = []
  | zip [] ys = [];

datatype 'a aSMcore_t_ext =
  ASMcore_t_ext of
    IntInf.int * IntInf.int * IntInf.int list * IntInf.int list *
      (IntInf.int -> IntInf.int) * 'a;

fun mm (ASMcore_t_ext (dpc, pcp, gprs, sprs, mm, more)) = mm;

fun drop n [] = []
  | drop n (x :: xs) =
    (if ((n : IntInf.int) = 0) then x :: xs
      else drop (IntInf.max (0, IntInf.- (n, (1 : IntInf.int)))) xs);

fun null [] = true
  | null (x :: xs) = false;

fun take n [] = []
  | take n (x :: xs) =
    (if ((n : IntInf.int) = 0) then []
      else x :: take (IntInf.max (0, IntInf.- (n, (1 : IntInf.int)))) xs);

fun pcp (ASMcore_t_ext (dpc, pcp, gprs, sprs, mm, more)) = pcp;

fun reg xs n = (if ((n : IntInf.int) = 0) then 0 else nth xs n);

type 'a one = {one : 'a};
val one = #one : 'a one -> 'a;

val one_inta : IntInf.int = (1 : IntInf.int);

val one_int = {one = one_inta} : IntInf.int one;

fun foldl f a [] = a
  | foldl f a (x :: xs) = foldl f (f a x) xs;

val one_nata : IntInf.int = (1 : IntInf.int);

val one_nat = {one = one_nata} : IntInf.int one;

fun membera A_ [] y = false
  | membera A_ (x :: xs) y = eq A_ x y orelse membera A_ xs y;

fun inserta A_ x xs = (if membera A_ xs x then xs else x :: xs);

fun removeAll A_ x [] = []
  | removeAll A_ x (y :: xs) =
    (if eq A_ x y then removeAll A_ x xs else y :: removeAll A_ x xs);

fun insert A_ x (Coset xs) = Coset (removeAll A_ x xs)
  | insert A_ x (Set xs) = Set (inserta A_ x xs);

fun member A_ x (Coset xs) = not (membera A_ xs x)
  | member A_ x (Set xs) = membera A_ xs x;

fun gprs (ASMcore_t_ext (dpc, pcp, gprs, sprs, mm, more)) = gprs;

fun sprs (ASMcore_t_ext (dpc, pcp, gprs, sprs, mm, more)) = sprs;

val equal_nat = {equal = (fn a => fn b => ((a : IntInf.int) = b))} :
  IntInf.int equal;

val bot_set : 'a set = Set [];

val sPR_RM : IntInf.int = (6 : IntInf.int);

val sPR_SR : IntInf.int = 0;

val sPR_ECA : IntInf.int = (2 : IntInf.int);

val sPR_EPC : IntInf.int = (3 : IntInf.int);

val sPR_ESR : IntInf.int = (1 : IntInf.int);

val sPR_FCC : IntInf.int = (8 : IntInf.int);

val sPR_PTL : IntInf.int = (10 : IntInf.int);

val sPR_PTO : IntInf.int = (9 : IntInf.int);

val sPR_EDPC : IntInf.int = (4 : IntInf.int);

val sPR_MODE : IntInf.int = (16 : IntInf.int);

val sPR_EData : IntInf.int = (5 : IntInf.int);

val sPR_EMODE : IntInf.int = (11 : IntInf.int);

val sPR_IEEEF : IntInf.int = (7 : IntInf.int);

val used_sprs : IntInf.int set =
  insert equal_nat sPR_SR
    (insert equal_nat sPR_ESR
      (insert equal_nat sPR_ECA
        (insert equal_nat sPR_EPC
          (insert equal_nat sPR_EDPC
            (insert equal_nat sPR_EData
              (insert equal_nat sPR_RM
                (insert equal_nat sPR_IEEEF
                  (insert equal_nat sPR_FCC
                    (insert equal_nat sPR_PTO
                      (insert equal_nat sPR_PTL
                        (insert equal_nat sPR_EMODE
                          (insert equal_nat sPR_MODE bot_set))))))))))));

fun sreg xs n = (if member equal_nat n used_sprs then nth xs n else 0);

fun fun_upd A_ f a b = (fn x => (if eq A_ x a then b else f x));

type 'a zero = {zero : 'a};
val zero = #zero : 'a zero -> 'a;

fun abs_int i = (if IntInf.< (i, 0) then IntInf.~ i else i);

fun sgn_int i =
  (if ((i : IntInf.int) = 0) then 0
    else (if IntInf.< (0, i) then (1 : IntInf.int)
           else IntInf.~ (1 : IntInf.int)));

val zero_nat = {zero = 0} : IntInf.int zero;

type 'a times = {times : 'a -> 'a -> 'a};
val times = #times : 'a times -> 'a -> 'a -> 'a;

type 'a power = {one_power : 'a one, times_power : 'a times};
val one_power = #one_power : 'a power -> 'a one;
val times_power = #times_power : 'a power -> 'a times;

fun powera one times a n =
  (if ((n : IntInf.int) = 0) then one
    else times a
           (powera one times a
             (IntInf.max (0, IntInf.- (n, (1 : IntInf.int))))));

fun power A_ = powera (one (one_power A_)) (times (times_power A_));

val times_nat = {times = (fn a => fn b => IntInf.* (a, b))} : IntInf.int times;

val power_nat = {one_power = one_nat, times_power = times_nat} :
  IntInf.int power;

fun snd (a, b) = b;

fun mod_nat m n = snd (IntInf.divMod (m, n));

val wlen_bit : IntInf.int = (32 : IntInf.int);

fun fit_nat i = mod_nat i (power power_nat (2 : IntInf.int) wlen_bit);

val times_int = {times = (fn a => fn b => IntInf.* (a, b))} : IntInf.int times;

val power_int = {one_power = one_int, times_power = times_int} :
  IntInf.int power;

fun intwd_as_nat n =
  (if IntInf.<= (power power_int (2 : IntInf.int)
                   (IntInf.max (0, IntInf.- (wlen_bit,
                     (1 : IntInf.int)))), n) andalso
        IntInf.< (n, power power_int (2 : IntInf.int) wlen_bit)
    then IntInf.max (0,
           (IntInf.+ (n, power power_int (2 : IntInf.int)
                           (IntInf.max (0, IntInf.- (wlen_bit,
                             (1 : IntInf.int)))))))
    else (if IntInf.< (n, IntInf.~
                            (power power_int (2 : IntInf.int)
                              (IntInf.max (0, IntInf.- (wlen_bit,
                                (1 : IntInf.int))))))
           then IntInf.max (0,
                  (IntInf.+ (IntInf.~
                               n, power power_int (2 : IntInf.int)
                                    (IntInf.max (0, IntInf.- (wlen_bit,
                                      (1 : IntInf.int)))))))
           else (if IntInf.<= (IntInf.~
                                 (power power_int (2 : IntInf.int)
                                   (IntInf.max (0, IntInf.- (wlen_bit,
                                     (1 : IntInf.int))))), n) andalso
                      IntInf.< (n, 0)
                  then IntInf.max (0,
                         (IntInf.+ (n, power power_int (2 : IntInf.int)
 wlen_bit)))
                  else IntInf.max (0, n))));

fun natwd_as_int n =
  (if IntInf.<=
        (power power_nat (2 : IntInf.int)
           (IntInf.max (0, IntInf.- (wlen_bit, (1 : IntInf.int)))),
        n) andalso
        IntInf.< (n, power power_nat (2 : IntInf.int) wlen_bit)
    then IntInf.- (n, power power_int (2 : IntInf.int) wlen_bit) else n);

fun int_add i1 i2 =
  natwd_as_int (fit_nat (IntInf.+ (intwd_as_nat i1, intwd_as_nat i2)));

fun int_sub i1 i2 =
  natwd_as_int
    (fit_nat
      (IntInf.max (0, IntInf.-
        (IntInf.+ (power power_nat (2 : IntInf.int) wlen_bit, intwd_as_nat i1),
        intwd_as_nat i2))));

fun replicate n x =
  (if ((n : IntInf.int) = 0) then []
    else x :: replicate (IntInf.max (0, IntInf.- (n, (1 : IntInf.int)))) x);

fun size_list [] = 0
  | size_list (a :: lista) = IntInf.+ (size_list lista, suc 0);

fun bv_msb w = (if null w then Zero_bit else hd w);

fun bv_extend i b w =
  replicate (IntInf.max (0, IntInf.- (i, size_list w))) b @ w;

fun fst (a, b) = a;

fun div_nat m n = fst (IntInf.divMod (m, n));

fun nat_to_bv_helper n =
  (fn bs =>
    (if ((n : IntInf.int) = 0) then bs
      else nat_to_bv_helper (div_nat n (2 : IntInf.int))
             ((if (((mod_nat n (2 : IntInf.int)) : IntInf.int) = 0)
                then Zero_bit else One_bit) ::
               bs)));

fun nat_to_bv n = nat_to_bv_helper n [];

fun equal_bit One_bit Zero_bit = false
  | equal_bit Zero_bit One_bit = false
  | equal_bit One_bit One_bit = true
  | equal_bit Zero_bit Zero_bit = true;

fun rem_initial b [] = []
  | rem_initial b (x :: xs) =
    (if equal_bit b x then rem_initial b xs else x :: xs);

fun norm_signed [] = []
  | norm_signed (b :: bs) =
    (case b
      of Zero_bit =>
        (if null (rem_initial Zero_bit bs) then []
          else b :: rem_initial Zero_bit bs)
      | One_bit => b :: rem_initial b bs);

fun bitNOT_bit Zero_bit = One_bit
  | bitNOT_bit One_bit = Zero_bit;

fun int_to_bv n =
  (if IntInf.<= (0, n)
    then norm_signed (Zero_bit :: nat_to_bv (IntInf.max (0, n)))
    else norm_signed
           (map bitNOT_bit
             (Zero_bit ::
               nat_to_bv
                 (IntInf.max (0, (IntInf.- (IntInf.~ n, (1 : IntInf.int))))))));

fun int2bvn n a =
  let
    val v = int_to_bv a;
  in
    drop (IntInf.max (0, IntInf.- (size_list v, n))) (bv_extend n (bv_msb v) v)
  end;

fun bv_to_int_aux [] w = w
  | bv_to_int_aux (b :: bs) w = bv_to_int_aux bs w;

fun bv_to_int bs = bv_to_int_aux bs 0;

fun s_lsh x =
  (fn xa => fn w => fn a =>
    bv_to_int (drop a (int2bvn w xa) @ replicate a Zero_bit))
    x;

fun sllog i sh =
  let
    val a =
      mod_nat (intwd_as_nat sh)
        (power power_nat (2 : IntInf.int) (5 : IntInf.int));
  in
    s_lsh i wlen_bit a
  end;

fun apsnd f (x, y) = (x, f y);

fun divmod_int k l =
  (if ((k : IntInf.int) = 0) then (0, 0)
    else (if ((l : IntInf.int) = 0) then (0, k)
           else apsnd (fn a => IntInf.* (sgn_int l, a))
                  (if (((sgn_int k) : IntInf.int) = (sgn_int l))
                    then IntInf.divMod (IntInf.abs k, IntInf.abs l)
                    else let
                           val (r, s) =
                             IntInf.divMod (IntInf.abs k, IntInf.abs l);
                         in
                           (if ((s : IntInf.int) = 0) then (IntInf.~ r, 0)
                             else (IntInf.- (IntInf.~ r, (1 : IntInf.int)),
                                    IntInf.- (abs_int l, s)))
                         end)));

fun div_int a b = fst (divmod_int a b);

fun srath i sh =
  let
    val sa =
      mod_nat (intwd_as_nat sh)
        (power power_nat (2 : IntInf.int) (5 : IntInf.int));
  in
    div_int i (power power_int (2 : IntInf.int) sa)
  end;

type 'a zero_neq_one = {one_zero_neq_one : 'a one, zero_zero_neq_one : 'a zero};
val one_zero_neq_one = #one_zero_neq_one : 'a zero_neq_one -> 'a one;
val zero_zero_neq_one = #zero_zero_neq_one : 'a zero_neq_one -> 'a zero;

val zero_neq_one_nat =
  {one_zero_neq_one = one_nat, zero_zero_neq_one = zero_nat} :
  IntInf.int zero_neq_one;

fun bitval A_ =
  (fn a =>
    (case a of Zero_bit => zero (zero_zero_neq_one A_)
      | One_bit => one (one_zero_neq_one A_)));

fun bv_to_nat x =
  foldl (fn bn => fn b =>
          IntInf.+ (IntInf.* ((2 : IntInf.int), bn), bitval zero_neq_one_nat b))
    0 x;

fun s_rsh x w a =
  (if IntInf.< (0, a)
    then (bv_to_nat (take (IntInf.max (0, IntInf.- (w, a))) (int2bvn w x)))
    else x);

fun srlog i sh =
  let
    val a =
      mod_nat (intwd_as_nat sh)
        (power power_nat (2 : IntInf.int) (5 : IntInf.int));
  in
    s_rsh i wlen_bit a
  end;

fun sxt_wd bv = bv_extend wlen_bit (bv_msb bv) bv;

val gPR_ret : IntInf.int = (31 : IntInf.int);

fun inc_pcp_by pc inc = fit_nat (IntInf.+ (pc, intwd_as_nat inc));

fun dpc_update dpca (ASMcore_t_ext (dpc, pcp, gprs, sprs, mm, more)) =
  ASMcore_t_ext (dpca dpc, pcp, gprs, sprs, mm, more);

fun pcp_update pcpa (ASMcore_t_ext (dpc, pcp, gprs, sprs, mm, more)) =
  ASMcore_t_ext (dpc, pcpa pcp, gprs, sprs, mm, more);

val wlen_byte : IntInf.int = (4 : IntInf.int);

fun inc_pcs_st st =
  pcp_update (fn _ => inc_pcp_by (pcp st) wlen_byte)
    (dpc_update (fn _ => pcp st) st);

fun list_update [] i y = []
  | list_update (x :: xs) i y =
    (if ((i : IntInf.int) = 0) then y :: xs
      else x :: list_update xs (IntInf.max (0, IntInf.- (i, (1 : IntInf.int))))
                  y);

fun gprs_update gprsa (ASMcore_t_ext (dpc, pcp, gprs, sprs, mm, more)) =
  ASMcore_t_ext (dpc, pcp, gprsa gprs, sprs, mm, more);

fun comp_exec st compf opd1 opd2 dest =
  gprs_update
    (fn _ =>
      list_update (gprs st) dest
        (if compf opd1 opd2 then (1 : IntInf.int) else 0))
    (inc_pcs_st st);

fun cell2data x = x;

fun data_mem_read mm ad = cell2data (mm (div_nat ad (4 : IntInf.int)));

fun load_from_mem memory ad off d =
  let
    val new_nat =
      mod_nat
        (div_nat (intwd_as_nat (data_mem_read memory ad))
          (power power_nat (2 : IntInf.int) (IntInf.* ((8 : IntInf.int), off))))
        (power power_nat (2 : IntInf.int) (IntInf.* ((8 : IntInf.int), d)));
  in
    bv_to_int
      (sxt_wd
        (bv_extend (IntInf.* ((8 : IntInf.int), d)) Zero_bit
          (nat_to_bv new_nat)))
  end;

fun load_exec st adr adi d dest =
  let
    val ad = fit_nat (IntInf.+ (intwd_as_nat adr, intwd_as_nat adi));
  in
    gprs_update
      (fn _ =>
        list_update (gprs st) dest
          (load_from_mem (mm st) ad (mod_nat ad (4 : IntInf.int)) d))
      (inc_pcs_st st)
  end;

fun arith_exec st arithf opd1 opd2 dest =
  gprs_update (fn _ => list_update (gprs st) dest (arithf opd1 opd2))
    (inc_pcs_st st);

fun const_load a b =
  natwd_as_int
    (IntInf.*
      (mod_nat (intwd_as_nat b)
         (power power_nat (2 : IntInf.int) (16 : IntInf.int)),
      power power_nat (2 : IntInf.int) (16 : IntInf.int)));

fun load_from_mema memory ad off d =
  let
    val a =
      mod_nat
        (div_nat (intwd_as_nat (data_mem_read memory ad))
          (power power_nat (2 : IntInf.int) (IntInf.* ((8 : IntInf.int), off))))
        (power power_nat (2 : IntInf.int) (IntInf.* ((8 : IntInf.int), d)));
  in
    a
  end;

fun load_execa st adr adi d dest =
  let
    val ad = fit_nat (IntInf.+ (intwd_as_nat adr, intwd_as_nat adi));
  in
    gprs_update
      (fn _ =>
        list_update (gprs st) dest
          (load_from_mema (mm st) ad (mod_nat ad (4 : IntInf.int)) d))
      (inc_pcs_st st)
  end;

fun mm_update mma (ASMcore_t_ext (dpc, pcp, gprs, sprs, mm, more)) =
  ASMcore_t_ext (dpc, pcp, gprs, sprs, mma mm, more);

fun data2cell x = x;

fun data_mem_write mm ad data =
  fun_upd equal_nat mm (div_nat ad (4 : IntInf.int)) (data2cell data);

fun store_to_mem memory ad off d i =
  let
    val owi = intwd_as_nat (data_mem_read memory ad);
    val wi = intwd_as_nat i;
    val hwi =
      IntInf.*
        (div_nat owi
           (power power_nat (2 : IntInf.int)
             (IntInf.* ((8 : IntInf.int), IntInf.+ (off, d)))),
        power power_nat (2 : IntInf.int)
          (IntInf.* ((8 : IntInf.int), IntInf.+ (off, d))));
    val lwi =
      mod_nat owi
        (power power_nat (2 : IntInf.int) (IntInf.* ((8 : IntInf.int), off)));
    val mwi =
      IntInf.*
        (mod_nat wi
           (power power_nat (2 : IntInf.int) (IntInf.* ((8 : IntInf.int), d))),
        power power_nat (2 : IntInf.int) (IntInf.* ((8 : IntInf.int), off)));
    val a =
      natwd_as_int
        (mod_nat (IntInf.+ (IntInf.+ (hwi, mwi), lwi))
          (power power_nat (2 : IntInf.int) wlen_bit));
  in
    data_mem_write memory ad a
  end;

fun store_exec st adr adi d sour =
  let
    val ad = fit_nat (IntInf.+ (intwd_as_nat adr, intwd_as_nat adi));
  in
    mm_update
      (fn _ =>
        store_to_mem (mm st) ad (mod_nat ad (4 : IntInf.int)) d
          (reg (gprs st) sour))
      (inc_pcs_st st)
  end;

fun sprs_update sprsa (ASMcore_t_ext (dpc, pcp, gprs, sprs, mm, more)) =
  ASMcore_t_ext (dpc, pcp, gprs, sprsa sprs, mm, more);

fun const_load_imm a b =
  IntInf.* (b, power power_int (2 : IntInf.int) (16 : IntInf.int));

fun is_system_mode a = (((nth (sprs a) sPR_MODE) : IntInf.int) = 0);

fun s_bitop f =
  (fn x => fn y =>
    let
      val v = int_to_bv x;
      val w = int_to_bv y;
    in
      bv_to_int
        (map (fn (a, b) => f a b)
          (zip (bv_extend (size_list w) (bv_msb v) v)
            (bv_extend (size_list v) (bv_msb w) w)))
    end);

fun bitOR_bit Zero_bit y = y
  | bitOR_bit One_bit y = One_bit;

fun bitAND_bit Zero_bit y = Zero_bit
  | bitAND_bit One_bit y = y;

fun bitXOR_bit Zero_bit y = y
  | bitXOR_bit One_bit y = bitNOT_bit y;

fun exec_instr st (Iaddo (rd, rS1, rS2)) =
  arith_exec st int_add (reg (gprs st) rS1) (reg (gprs st) rS2) rd
  | exec_instr st (Isubo (rd, rS1, rS2)) =
    arith_exec st int_sub (reg (gprs st) rS1) (reg (gprs st) rS2) rd
  | exec_instr st (Iadd (rd, rS1, rS2)) =
    arith_exec st int_add (reg (gprs st) rS1) (reg (gprs st) rS2) rd
  | exec_instr st (Isub (rd, rS1, rS2)) =
    arith_exec st int_sub (reg (gprs st) rS1) (reg (gprs st) rS2) rd
  | exec_instr st (Iaddio (rd, rs, imm)) =
    arith_exec st int_add (reg (gprs st) rs) imm rd
  | exec_instr st (Isubio (rd, rs, imm)) =
    arith_exec st int_sub (reg (gprs st) rs) imm rd
  | exec_instr st (Iaddi (rd, rs, imm)) =
    arith_exec st int_add (reg (gprs st) rs) imm rd
  | exec_instr st (Isubi (rd, rs, imm)) =
    arith_exec st int_sub (reg (gprs st) rs) imm rd
  | exec_instr st (Iand (rd, rS1, rS2)) =
    arith_exec st (s_bitop bitAND_bit) (reg (gprs st) rS1) (reg (gprs st) rS2)
      rd
  | exec_instr st (Ior (rd, rS1, rS2)) =
    arith_exec st (s_bitop bitOR_bit) (reg (gprs st) rS1) (reg (gprs st) rS2) rd
  | exec_instr st (Ixor (rd, rS1, rS2)) =
    arith_exec st (s_bitop bitXOR_bit) (reg (gprs st) rS1) (reg (gprs st) rS2)
      rd
  | exec_instr st (Iandi (rd, rs, imm)) =
    arith_exec st (s_bitop bitAND_bit) (reg (gprs st) rs) imm rd
  | exec_instr st (Iori (rd, rs, imm)) =
    arith_exec st (s_bitop bitOR_bit) (reg (gprs st) rs) imm rd
  | exec_instr st (Ixori (rd, rs, imm)) =
    arith_exec st (s_bitop bitXOR_bit) (reg (gprs st) rs) imm rd
  | exec_instr st (Isll (rd, rS1, rS2)) =
    arith_exec st sllog (reg (gprs st) rS1) (reg (gprs st) rS2) rd
  | exec_instr st (Isrl (rd, rS1, rS2)) =
    arith_exec st srlog (reg (gprs st) rS1) (reg (gprs st) rS2) rd
  | exec_instr st (Isra (rd, rS1, rS2)) =
    arith_exec st srath (reg (gprs st) rS1) (reg (gprs st) rS2) rd
  | exec_instr st (Islli (rd, rs, sh_am)) =
    arith_exec st sllog (reg (gprs st) rs) sh_am rd
  | exec_instr st (Isrli (rd, rs, sh_am)) =
    arith_exec st srlog (reg (gprs st) rs) sh_am rd
  | exec_instr st (Israi (rd, rs, sh_am)) =
    arith_exec st srath (reg (gprs st) rs) sh_am rd
  | exec_instr st (Ilhg (rd, rs)) =
    arith_exec st const_load 0 (reg (gprs st) rs) rd
  | exec_instr st (Ilhgi (rd, imm)) = arith_exec st const_load_imm 0 imm rd
  | exec_instr st (Iclr rd) = comp_exec st (fn _ => fn _ => false) 0 0 rd
  | exec_instr st (Isgr (rd, rS1, rS2)) =
    comp_exec st (fn a => fn b => IntInf.< (a, b)) (reg (gprs st) rS2)
      (reg (gprs st) rS1) rd
  | exec_instr st (Iseq (rd, rS1, rS2)) =
    comp_exec st (fn a => fn b => ((a : IntInf.int) = b)) (reg (gprs st) rS1)
      (reg (gprs st) rS2) rd
  | exec_instr st (Isge (rd, rS1, rS2)) =
    comp_exec st (fn a => fn b => IntInf.<= (a, b)) (reg (gprs st) rS2)
      (reg (gprs st) rS1) rd
  | exec_instr st (Isls (rd, rS1, rS2)) =
    comp_exec st (fn a => fn b => IntInf.< (a, b)) (reg (gprs st) rS1)
      (reg (gprs st) rS2) rd
  | exec_instr st (Isne (rd, rS1, rS2)) =
    comp_exec st (fn a => fn b => not ((a : IntInf.int) = b))
      (reg (gprs st) rS1) (reg (gprs st) rS2) rd
  | exec_instr st (Isle (rd, rS1, rS2)) =
    comp_exec st (fn a => fn b => IntInf.<= (a, b)) (reg (gprs st) rS1)
      (reg (gprs st) rS2) rd
  | exec_instr st (Iset rd) = comp_exec st (fn _ => fn _ => true) 0 0 rd
  | exec_instr st (Iclri rd) = comp_exec st (fn _ => fn _ => false) 0 0 rd
  | exec_instr st (Isgri (rd, rs, imm)) =
    comp_exec st (fn a => fn b => IntInf.< (a, b)) imm (reg (gprs st) rs) rd
  | exec_instr st (Iseqi (rd, rs, imm)) =
    comp_exec st (fn a => fn b => ((a : IntInf.int) = b)) (reg (gprs st) rs) imm
      rd
  | exec_instr st (Isgei (rd, rs, imm)) =
    comp_exec st (fn a => fn b => IntInf.<= (a, b)) imm (reg (gprs st) rs) rd
  | exec_instr st (Islsi (rd, rs, imm)) =
    comp_exec st (fn a => fn b => IntInf.< (a, b)) (reg (gprs st) rs) imm rd
  | exec_instr st (Isnei (rd, rs, imm)) =
    comp_exec st (fn a => fn b => not ((a : IntInf.int) = b)) (reg (gprs st) rs)
      imm rd
  | exec_instr st (Islei (rd, rs, imm)) =
    comp_exec st (fn a => fn b => IntInf.<= (a, b)) (reg (gprs st) rs) imm rd
  | exec_instr st (Iseti rd) = comp_exec st (fn _ => fn _ => true) 0 0 rd
  | exec_instr st (Ilb (rd, rs, imm)) =
    load_exec st (reg (gprs st) rs) imm (1 : IntInf.int) rd
  | exec_instr st (Ilh (rd, rs, imm)) =
    load_exec st (reg (gprs st) rs) imm (2 : IntInf.int) rd
  | exec_instr st (Ilw (rd, rs, imm)) =
    load_exec st (reg (gprs st) rs) imm (4 : IntInf.int) rd
  | exec_instr st (Ilbu (rd, rs, imm)) =
    load_execa st (reg (gprs st) rs) imm (1 : IntInf.int) rd
  | exec_instr st (Ilhu (rd, rs, imm)) =
    load_execa st (reg (gprs st) rs) imm (2 : IntInf.int) rd
  | exec_instr st (Isb (rd, rs, imm)) =
    store_exec st (reg (gprs st) rs) imm (1 : IntInf.int) rd
  | exec_instr st (Ish (rd, rs, imm)) =
    store_exec st (reg (gprs st) rs) imm (2 : IntInf.int) rd
  | exec_instr st (Isw (rd, rs, imm)) =
    store_exec st (reg (gprs st) rs) imm (4 : IntInf.int) rd
  | exec_instr st (Imovs2i (rd, sa)) =
    (if not (is_system_mode st) andalso
          not (member equal_nat sa
                (insert equal_nat sPR_RM
                  (insert equal_nat sPR_IEEEF
                    (insert equal_nat sPR_FCC bot_set))))
      then st
      else gprs_update (fn _ => list_update (gprs st) rd (sreg (sprs st) sa))
             (inc_pcs_st st))
  | exec_instr st (Imovi2s (sa, rs)) =
    (if not (is_system_mode st) andalso
          not (member equal_nat sa
                (insert equal_nat sPR_RM
                  (insert equal_nat sPR_IEEEF
                    (insert equal_nat sPR_FCC bot_set))))
      then st
      else sprs_update (fn _ => list_update (sprs st) sa (reg (gprs st) rs))
             (inc_pcs_st st))
  | exec_instr st Irfe = st
  | exec_instr st (Itrap imm) = inc_pcs_st st
  | exec_instr st (Ij imm) =
    pcp_update (fn _ => inc_pcp_by (pcp st) imm)
      (dpc_update (fn _ => pcp st) st)
  | exec_instr st (Ijr rs) =
    pcp_update (fn _ => intwd_as_nat (reg (gprs st) rs))
      (dpc_update (fn _ => pcp st) st)
  | exec_instr st (Ijal imm) =
    gprs_update
      (fn _ =>
        list_update (gprs st) gPR_ret
          (natwd_as_int (inc_pcp_by (pcp st) (4 : IntInf.int))))
      (pcp_update (fn _ => inc_pcp_by (pcp st) imm)
        (dpc_update (fn _ => pcp st) st))
  | exec_instr st (Ijalr rs) =
    gprs_update
      (fn _ =>
        list_update (gprs st) gPR_ret
          (natwd_as_int (inc_pcp_by (pcp st) (4 : IntInf.int))))
      (pcp_update (fn _ => intwd_as_nat (reg (gprs st) rs))
        (dpc_update (fn _ => pcp st) st))
  | exec_instr st (Ibeqz (rs, imm)) =
    (if (((reg (gprs st) rs) : IntInf.int) = 0)
      then pcp_update (fn _ => inc_pcp_by (pcp st) imm)
             (dpc_update (fn _ => pcp st) st)
      else inc_pcs_st st)
  | exec_instr st (Ibnez (rs, imm)) =
    (if (((reg (gprs st) rs) : IntInf.int) = 0) then inc_pcs_st st
      else pcp_update (fn _ => inc_pcp_by (pcp st) imm)
             (dpc_update (fn _ => pcp st) st));

val sigma_0 : unit aSMcore_t_ext =
  ASMcore_t_ext
    (0, (1 : IntInf.int), replicate (32 : IntInf.int) (1 : IntInf.int),
      replicate (32 : IntInf.int) 0, (fn _ => 0), ());

end; (*struct Example*)
