
structure MyKeOSAdapter1 = 
struct

val c_alloc   = _import "alloc" public: Int32.int * Int32.int * Int32.int -> int;
val c_release = _import "release" public: Int32.int * Int32.int * Int32.int -> int;
val c_status  = _import "status" public: Int32.int * Int32.int * Int32.int -> int;


fun intOfInt (Datatypes.Int_of_integer y) = y;
												  
fun alloc (taskid:Datatypes.int) (thid:Datatypes.int) (res:Datatypes.int) (state) = 
   (SOME (Datatypes.Int_of_integer(IntInf.fromInt(c_alloc(IntInf.toInt (intOfInt taskid), IntInf.toInt (intOfInt thid), IntInf.toInt (intOfInt res)))), 
    state))
								  
fun release (taskid:Datatypes.int) (thid:Datatypes.int) (res:Datatypes.int) (state) =
    (SOME (Datatypes.Int_of_integer(IntInf.fromInt(c_release(IntInf.toInt (intOfInt taskid), IntInf.toInt (intOfInt thid), IntInf.toInt (intOfInt res)))), 
	 state))

fun status (taskid:Datatypes.int) (thid:Datatypes.int) (res:Datatypes.int) (state)=
    (SOME (Datatypes.Int_of_integer(IntInf.fromInt(c_status(IntInf.toInt (intOfInt taskid), IntInf.toInt (intOfInt thid), IntInf.toInt (intOfInt res)))), 
	  state))	
	
						
end