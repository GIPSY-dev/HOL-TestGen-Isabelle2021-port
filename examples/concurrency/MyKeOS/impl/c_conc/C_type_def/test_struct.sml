
(*signature TEST =
sig
  type t
  val Id: t -> t
end

functor CId (structure F: MLTON_FINALIZABLE
             structure Prim:
                  sig
                     val Id: Word32.word -> Word32.word
                  end): TEST =
   struct
      type t = Word32.word F.t

      fun Id (l: t) =
         F.withValue
         (l, fn w' =>
          let
             val c = F.new (Prim.Id  w')
             val _ = F.finalizeBefore (c, l)
          in
             c
          end)
   end
   
functor Test (structure CId: TEST
              structure MLton: sig
                                  structure GC:
                                     sig
                                        val collect: unit -> unit
                                     end
                               end) =
   struct
      fun f n =
         if n = 1
            then ()
         else
            let
               val a = Array.tabulate (n, fn i => i)
               val _ = Array.sub (a, 0) + Array.sub (a, 1)
            in
               f (n - 1)
            end
			
   
      val _ = MLton.GC.collect ()
      val _ = f 100
      val _ = print (concat ["listSum(l) = ",
                             Word32.toString (0wx37),
                             "\n"])
      val _ = MLton.GC.collect ()
      val _ = f 100
   end
   
   
structure CId =
   CId (structure F = MLton.Finalizable
          structure Prim =
             struct
			    val (res: Word32.word) = 0wx37;
                val Id = _import "test_structur" public: Word32.word -> Word32.word;
				val _ = (if 0wx0 = (Id res)
                         then print "True \n"
                         else print "False \n");
             end)
			 
structure S = Test (structure CId = CId
                    structure MLton = MLton)*)



structure TestStruct = 
struct
val c_test_structur   = _import "test_structur" public: Word32.word -> Word32.word;
val c_return_x   = _import "return_x" public: Word32.word -> int;

val (res: Word32.word) = 0wx37;
												  
								  
val _ = (if c_return_x(res: Word32.word) = 0
         then print "True \n"
         else print "False \n");		
						
end