#setting gdb options 
 set logging file Example_sequential.log 
 set logging on 
 set pagination off 
 set target-async on 
 set non-stop on 
 set print thread-events off 
 
#setting thread entry 
 break 68 
 commands 
 silent 
 thread 3 
 continue 
 end 
 
 #setting thread exit 
 break 77 
 commands 
 silent 
 thread 3 
 continue 
 end 
 
#setting thread entry 
 break 77 
 commands 
 silent 
 thread 3 
 continue 
 end 
 
 #setting thread exit 
 break 79 
 commands 
 silent 
 thread 3 
 continue 
 end 
 
#setting thread entry 
 break 79 
 commands 
 silent 
 thread 3 
 continue 
 end 
 
 #setting thread exit 
 break 81 
 commands 
 silent 
 thread 99 
 continue 
 end 
 
#setting thread entry 
 break 50 
 commands 
 silent 
 thread 2 
 continue 
 end 
 
 MyKeOS.in_c.alloc 5 1 nat 8466#setting thread entry 
 break 59 
 commands 
 silent 
 thread 2 
 continue 
 end 
 
 MyKeOS.in_c.release 5 1 nat 2153#setting thread entry 
 break 61 
 commands 
 silent 
 thread 2 
 continue 
 end 
 
 MyKeOS.in_c.status 5 1#setting main thread entry 
 break 123 
 commands 
 silent 
 set scheduler-locking on 
 continue 
 end 
 
 #wait for thread creation 
 break 137 
 commands 
 silent 
 thread 3 
 continue 
 end 
 
start 
