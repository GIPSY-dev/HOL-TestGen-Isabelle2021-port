/*
 ============================================================================
 Name        : ConcurrentThreads_sleep.c
 Author      : Yakoub
 Version     :
 Copyright   : Your copyright notice
 Description : Hello World in C, Ansi-style
 ============================================================================
 */
#include <stdio.h>  
#include <stdlib.h>  
#include <pthread.h>      


//int start = 0;
int alloc (int taskid, int thid, int x)
{ 
    /* Action Thread 1 */
   taskid= 1;
   thid= 1;
   return x+1;
}


int release (int taskid, int thid, int x)
{ 
    /* Action Thread 1 */
   taskid= 1;	
   thid= 1;
   return x-1;
}

int status (int taskid, int thid, int x)
{ 
    /* Action Thread 1 */
   taskid= 1;	
   thid= 2;
   return x;
}




