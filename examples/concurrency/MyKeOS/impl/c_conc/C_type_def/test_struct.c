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


typedef struct ID
{   int taskID;
    int thID;
	int var;	
} Id;
 
Id test_structur (Id x)
{ 
  x.taskID = 2;
  x.thID = 1;
  x.var=0;
  return x;
}

int return_x (Id x)
{x.var = 2;
	
return (test_structur (x).var);
}
//int main()
//{ Id ij; 
  //printf("value is %d \n", test_structur (ij).var);
  //return 0	;
//}


