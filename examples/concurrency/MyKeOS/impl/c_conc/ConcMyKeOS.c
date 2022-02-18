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

/* thread informations and shared variable*/
typedef 
struct ID
{   int taskID;
    int thID;
	int var;	
}id;
 
/*a library containing operations on the shared variable*/

int alloc (id *ij, int x)
{ 
  /* Action Thread 1 */
   (*ij).var = (*ij).var + x;
   printf("Task: %d Thread: %d State:%d \n", (*ij).taskID, (*ij).thID, (*ij).var);
   return (*ij).var; 
}

int release (id *ij, int x)
{ /* Action Thread 1 */
   (*ij).var = (*ij).var - x;
   printf("Task: %d Thread: %d State:%d \n", (*ij).taskID, (*ij).thID, (*ij).var);
   return (*ij).var;
}

int status (id *ij)
{  
  /* Action Thread 1 */
   printf("Task: %d Thread: %d State:%d \n",  (*ij).taskID, (*ij).thID, (*ij).var);
   return (*ij).var;
}

/*Behaviours of threads generated in Isabelle*/
void *behaviour1 (void *ij)
{ id  *x = (void *)ij; 
   
  /* Action Thread (5,1) */
  (*x).taskID = 5;
  (*x).thID = 1;
  (*x).var = 7;
  
  (*x).var = alloc (x, 3);
  
  (*x).var = release (x, 8);
  
  (*x).var = status (x);
  
   //sleep(rand() % 3);
   return NULL;
}

void *behaviour2 (void *ij)
{ id  *x = (void *)ij; 
   
  /* Action Thread (5,0) */
  (*x).taskID = 5;
  (*x).thID = 0;
  (*x).var = 5;
  
  (*x).var = alloc (x, 2);
  
  (*x).var = release (x, 6);
  
  (*x).var = status (x);
  
   //sleep(rand() % 3);
   return NULL;
}


void *behaviour3 (void *ij)
{ id  *x = (void *)ij; 
   
  /* Action Thread (3,1) */
  (*x).taskID = 3;
  (*x).thID = 1;
  (*x).var = 2;
  
  (*x).var = alloc (x, 2);
  
  (*x).var = release (x, 3);
  
  (*x).var = status (x);
  
   //sleep(rand() % 3);
   return NULL;
}

void *behaviour4 (void *ij)
{ id  *x = (void *)ij; 
   
  /* Actions Thread (3,0) */
  (*x).taskID = 3;
  (*x).thID = 0;
  (*x).var = 8;
  
  (*x).var = alloc (x, 3);
  
  (*x).var = release (x, 9);
  
  (*x).var = status (x);
  
   //sleep(rand() % 3);
   return NULL;
}

int mann(id ij) /* */
{ 



ij.taskID = 2;
ij.thID = 1;
ij.var=0;
	
 pthread_t thread1, thread2, thread3, thread4;
    /* Creation des threads*/
    pthread_create (&thread1, NULL, behaviour1, &ij);
	pthread_create (&thread2, NULL, behaviour2, &ij);
	//pthread_create (&thread3, NULL, behaviour3, &ij);
	//pthread_create (&thread4, NULL, behaviour4, &ij);
	
    /* Lancement des Thread */
	/* Le thread principal "Main" attend la fin des deux threads pour continuer */
    pthread_join(thread1, NULL);
	pthread_join(thread2, NULL);
	//pthread_join(thread3, NULL);
	//pthread_join(thread4, NULL);
    printf("fin des deux thread %d \n", ij.var);	
	//pthread_exit(NULL);
	return 0;
		
} /* main() */

int get_x (int x)
{ id ij;
   x = 0;
  x = mann (ij);
  return x ;	
}

