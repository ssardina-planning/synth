/***********************************************************************
 This is the header of the storage manager.                      

 It supplies two basic memory services:

  1) General services like "malloc" and "free".

  2) Record managers.
     These are lists of records of the same size.
     Records can be allocated, duplicated and freed.

     The following routines are for record managers:

     1) mgr_ptr new_mgr(rec_size)

        Returns a new record manager for records of size rec_size.

     2) rec_ptr new_rec(mgr_ptr)

        Get a new record via the record manager.

     3) rec_ptr dup_rec(mgr_ptr,rec_ptr)

        Get a new record which is a duplicate of an existing record .

     4) void free_rec(mgr_ptr,rec_ptr)

        Free the record to the record manager.

  3) A routine which returns the amount of memory allocated so far:
   
       unsigned int get_bytes_allocated();

 For this package to work the "initial_storage" procedure must be 
 called first.
 ***********************************************************************/

#ifndef STORAGEHDEF
#define STORAGEHDEF

/* Define record types ( which contains a pointer for linking ) */
typedef struct rec {
  struct rec *link;
} rec_rec, *rec_ptr;

/* Define record manager types */
typedef struct mgr{
    rec_rec free;        /* Free list */
    int  rec_size;       /* Record size of manager */
    int count;
    void (*free_hook)(rec_ptr r); /* Pointer to hook function which is activated
                            when a record is freed */
} mgr_rec, *mgr_ptr;

/* Initialize storage. Called from main.c */
void init_storage();

/* Standard "malloc(size)" and "free(pointer)" routines */
/* char *malloc();
void free(); */


/* Routines which handle record managers                 */
mgr_ptr new_mgr(int rec_size);

rec_ptr new_rec(register mgr_ptr mp);
rec_ptr dup_rec(mgr_ptr mp, rec_ptr r);
void free_rec(register mgr_ptr mp, rec_ptr r);

/* Get the number of bytes allocated */
unsigned int get_bytes_allocated();

#endif
