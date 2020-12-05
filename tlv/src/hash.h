/***********************************************************************
 This file provides hash tables.
 The following is a description of the functions:

 1) hash_ptr new_hash(int init_size,
                      int (*hash_fun)(rec_ptr),
                      int (*eq_fun)(rec_ptr,rec_ptr),
                      mgr_ptr)

    Create a new hash structure which contains a hash table.

    The first parameter is the number of entries which will be allocated

    for the hash table.
    The second parameter is a hash function on the records.

    The third parameter is a function which determines equality of
    two records.

    The fourth parametere is a record manager which is used for 
    creating links in the linked lists of the hash table.

 2) rec_ptr find_hash(hash_ptr,rec_ptr)

    Find a record in the hash table. If it is found then return the pointer.
    If the record is not found then 0 is returned.

 3) rec_ptr insert_hash(hash_ptr,rec_ptr)

    First it checks if the record exists in the hash table.
    If it exists then the pointer to the record is returned.
    If it does not exist then a duplicate of the record is added
    at the end of the linked list and the pointer to the duplicate is
    returned.

 4) void clear_hash(hash_ptr)
  
    Clear all linked lists of hash table.

 5) void remove_hash(hash,rec)

    This function appears only in the body.
    It removes a record from the hash table.
    If the record doesn't exist then this is an error and the program
    halts.

 ***********************************************************************/

#ifndef HASHHDEF
#define HASHHDEF

/* Define hash structure types "hash_rec" and "hash_ptr" */
typedef struct hash {
  int size;           /* Number of entries of the hash table. */
  int (*hash_fun)(rec_ptr r);  /* Hash function on rec_ptr. */
  int (*eq_fun)(rec_ptr a, rec_ptr b);  /* Equality function on two rec_ptr parameters. */
  mgr_ptr mgr;        /* Record manager which is used for the links. */
  rec_ptr *tab;       /* The hash table. */
} hash_rec,*hash_ptr;


/* Functions */
hash_ptr new_hash(int init_size,
                  int (*hash_fun)(rec_ptr r),
                  int (*eq_fun)(rec_ptr a, rec_ptr b),
                  mgr_ptr mgr);

rec_ptr find_hash(hash_ptr hash, rec_ptr rec);
rec_ptr insert_hash(hash_ptr hash, rec_ptr rec);
void remove_hash(hash_ptr hash, rec_ptr rec);

void clear_hash(hash_ptr hash);

#endif
