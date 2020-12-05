/* For malloc */
#include <storage.h>
#include <stdio.h>
#include <stdlib.h>
#include <hash.h>

#if SYSTEM==cyg
#include <string.h>
#else
/* We need the following for "bzero". */
#include <strings.h>
#endif

/* Create a new hash table */
hash_ptr new_hash(int init_size,
                  int (*hash_fun)(rec_ptr r),
                  int (*eq_fun)(rec_ptr a, rec_ptr b),
                  mgr_ptr mgr)
{
  /* Allocate memory for hash record */
  hash_ptr res = (hash_ptr)malloc(sizeof(struct hash));

  res->size = init_size;
  res->hash_fun = hash_fun;
  res->eq_fun = eq_fun;
  res->mgr = mgr;

  init_size *= sizeof(rec_ptr);

  /* Allocate a block of memory which will contain "init_size"
     pointer to records. This is the actual hash table */
  res->tab = (rec_ptr *)malloc(init_size);

#if SYSTEM==cyg
  memset(res->tab,0,init_size);
#else
  bzero(res->tab,init_size);
#endif

  return(res);
}

/* Clear the hash structure by going over the hash table and freeing 
   all of the linked lists. */
void clear_hash(hash_ptr hash)
{
  int i;
  for(i=0;i<hash->size;i++){
    rec_ptr p = hash->tab[i];
    while(p){
      rec_ptr q = p;
      p = p->link;
      free_rec(hash->mgr,q);
    }
    hash->tab[i] = 0;
  }
}

/* Find a record in the hash table. It is is found then the pointer
   to the link is returned, else 0 is returned. */
rec_ptr find_hash(hash_ptr hash, rec_ptr rec)
{
  int (*eq_fun)(rec_ptr a, rec_ptr b) = hash->eq_fun;
  rec_ptr *p = hash->tab + (((unsigned)(*hash->hash_fun)(rec)) % hash->size);
  while(*p){
    if((*eq_fun)(*p,rec))return(*p);
    p = &((*p)->link);
  }
  return(0);
}

/* Insert a record into the hash table */
rec_ptr insert_hash(hash_ptr hash, rec_ptr rec)
{
  int (*eq_fun)(rec_ptr a, rec_ptr b) = hash->eq_fun;
  rec_ptr *p = hash->tab + (((unsigned) (*hash->hash_fun)(rec)) % hash->size);
  while (*p) {
    if ((*eq_fun)(*p, rec))
      return *p;
    p = &((*p)->link);
  }
  /* Inserts record at end of list of hash entry */
  *p = dup_rec(hash->mgr, rec);
  return *p;
}


/* This function is used only by assoc.c .
   It removes a record from the hash table.
   If the record is not found then this is an error */
void remove_hash(hash_ptr hash, rec_ptr rec)
{
  int (*eq_fun)(rec_ptr a, rec_ptr b) = hash->eq_fun;

  /* Find list where the record is in */
  rec_ptr *p = hash->tab + (((unsigned)(*hash->hash_fun)(rec)) % hash->size);

  /* Find the record in the linked list */
  while(*p){
    if((*eq_fun)(*p,rec)){
      /* The record has been found so remove it from the list */
      rec_ptr q = *p;
      *p = (*p)->link;
      free_rec(hash->mgr,q);
      return;
    }
    p = &((*p)->link);
  }

  /* The record has not been found in the hash table.
     This should never happen */
  fprintf(stderr,"Internal error\n");
  fprintf(stderr,"remove_hash: record not found\n");
  exit(1);
}

