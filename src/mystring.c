/* For malloc */
#include <stdlib.h>

#include <storage.h>
#include <hash.h>
#include <mystring.h>

/* String record manager */
static mgr_ptr string_mgr;

/* String hash table */
static hash_ptr string_hash;
#define STRING_HASH_SIZE 511


/* Hash function on the string text returning int */
static int string_hash_fun(rec_ptr string)
{
  char *p = ((string_ptr)string)->text;
  unsigned h = 0;
  while(*p)h = (h<<1) + *(p++);
  return(h);
}

/* Returns true if two string are equal */
static int string_eq_fun(rec_ptr a1, rec_ptr a2)
{
  return(strcmp( ((string_ptr)a1)->text,((string_ptr)a2)->text)==0);
}

/* Initialize string hash table. */
void init_string(void)
{
  /* Create string record manager */
  string_mgr = new_mgr(sizeof(struct string));

  /* Create string hash structure */
  string_hash = new_hash(STRING_HASH_SIZE,string_hash_fun,
			 string_eq_fun,string_mgr);
}


/* Finds the string in the hash table. If it isn't in the hash table
   then insert it. */
string_ptr find_string(char *x)
{
  string_rec a,*res;
  a.text = x;

  /* If the string is already in the hash table return the pointer to it */
  if(res = (string_ptr)find_hash(string_hash,(rec_ptr)&a))return(res);

  /* Allocate space for the text of x */
  a.text = (char *)strcpy((char *)malloc(strlen(x)+1),x);

  /* Insert the string record ( containing x ) to the hash table */
  return((string_ptr)insert_hash(string_hash,(rec_ptr)&a));
}
