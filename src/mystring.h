/***********************************************************************
 This file access a string hash table defined in string.c .

 It should be intialized by calling init_string.

 The function 

  string_ptr find_string(char *x)

  Searches for the string x in the hash table.
  If it is found the pointer to it in the hash table is returned.
  If it does not exist in the hash table then it is inserted.

  So what "find_string" actually does is build a hash table
  with all strings found.
 
 ***********************************************************************/

#ifndef MYSTRINGHDEF
#define MYSTRINGHDEF

/* Define two types: a string record ( string_rec ),                 */
/*                   and a pointer to a string record ( string_ptr ) */
typedef struct string{
  struct assoc *link;
  char *text;
} string_rec,*string_ptr;

/* Accepts an input parameter of "char *" and returns pointer to */
/* string record.                                                */
string_ptr find_string(char *x);

/* Initializes string hash table. Called from main.c */
void init_string();

#endif
