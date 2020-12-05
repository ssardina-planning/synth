/***********************************************************************
 This file defines routines for creating and accessing 
   association hash tables.

 An association is simply a pair of two nodes (x,y) of type node_ptr. 

 The following functions are provided:

 1) hash_ptr new_assoc();

    Create new association hash strutcure.

 2) node_ptr find_assoc(hash_ptr,node_ptr x);

    If node x appears in association hash structure then y is returned.
    Else the constant NIL is returned.

 3) void insert_assoc(hash_ptr,node_ptr x,node_ptr y);

    Insert the association of (x,y) into the hash structure.

    If an associate (x,z) already exists then (x,y) is inserted
    *instead* of this. So to update an association there is no need to
    remove.

 4) void init_assoc()

    Initialize this file.

 5)  Go over all associations in hash and call the hook for each of them.
   void visit_assoc(hash_ptr hash,
                    void (*walk_hook)(node_ptr x, node_ptr y));

 ***********************************************************************/

#ifndef ASSOCHDEF
#define ASSOCHDEF

/* Define assoc record types. This is similar to the rec_ptr type
   defined in "storage.h", but it contains two extra fields: x,y */
typedef struct assoc {
  struct assoc *link;
  node_ptr x;
  node_ptr y;
} assoc_rec,*assoc_ptr;

void init_assoc(void);

hash_ptr new_assoc(void);

node_ptr find_assoc(hash_ptr hash, node_ptr x);
void insert_assoc(hash_ptr hash,
                  node_ptr x, node_ptr y);

void remove_assoc(hash_ptr hash, node_ptr x, node_ptr y);

void clear_assoc(hash_ptr hash,
                 void (*free_hook)(node_ptr y));

void visit_assoc(hash_ptr hash,
                 void (*walk_hook)(node_ptr x, node_ptr y));

#endif
