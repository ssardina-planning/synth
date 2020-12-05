#include <storage.h>
#include <hash.h>
#include <node.h>
#include <assoc.h>

static mgr_ptr assoc_mgr;

#define ASSOC_HASH_SIZE 127

/* Create new record manager.  Initialized from main.c */
void init_assoc(void)
{
  assoc_mgr = new_mgr(sizeof(struct assoc));
}

/* Hash function for the hash structure */
static int assoc_hash_fun(rec_ptr assoc)
{
  return (int) (((assoc_ptr) assoc)->x);
}

/* Equivalence function for the hash structure */
static int assoc_eq_fun(rec_ptr a1, rec_ptr a2)
{
  return (((assoc_ptr) a1)->x) == (((assoc_ptr) a2)->x);
}

/* Create new association hash table */
hash_ptr new_assoc(void)
{
  return new_hash(ASSOC_HASH_SIZE, assoc_hash_fun, assoc_eq_fun, assoc_mgr);
}

/* Find the node associated with x */
node_ptr find_assoc(hash_ptr hash, node_ptr x)
{
  assoc_rec a;
  assoc_ptr b;
  a.x = x;
  b = (assoc_ptr) find_hash(hash, (rec_ptr) &a);
  if (b)
    return b->y;
  else
    return NIL;
}

/* Insert or update the association in the hash structure */
void insert_assoc(hash_ptr hash, node_ptr x, node_ptr y)
{
  assoc_rec a, *b;
  a.x = x;
  a.y = y;
  b = (assoc_ptr) insert_hash(hash, (rec_ptr) &a);
  b->y = y;
}

/* Remove an association from the hash structure */
void remove_assoc(hash_ptr hash, node_ptr x, node_ptr y)
{
  assoc_rec a;
  a.x = x;
  a.y = y;
  remove_hash(hash, (rec_ptr) &a);
}

void (*assoc_free_hook)(node_ptr y);

void free_assoc(assoc_ptr a)
{
  if (assoc_free_hook)
    (*assoc_free_hook)(a->y);
}

/* Clear the association hash structure using the supplied free hook */
/* The free_hook procedure will be activated for every freed link in */
/* the hash structure.                                               */
void clear_assoc(hash_ptr hash, void (*free_hook)(node_ptr y))
{
  assoc_free_hook = free_hook;
  assoc_mgr->free_hook = (void (*)(rec_ptr y)) free_assoc;
  clear_hash(hash);
  assoc_mgr->free_hook = 0;
}

/* Go over all associations in hash and call the hook for each of
   them. */
void visit_assoc(hash_ptr hash,
                 void (*walk_hook)(node_ptr x, node_ptr y))
{
  int i;
  for(i=0;i<hash->size;i++){
    assoc_ptr p = (assoc_ptr) hash->tab[i];
    for(; p; p = p->link){
      walk_hook(p->x, p->y);
    }
  }
}
