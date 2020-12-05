/********************************************************************
*                                                                   *
*     Copyright (C) 1990, Carnegie-Mellon University                *
*                                                                   *
*     Numerous additions in Weizmann institute.                     *
*                                                                   *
*********************************************************************/

/* BDD routines */


/* If 1 then allow reordering. I think it is a good idea to
   erase this symbol, and just have the code always be able
   to do reordering.  */ 
#define REORDER 1



/* For malloc */
#include <stdlib.h>

#include <stdio.h>
#include <storage.h>
#include <bdd.h>
#include <node.h>
#include <hash.h>
#include <assoc.h>
#include <math.h>
#include <util_err.h>
#include "y.tab.h"


/* Variable number from which to start allocating. */
int NSTBASE = 0;
int nstvars ; /* nstvars contains maximal (bdd level/2) allocated. */

/* variables used in "init_bdd" */
int KEYTABLESIZE=126727, APPLY_CACHE_SIZE=522713, MINI_CACHE_SIZE=522713;


/* Minimal number of nodes for garbage collection.  */
#define MIN_NODES 10000

/* Garbage collection threshould.  */
int gc_threshold = MIN_NODES;

static int maxnodes;		/* garb collect threshold */

/* Variables which are used for reordering. */
int reorder=0;
int reorder_bits= 10;
int reorder_size = 5000;


static node_ptr save_bdd_list=NIL;  /* list of bdds in use */
int save_bdd_list_length = 0;

/* Record manager for bdd strutures */
static mgr_ptr bdd_mgr;


int allocatecount, disposecount, garbagecollectcount;

/* Define structure under which all bdd records reside */
static keytable_rec reduce_table;

static int verbose=0;

/* Define apply cache. The apply cache saves the results of 
   evaluations of bdd's. */
static apply_rec *apply_cache;
static int apply_cache_size;

static hash_ptr shared_vars_hash;

/* Constants for bdd leafs one and zero  */
bdd_ptr ONE,ZERO;


/****** Variables used for reordering. ******/

/* This is the current size of the following arrays. 
   So the arrays range from 0 till top_level - 1. */
int top_level=-1; 

/* The number of bdd nodes at each level. */
static int *n_bdd_at_level;

/* Each entry is a list of all bdd nodes at that level. */
static bdd_ptr *bdd_at_level;


int             primes[] = {
			    2,
			    3,
			    7,
			    13,
			    31,
			    61,
			    127,
			    251,
			    509,
			    1021,
			    2039,
			    4093,
			    8191,
			    16381,
			    32749,
			    65521,
			    126727,	/* 359 353	 */
			    262063,	/* 503 521	 */
			    522713,	/* 719 727	 */
			    1046429,	/* 1013 1033	 */
			    2090867,	/* 1439 1453	 */
			    4186067,	/* 2039 2053	 */
			    8363639,	/* 2887 2897	 */
			    16777207,	/* 4093 4099	 */
			    33489353,	/* 5791 5783	 */
			    670757739,	/* 8171 8209	 */
			    134168873,	/* 11579 11587	 */
			    268303439,	/* 16349 16411	 */
			    536848891,	/* 23167 23173	 */
			    1073217479,	/* 32749 32771	 */
			    /* 2146654199,	 46327 46337	 */
			    /* 4294442903,	 65521 65543	 */
			    /* 8588840951	 92671 92681	 */
};


/* This array contains for each level which is the root of 
   the support of a program variable, the name of that variable.  */
node_ptr *variable_names;

/* List of all program variables.  */
extern node_ptr variables;

/* Obtain support bdd from variable name.  */
extern bdd_ptr get_bdd_of_var();

/* The maximum level beyond which there are no bdds (calculated
   during reordering. */
static int max_level = -1;


/* Fill the array "variable_names" such that each entry which is
   the level of a node which is the root of the support bdd of a
   variable, points to the node_ptr of the term of the variable. */
void set_variable_names(void)
{
  node_ptr l;
  int i;
 
  /* Clear the array "variable_names". */
  for(i = 0; i< ( max_level == -1 ? nstvars*2 : max_level ) ; i++)
    variable_names[i] = NIL;
    
  for(l = variables; l; l = cdr(l))
    { bdd_ptr f = get_bdd_of_var(car(l));
      variable_names[GETLEVEL(f)] = car(l);
    }
}

void *myrealloc(void *arr, int oldsize, int newsize)
{
  void *new_arr = malloc(newsize);

  /* Copy oldarray to new array */
  memcpy(new_arr,arr,oldsize);

  /*free(arr);*/

  return new_arr;
}

/* Call this whenever variables are created. (or after the 
   creation of a set of variables.) This is similar to set_variables_names,
   but also can change the size of the various arrays. */
void set_var_names(void)
{
  node_ptr l;
  int i;
  int is_first = (top_level == -1);
  int old_top_level = top_level;

  /* Check to see if the three arrays are of appropriate size. */
  if (top_level < nstvars * 2 + 16)
    {
      top_level = nstvars * 2 + 16; /* The 16 is just for safety. */
      if (is_first)
      {
        n_bdd_at_level = (int *)     malloc(top_level * sizeof(int));
        bdd_at_level   = (bdd_ptr *) malloc(top_level * sizeof(bdd_ptr));
        variable_names = (node_ptr *)malloc(top_level * sizeof(node_ptr));
      }
      else
      {
#if SYS==cyg
        n_bdd_at_level = (int *) myrealloc((void *)n_bdd_at_level,
                                             old_top_level * sizeof(int),
                                             top_level * sizeof(int));
        bdd_at_level = (bdd_ptr *) myrealloc((void *)bdd_at_level,  
                                             old_top_level * sizeof(bdd_ptr),        
                                             top_level * sizeof(bdd_ptr));
        variable_names = (node_ptr *) myrealloc((void *)variable_names,
                                              old_top_level * sizeof(node_ptr),
                                              top_level * sizeof(node_ptr));
#else
        n_bdd_at_level = (int *) realloc((void *)n_bdd_at_level,
                                             top_level * sizeof(int));
        bdd_at_level = (bdd_ptr *) realloc((void *)bdd_at_level,  
                                             top_level * sizeof(bdd_ptr));
        variable_names = (node_ptr *) realloc((void *)variable_names,
                                             top_level * sizeof(node_ptr));
#endif
      }
    }


 /* Clear the array "variable_names". */
  for(i = 0; i<nstvars*2+8; i++)
    variable_names[i] = NIL;
    
  for(l = variables; l; l = cdr(l))
    { bdd_ptr f = get_bdd_of_var(car(l));
      variable_names[GETLEVEL(f)] = car(l);
    } 
}



/* Create a keytable. */
/* Keytable is the hash table which allows us
   to keep BDD in reduced form 
   kp -> n is the size of the table
   kp -> elements_in_table is the total number
            of BDD nodes in all hash bins
   kp -> hash_table_buf points to an array
            of pointers to BDD nodes.
	    all pointers all initialized to NULL
*/
static void create_keytable(register keytable_ptr kp,
                            register int n)
{

#ifdef REORDER
  if(!reorder)
#endif
   {  /* Adjust n to be a number in primes[]. */
      register int i;
      for (i = 1; primes[i] <= n; i++) ;
      n = primes[i - 1];
   }

   /* Initialize a keytable. */
   kp->n = n;
   kp->elements_in_table = 0;
   kp->hash_table_buf = (bdd_ptr *)malloc(n*sizeof(bdd_ptr));

   {  /* Initialize hash bin list pointers to NULL. */
      register int i;
      for (i = 0; i < n; i++) kp->hash_table_buf[i] = NULL;
   }
}

/* Initialize the BDD package.
   This creates the keytable and the apply cache.
   Size of the keytable is given by global KEYTABLESIZE
   Size of the apply cache is given by global APPLY_CACHE_SIZE
 */
void init_bdd(void)
{
   nstvars = NSTBASE;

   /* Intialize bdd record manager */
   bdd_mgr = new_mgr(sizeof(struct bdd));

   allocatecount = garbagecollectcount = disposecount     = 0;

   /* Create key tables. */
   create_keytable(&reduce_table, KEYTABLESIZE);

   /* Create apply cache */
   apply_cache_size = APPLY_CACHE_SIZE;
   apply_cache = (apply_rec *)malloc(sizeof(apply_rec)*apply_cache_size);
   {
     int i;
     for(i=0;i<apply_cache_size;i++)apply_cache[i].op = 0;
   }

   /* set up constant symbols for bdd.c */
   ZERO = save_bdd(leaf_bdd(zero_number));
   ONE  = save_bdd(leaf_bdd(one_number));

   /* Initialize maxnodes. */
   maxnodes = gc_threshold;

   shared_vars_hash = new_assoc();
}

/* Return the leaf node of aleaf bdd.  */
node_ptr leaf_value(bdd_ptr b)
{
  return (node_ptr)(b->left);
}

/* Take a node, and return a leaf bdd where the node is the leaf. */
bdd_ptr leaf_bdd(node_ptr n)
{
  return(find_bdd(LEAFLEVEL, (bdd_ptr) n,0));
}

/* Returns atomic bdd for a current variable of n ( which number (i.e level) is
   actually 2*n). The atomic bdd for variable n looks like this:

         2*n
        /  \
       0    1 */
bdd_ptr atomic_bdd(int n)
{
  return find_bdd(THE_CURRENT_VAR(n), ZERO, ONE);
}

#define HASHING(d1, d2, d3, n) ((((unsigned) (d1)) + (((unsigned) (d2))<<1) + (((unsigned) (d3))<<2)) % ((unsigned) (n)))

/* find_bdd returns a BDD node whose left
   pointer is to d1, right pointer is to d2,
   and whose level is "level".
   if such a node already exists, a pointer
   to this node is returned, else a 
   new node is created. This routine is
   used to keep BDD's in reduced form.
   Note also, that if d1 == d2, this node
   is redundant, so we return d1.
*/

bdd_ptr find_bdd(register int level, register bdd_ptr d1, register bdd_ptr d2)
{
  register int hash_num;
  register bdd_ptr *q,p,d;
  if (d1==d2 && level != LEAFLEVEL)
    return d1;
  /* here we use level, d1 and d2 to hash into
     the key table */
  hash_num = HASHING(d1, d2, level, reduce_table.n);
  q = reduce_table.hash_table_buf + hash_num;
  /* q is a pointer to the element in the hash table */
  p = *q;
  /* p is a pointer to the first element of the list (or NULL) */
  /* search the list. if any node matches level,d1,d2, return it */
  while (p &&
         (p->left != d1 ||
          p->right != d2 ||
          GETLEVEL(p) != level))
    p = p->next;
  if (p) return p;
  /* otherwise, create a new node, and fill in the fields with
     level,d1,d2 */
  d = (bdd_ptr) new_rec(bdd_mgr);
  allocatecount++;
  d->left = d1;
  d->right = d2;
  d->dfield = 0;
  SETLEVEL(d, level);
  /* now make the new node the first element of the list */
  d->next = *q;
  *q = d;
  reduce_table.elements_in_table += 1;  /* update count of total nodes */
  return(d);
}

/* Sweep bdds in reduce table. */
/* Deletes any BDD nodes which do not have their
   mark field set. This is done by scanning the keytable structure
   which is called "reduce_table" in bdd.c .
   This is done to free memory .*/
void sweep_reduce()
{
  register bdd_ptr *p = reduce_table.hash_table_buf;
  register int n;
  for (n = reduce_table.n; n>0; n--, p++) {
    register bdd_ptr *q = p;
    while (*q) {
      if (TESTMARK(*q)) {
        CLEARMARK(*q);
        q = &((*q)->next);
      }
      else {
        free_rec(bdd_mgr, (rec_ptr) *q);
        *q = (*q)->next;
        disposecount++;
        reduce_table.elements_in_table--;
      }
    }
  }
}

void set_bdd_verbose(int val)
{
  verbose = val;
}

#ifdef REORDER

/* List of all bdd nodes which are leafs. */
static bdd_ptr constant_bdd_nodes;

/* This function seperates all bdd nodes depending on their level. and
remove all of them form the global hash table. */
void devide_bdd_by_level()
{
  register bdd_ptr *p = reduce_table.hash_table_buf;
  register int n;

  /* Clear arrays. */
  for (n = 0; n<top_level; n++) {
    n_bdd_at_level[n] = 0;
    bdd_at_level[n] = NULL;
  }

  constant_bdd_nodes = NULL;

  /* Sort bdds into the array bdd_at_level and the variable
     constant_bdd_nodes. Also remove them from the reduce table. */
  for (n = reduce_table.n; n>0; n--, p++) {
    register bdd_ptr q;
    register int level;
    while (q = *p) {
      level = GETLEVEL(q);

      /* This line changes the head of the current list in the
         array reduce_table.hash_table_buf. In effect it take the
         head (q) out of the list and puts its "next" as the head. */
      *p = q->next;

      if (level == LEAFLEVEL) {
        q->next = constant_bdd_nodes;
        constant_bdd_nodes = q;
      }
      else {
        n_bdd_at_level[level]++;
        q->next = bdd_at_level[level];
        bdd_at_level[level] = q;
      }
    }
  }

  /* Set max_level by finding last entry in "n_bdd_at_level" which
     has elements. */
  max_level = top_level-1;
  while (max_level>0 && !n_bdd_at_level[max_level-1])
    max_level--;

  if (max_level%2)
    max_level++;
}

/* Adds bdd "q" to the reduce table and returns the bdd
   which is in q->next. */
bdd_ptr add_to_hash_table(bdd_ptr q)
{
  register bdd_ptr p;
  register unsigned int hash_num;
  hash_num = HASHING(q->left, q->right, GETLEVEL(q), reduce_table.n);
  p = q->next;
  CLEARMARK(q);
  q->next = reduce_table.hash_table_buf[hash_num];
  reduce_table.hash_table_buf[hash_num] = q;
  return(p);
}

static int bdd_independent;

/* This function attempts to swap the variable ordering of level1 and level2.
   Only called from "swap_variable_group" - in this call
     level1 + 1 = level2 .  The reduce table is used as an intermediate
   storage place, but at the end of the routine the reduce table
   is empty again. */
void swap_variable(int level1, int level2)
{
  bdd_rec head1, head2;
  register bdd_ptr p, q;
  register bdd_ptr f00, f01, f10, f11;
  register int n;

  n = n_bdd_at_level[level1];
  n_bdd_at_level[level1] = n_bdd_at_level[level2];
  n_bdd_at_level[level2] = n;

  head1.next = bdd_at_level[level1];
  head2.next = bdd_at_level[level2];

  for(p =  &head1; q = p->next ; )
    { 
      if(GETLEVEL(q->left) != level2 && GETLEVEL(q->right) != level2)
	{ SETLEVEL(q, level2);
	  p->next = add_to_hash_table(q);
	}
      else
	p = p->next;
    }
  
  /* If head.next == 0 then this means that in the previous loop
     all the "q" nodes were added to the hash table. This means that
     there are no nodes of level1 which have sons of level2. Since we
     know that level1 + 1 == level2 we can conclude that nodes with 
     level1 and level2 never appear together in a bdd and are thus
     indpendent. */
  if(head1.next)
    bdd_independent = 0;

  /* For all nodes which *are* dependent, switch the location of 
     the level2 and level1 nodes. This loop might create new level2
     nodes which will be stored in the reduce_table. */
  for(p = head1.next; p ; p = q)
    { q = p->next;
      if(GETLEVEL(p->left) == level2)
	{ f00 = p->left->left;
	  f01 = p->left->right;
	}
      else
	f00 = f01 = p->left;
      if(GETLEVEL(p->right) == level2)
	{ f10 = p->right->left;
	  f11 = p->right->right;
	}
      else
	f10 = f11 = p->right;

      p -> left = (f00 == f10)? f00 : find_bdd(level2, f00, f10);
      p -> right = (f01 == f11)? f01 : find_bdd(level2, f01, f11);
    }

  for(p = &head2; q = p->next; p = q)
    SETLEVEL(q, level1);

  p->next = head1.next;


  bdd_at_level[level1] = head2.next;


  /* Make bdd_at_level[level2] point to list of all bdds which 
     are in reduce table. */
  bdd_at_level[level2] = NULL;
  for (n = 0; n<reduce_table.n; n++) 
    if(q = reduce_table.hash_table_buf[n])
      {
        /* Find tail of list. */
	while(q->next)  q = q->next;

        /* Connect the current reduce table list to bdd_at_level[level2]
           list. */
	q->next = bdd_at_level[level2];
	bdd_at_level[level2] = reduce_table.hash_table_buf[n];

        /* Remove list from reduce table. */
	reduce_table.hash_table_buf[n] = NULL;
      }
}

/* Try to deallocate bdd's between levels level1 and level2
   (including level1 but not including level2). */
void sweep_and_collect(int level1, int level2)
{
  register int i;
  bdd_rec head;
  register bdd_ptr p, q;
  register struct node *bddlist = save_bdd_list;

  /* Mark all nodes on "save_bdd_list" with level between level1 and level2 */
  while(bddlist)
    { register k = GETLEVEL(bddlist->left.bddtype);
      if(k>=level1 && k<level2)
	SETMARK(bddlist->left.bddtype);
      bddlist = bddlist->right.nodetype;
    }

  /* Go over all nodes with level smaller than level1. Mark all sons
     of these nodes if the son has level between level1 and level2. 
     I assume that this marking is done under the assumption that
     there is no need to free nodes with level below level1. */
  for(i = 0; i<level1; i++)
    for(p = bdd_at_level[i]; p ; p = p->next)
      { 
	if(GETLEVEL(p->left) >= level1 && GETLEVEL(p->left) < level2)
	  SETMARK(p->left);
	if(GETLEVEL(p->right) >= level1 && GETLEVEL(p->right) < level2)
	  SETMARK(p->right);
      }

  /* Deallocate all unmarked nodes with levels between level1 and level2.
     If we encounter a marked node then mark his sons if the sons have
     level between level1 and level2, so that the sons will not be freed. 
     After this loop all markings are cleared. */
  for(i = level1; i<level2; i++)
    { head.next = bdd_at_level[i];
      p = &head;
      while(q = p->next)
	{
	  if(TESTMARK(q))
	    { CLEARMARK(q);
	      if(GETLEVEL(q->left) < level2)
		SETMARK(q->left);
	      if(GETLEVEL(q->right) < level2)
		SETMARK(q->right);
	      p = q;
	    }
	  else
	    { p->next = q->next;
	      free_rec(bdd_mgr,(rec_ptr)q);
	      disposecount++;
	      reduce_table.elements_in_table--;
	    }	    
	}
      bdd_at_level[i] = head.next;
    }
}

/* Move the group of variables in levels [level1,level2] (inclusive ??)
   such that variables at level2 will now be at level3. */
void swap_variable_group(int level1, int level2, int level3)
{
  bdd_rec head;
  bdd_ptr p, q;
  int i, j;

  bdd_independent = 1;

  for(i = level2-1; i>=level1; i--)
    for(j = 0; j<level3-level2; j++)
      swap_variable(i+j, i+j+1);

  if(!bdd_independent)
    sweep_and_collect(level1, level3-1);
}

/* This is the heart of the reordering algorithm. 
   Take a variable (whose level starts with "level") and move
   it to a better place. The function returns the level to which 
   the variable was moved. */
int find_optimal_position(int level)
{
  int i, level0, level1, level2;
  int current_min;
  int min_position;

  current_min = reduce_table.elements_in_table;
  min_position = level;

  /* Set level0 to be the level of the *next* variable. So the variable
     which we want to move will be from level "level" till level 
     "level0 - 1", inclusive.  */
  for(level0 = level+2; !variable_names[level0] && level0<max_level; level0+=2)
    ;

  if(verbose)
    { fprintf(stderr, " %d bits, ", level0-level);
      print_node(stderr, variable_names[level]);
    }

  /* Dont move a variable whose size in bits is larger than
     "reorder_bits" since it becomes expensive to move such
     a large group of variables together. */
  if(level0 > level+reorder_bits)
    { if(verbose)
	fprintf(stderr, ",  skip\n");
      return(level);
    }

  if(verbose) fprintf(stderr, "\n");

  /* Move variable to the *end*. */
  swap_variable_group(level, level0, max_level);
  set_variable_names();

  /* Now level1 contains the first level of the variable and level2,
     the last level of the variable. */
  level1 = max_level-level0+level;
  level2 = max_level;

  /* Try all possible locations for the variable, and remember
     when the minimum number of nodes is found. */
  while(level1 > 0) {

    for(i = level1-1; !variable_names[i] && i>0; i--)
      ;

    if(i == 0)
      break;

    swap_variable_group(i, level1, level2);

    /* Remember position where minimum # of nodes attained. */
    if(reduce_table.elements_in_table < current_min)
      { current_min = reduce_table.elements_in_table;
	min_position = i;
      }

    level2 -= (level1 - i);
    level1 = i;
    
  }

  set_variable_names();

  if(verbose)
    fprintf(stderr, " placed at %d with size %d\n", min_position, current_min);

  /* Move variable to place where minimum number of nodes obtained. */
  swap_variable_group(level1, level2, min_position+level0-level);
  set_variable_names();

  return(min_position);
}


static int last_reorder_size = 0;

#define max(a, b) (((a) > (b))? (a) : (b))

/* Main routine for reordering. */
#define DYNAMIC_REORDER 0
#define BY_VARS 1
void reorder_variables(int reorder_type, node_ptr vars)
{ 
  int selected_level = 0;
  int max_width;
  int i, j, k;
  int nvar = 0;
  bdd_ptr p;

  /* Save the size of the reduce_table "hash". */
  int hash_size = reduce_table.n;

  if( reorder_type == DYNAMIC_REORDER &&
      reduce_table.elements_in_table < 5 * last_reorder_size/4)
    return;


  if(verbose)
    fprintf(stderr, "start reordering variables with size %d\n", 
	    reduce_table.elements_in_table);

  /* Fill "bdd_at_level" array and remove nodes from reduce table. 
     Also set "n_bdd_at_level" array. */
  devide_bdd_by_level();

  set_variable_names();

  /* Deallocate all unsaved bdd nodes. (this deallcation routine 
     should only be called when the bdd nodes are stored in the
     array "bdd_at_level".) */
  sweep_and_collect(0, max_level);

  reduce_table.n = 251;

  j = 0;
  for(i = 0; i<max_level; i++)
    if(variable_names[i])
      j = i;
    else
      { n_bdd_at_level[j] = max(n_bdd_at_level[j], n_bdd_at_level[i]);
	n_bdd_at_level[i] = 0;
      }

  /* Loops which selects a variable which is to be moved, and moves
     it to a better place. */

  if (reorder_type == BY_VARS) {
    /* Set order according to list */
    node_ptr l;
    int target_level = 2, startvarlevel,endvarlevel;
     
    for (l = vars; l; l = cdr(l) )
    {
      node_ptr varname = car(l);

      /* Find level of variable. */
      bdd_ptr bddvar = get_bdd_of_var(varname);

      startvarlevel = GETLEVEL(bddvar);

      for (endvarlevel = startvarlevel+2; 
            !variable_names[endvarlevel] && endvarlevel<max_level; 
            endvarlevel += 2)
         ;

      /* Now the variable is in levels startvarlevel , till endvarlevel - 1 */

      if (verbose) {
        char vname[200];
        vname[0] = 0;

        sprint_node(vname,200, varname);
        fprintf(stderr,"Moving variable %s from level %d/%d to level %d\n",
                vname,
                startvarlevel, endvarlevel - 1, target_level);
      }

      /* Move variable to proper location. */
      swap_variable_group(target_level, startvarlevel, endvarlevel);
      set_variable_names();

      /* Update target location */
      target_level += endvarlevel - startvarlevel;
    }
  }
  else
    /* Dynamic reordering. */
    while(selected_level >=0)
      { 
        /* Select level which is to be moved. We select the variable
           which currently has a level of maximal width. */ 
        selected_level = -1;
        max_width = 4;
        for(i = 0; i<max_level; i++)
          if(n_bdd_at_level[i] > max_width && variable_names[i])
            { selected_level = i;
              max_width = n_bdd_at_level[i];
            }

        if(selected_level < 0)
          break;

        if(verbose)
          fprintf(stderr, " %2dth var, position %3d, width %3d, ", 
                 nvar++, selected_level, max_width);

        n_bdd_at_level[selected_level] = 0;

        /* Move level to best place. */
        find_optimal_position(selected_level);

      }

  set_variable_names();

  /* Reconstruct "variables" list according to new order. */
  variables = NIL;
  for(i = max_level-1; i>=0; i--)
    if(variable_names[i])
      variables = cons(variable_names[i], variables);

  output_order();

  /* Restore value of hash table. */
  reduce_table.n = hash_size;

  last_reorder_size = reduce_table.elements_in_table;

  /** Put all nodes back into reduce table!!! **/

  for(i = 0; i<max_level; i++)
    for(p = bdd_at_level[i]; p ; p = add_to_hash_table(p))
      ;
  for(p = constant_bdd_nodes; p ; p = add_to_hash_table(p))
    ;

}

#endif


#define OP_MASK   0x7fffffff
#define SAVE_MASK 0x80000000

void save_apply(int op,
                register bdd_ptr d1,register bdd_ptr d2)
{
  register apply_rec *a = apply_cache + 
                          HASHING(d1, d2, op, apply_cache_size);
  if(a->arg1 == d1 && a->arg2 == d2 && (a->op & OP_MASK) == op)
    a->op |= SAVE_MASK;
}

/* Insert an apply record into the apply cache */
/* op is the op code (see bdd.h)
   d1 is the first argument
   d2 is the second argument
   d is the result */
/* opcodes below USE_BIG_CACHE use only the portion
   of the hash table below MINI_CACHE_SIZE (set by 
   command line option) (USE_BIG_CACHE defined in bdd.h)
*/
void insert_apply(int op,
                  register bdd_ptr d1,register bdd_ptr d2,
                  register bdd_ptr d)
{
  register apply_rec *a = apply_cache +
     HASHING(d1, d2, op, ((op < USE_BIG_CACHE) ? MINI_CACHE_SIZE : apply_cache_size));
  if(!(a->op & SAVE_MASK)){
    a->op = op;
    a->arg1 = d1;
    a->arg2 = d2;
    a->res = d;
  }
}

/* Find an apply record in the apply cache */
/* op is the op code (see bdd.h)
   d1 is the first argument
   d2 is the second argument
   returns the result of the op if it is
   in the cache, else returns NULL
   (see insert_apply) */
bdd_ptr find_apply(int op,
                   register bdd_ptr d1, register bdd_ptr d2)
{
  register apply_rec *a = apply_cache +
     HASHING(d1, d2, op, ((op < USE_BIG_CACHE) ? MINI_CACHE_SIZE : apply_cache_size));
  if(a->arg1 == d1 && a->arg2 == d2 && (a->op & OP_MASK) == op)
    return(a->res);
  else
    return(NULL);
}

/* empty the apply cache of all entries except
   those with SAVE bit set. This is in preparation
   for garbage collection. Call mark_bdd on all
   results with SAVE bit set to protect them
   from garbage collection */

void flush_apply(void)
{
  int i=apply_cache_size;
  apply_rec *a=apply_cache;
  while(i--){
    if(a->op & SAVE_MASK)mark_bdd(a->res);
    else a->op = 0;
    a++;
    }
}


/* Repair (clear) mark field. */
void repairmark(register bdd_ptr d)
{
  if(!TESTMARK(d))return;
  CLEARMARK(d);
  if (ISLEAF(d)) return;
  repairmark(d->left);
  repairmark(d->right);
}

/* Redo depth-first numbering of bdd. */
void renumber(register bdd_ptr d,
              register int* pcount)
{
  if(TESTMARK(d))return;
  SETMARK(d);
   /*  SETID(d, (*pcount)++);*/
  (*pcount)++;
  if (ISLEAF(d)) return;
  renumber(d->left,  pcount);
  renumber(d->right, pcount);
}

/* Return number of nodes in bdd. */
int size_bdd(register bdd_ptr d)
{
   int dsize = 0;
   renumber(d, &dsize);
   repairmark(d);
   return(dsize);
}


/* Returns the level of this variable in the global bdd.
   Assumes the set_variable_names() has been executed. */
int var_level(node_ptr v)
{
  int i;
  for(i=0 ; i < top_level ; i++) if(variable_names[i] == v) return(i);
  return(-1); /* The var was not found */
}



/* Redo depth-first marking of bdd. */
/* This routine is called to mark all
   nodes in a BDD to protect them from garbage
   collection */
void mark_bdd(register bdd_ptr d)
{
  if(!d)catastrophe("mark_bdd: d == 0");
  if(TESTMARK(d))return;
  SETMARK(d);
  if(!ISLEAF(d)){
    mark_bdd(d->left);
    mark_bdd(d->right);
  }
}


/* Apply a function f to two bdd's */
bdd_ptr apply_bdd(node_ptr (*f)(node_ptr la, node_ptr lb),
                  bdd_ptr a, bdd_ptr b)
{
  int alevel,blevel;
  bdd_ptr temp1;
  if(ISLEAF(a) && ISLEAF(b))return leaf_bdd(f(leaf_value(a),leaf_value(b)));

  /* Search for apply in the cache. If it exists return the result from
     cache */
  if(temp1=find_apply((int)f,a,b))return(temp1);

  /*                                      */
  /* Apply the operation to the two bdd's */
  /*                                      */
  alevel=GETLEVEL(a);
  blevel=GETLEVEL(b);
  if(alevel==blevel)
    temp1=find_bdd(alevel,apply_bdd(f,a->left,b->left),
		   apply_bdd(f,a->right,b->right));
  else if(alevel<blevel)
    temp1=find_bdd(alevel,apply_bdd(f,a->left,b),apply_bdd(f,a->right,b));
  else temp1=find_bdd(blevel,apply_bdd(f,a,b->left),apply_bdd(f,a,b->right));

  /* Insert operation and result into the apply cache */
  insert_apply((int)f,a,b,temp1);

  /* Return result */
  return(temp1);
}

#define ELSE_LEAF ((node_ptr) -1)
bdd_ptr if_then_bdd(bdd_ptr a, bdd_ptr b)
{
  int alevel,blevel;
  bdd_ptr temp1;
  if(a==ZERO)return(leaf_bdd(ELSE_LEAF));
  if(a==ONE)return(b);
  if(ISLEAF(a))type_error(leaf_value(a));

  if(temp1=find_apply((int)if_then_bdd,a,b))return(temp1);

  alevel=GETLEVEL(a);
  blevel=GETLEVEL(b);
  if(alevel==blevel)
    temp1=find_bdd(alevel,if_then_bdd(a->left,b->left),
		   if_then_bdd(a->right,b->right));
  else if(alevel<blevel)
    temp1=find_bdd(alevel,if_then_bdd(a->left,b),if_then_bdd(a->right,b));
  else temp1=find_bdd(blevel,if_then_bdd(a,b->left),if_then_bdd(a,b->right));

  insert_apply((int)if_then_bdd,a,b,temp1);

  return(temp1);
}


bdd_ptr else_bdd(bdd_ptr a, bdd_ptr b)
{
  int alevel,blevel;
  bdd_ptr temp1;
  if(ISLEAF(a)){
    if(leaf_value(a) != ELSE_LEAF)return(a);
    else return(b);
  }
  if(temp1=find_apply((int)else_bdd,a,b))return(temp1);
  alevel=GETLEVEL(a);
  blevel=GETLEVEL(b);
  if(alevel==blevel)
    temp1=find_bdd(alevel,else_bdd(a->left,b->left),
		   else_bdd(a->right,b->right));
  else if(alevel<blevel)
    temp1=find_bdd(alevel,else_bdd(a->left,b),else_bdd(a->right,b));
  else temp1=find_bdd(blevel,else_bdd(a,b->left),else_bdd(a,b->right));
  insert_apply((int)else_bdd,a,b,temp1);
  return(temp1);
}

bdd_ptr if_then_else_bdd(bdd_ptr a,bdd_ptr b, bdd_ptr c)
{
  return(else_bdd(if_then_bdd(a,b),c));
}


/* The first bdd is the default assignment
  "the default", and the second is the assignment */
bdd_ptr default_in_bdd_aux(bdd_ptr a, bdd_ptr b,
                       int from_same_level)
{
  int alevel,blevel;
  bdd_ptr temp1;

  /* If b==ZERO then we have reached a point which does not
     represent an assignment. so return ZERO */
  if (b==ZERO) return ZERO;

  /* If b==ONE then we have reached a point which is a valid
     assignment. Even if a is ZERO, b overrides it, so we 
     return 1. Otherwise we just return a, the rest of the default. */
  if (b==ONE)
    if (a == ZERO) 
       return ONE;
    else 
       return a;

  /* If a==ONE then all the default has already been included
     to the results by the recursive callers of this function.
     All that is left is to return what remains from the assignment
     b *which is not a leaf, since we already checked that before. */
  if (a == ONE) return b;

  /* If a==ZERO it means that we have reached a point which is
     not consistent with the default, so intuitively, we want
     to return ZERO. 

     I am not sure about the following : ?????
     However, the question is whether we have 
     been overriden by b. 

     If "from_same_level" is true then the father of a has
     been overridden by b. */
  /*    if (a == ZERO && !from_same_level) return ZERO;*/

     if (a == ZERO) return ZERO; 




  if(ISLEAF(b))type_error(leaf_value(b));

  if(temp1=find_apply((int)default_in_bdd_aux,a,b))return(temp1);

  alevel=GETLEVEL(a);
  blevel=GETLEVEL(b);

  if(alevel==blevel) {
    /* b has the upper hand. a doesn't matter*/
    bdd_ptr a_or = or_bdd(a->left, a->right);
    temp1=find_bdd(alevel,default_in_bdd_aux(a_or,b->left, 1),
     		          default_in_bdd_aux(a_or,b->right, 1));
  }

  /* If levels are different, just follow either the default, or 
     assignment, and include their information in the result. */

  else if(alevel<blevel)
    temp1=find_bdd(alevel,default_in_bdd_aux(a->left,b,0),default_in_bdd_aux(a->right,b,0));
  else 
    temp1=find_bdd(blevel,default_in_bdd_aux(a,b->left,0),default_in_bdd_aux(a,b->right,0));

  insert_apply((int)default_in_bdd_aux,a,b,temp1);

  return(temp1);
}


/* Returns b, with default values from a.
   The idea is that b adds assignments to a.
   If b and a contradict, then b overrides a.
   The assignments in a are considered, the default
   value.  This is used to implement the "default .. in "
   construct. 
 */
bdd_ptr default_in_bdd(bdd_ptr a, bdd_ptr b)
{
  return default_in_bdd_aux(a,b,0);
}


/***************************************************************************\
*function: r_shift_brute					      	    *
*									    *
* Just get a bdd with all levels increased by 1.
\***************************************************************************/
bdd_ptr r_shift_brute(bdd_ptr a)
{
  int alevel;
  bdd_ptr temp1;
  if(ISLEAF(a))return(a);
  if(temp1=find_apply((int)r_shift_brute,a,0))return(temp1);
  alevel = GETLEVEL(a);

  temp1 = find_bdd(alevel + 1,
		     r_shift_brute(a->left),r_shift_brute(a->right));

  insert_apply((int)r_shift_brute,a,0,temp1);

  return(temp1);
}


/**********************************************************************
  This function takes b, which may include illegal encodings of
  variables, and elimininate illegal edges such that all encodings
  are legal. Illegal encodings can occur when the range of a variable
  is not a power of two. In this case, some variables are encoded 
  without using the last bdd level allocated for the variable.
  In some cases, this last bit manages to creap in, this is an
  illegal encoding which we actually we want to get rid of it.

  The limit_to function takes a bdd, b, and a limit bdd limit.
  The limit bdd is a bdd which represents V' = V for all program
  variables. This representation only includes legal encodings.
  The function throws away bits which  make the encoding illegal.

  The advanteg of using V' = V for limiting the set of values is
  that we do not have to deal with symbol tables and finding
  out the name of the varialbe, and its encoding according to 
  the level of the bdd. The price we pay is that it is a little
  cumbersome to work with V' = V. Actually, we only care about
  the values of V.
 **********************************************************************/

bdd_ptr limit_to_aux(bdd_ptr b, bdd_ptr limit_unprimed, bdd_ptr limit_primed) {
                                    
  if (ISLEAF(b)) 
      return b;
  else 
  {
      int blevel=GETLEVEL(b);
      bdd_ptr limit = IS_CURRENT_VAR(blevel) ? limit_unprimed :
                                               limit_primed;
      int limit_level=  GETLEVEL(limit);

      /* Advance limit until we reach blevel. */

      while (limit_level < blevel) {
        /* Advance limit to be primed or unprimed according to b. */
        do {
            limit = limit->left == ZERO ? limit->right : limit->left;
            limit_level = GETLEVEL(limit);
        } while ( ! ISLEAF(limit) && 
                  ( IS_CURRENT_VAR(blevel) ? !IS_CURRENT_VAR(limit_level):
                    IS_CURRENT_VAR(limit_level)) );
      }

      if (blevel == limit_level) 

        /* Traverse b and the limit together. */
        if (IS_CURRENT_VAR(blevel))
            return find_bdd(blevel,
                     limit_to_aux(b->left, limit->left, limit_primed),
                     limit_to_aux(b->right, limit->right, limit_primed));
        else
            return find_bdd(blevel,
                     limit_to_aux(b->left, limit_unprimed, limit->left),
                     limit_to_aux(b->right, limit_unprimed, limit->right));
		   
      
      else {
        bdd_ptr or_b = or_bdd(b->left, b->right);
          /* blevel < limit_level, so there is no corresponding 
             bit in the limit, so we throw the bit away. */
        if (IS_CURRENT_VAR(blevel))
            return limit_to_aux(or_b, limit, limit_primed);
        else
            return limit_to_aux(or_b, limit_unprimed, limit);
      }
  }
}
 
bdd_ptr limit_to(bdd_ptr b, bdd_ptr limit) {
  return limit_to_aux(b,limit,r_shift_brute(limit));
}

/*********************************************************************/

/* The first parameter is a satisfying path, the second
   is a bdd of all the values a specific variable can get */
bdd_ptr old_my_if_then_bdd(bdd_ptr a,bdd_ptr b)
{
  int alevel,blevel;
  bdd_ptr temp1;
  if(a==ZERO)return(leaf_bdd(ELSE_LEAF));
  if(a==ONE)
   {
    if ( ISLEAF(b) )  
      return(b);
    else
      return(leaf_bdd(ELSE_LEAF));
    }
  if(ISLEAF(a))type_error(leaf_value(a));

  if(temp1=find_apply((int)old_my_if_then_bdd,a,b))return(temp1);

  alevel=GETLEVEL(a);
  blevel=GETLEVEL(b);
  if(alevel==blevel)
    temp1=find_bdd(alevel,old_my_if_then_bdd(a->left,b->left),
		   old_my_if_then_bdd(a->right,b->right));
  else if(alevel<blevel)
   {
    temp1=old_my_if_then_bdd(a->left,b);
    if (temp1 == leaf_bdd(ELSE_LEAF))
      temp1 = old_my_if_then_bdd(a->right,b);
    }
  else temp1=leaf_bdd(ELSE_LEAF);

  insert_apply((int)old_my_if_then_bdd,a,b,temp1);

  return(temp1);
}



/* The first parameter is a satisfying path, the second
   is a bdd of all the values a specific variable can get */

bdd_ptr my_if_then_bdd_aux(bdd_ptr a, bdd_ptr b, int commited)
{
  int alevel,blevel;
  bdd_ptr temp1;
  if(a==ZERO)return(leaf_bdd(ELSE_LEAF));
  if(a==ONE)
   {
    if ( commited )  
      return(b);
    else
      return(leaf_bdd(ELSE_LEAF)); 
    }
  if(ISLEAF(a))type_error(leaf_value(a));


  alevel=GETLEVEL(a);
  blevel=GETLEVEL(b);
  if(alevel==blevel)
   {
    commited = 1;
    temp1=find_bdd(alevel,my_if_then_bdd_aux(a->left,b->left,commited),
		   my_if_then_bdd_aux(a->right,b->right,commited));
    }
  else if(alevel<blevel)
   {
    temp1=my_if_then_bdd_aux(a->left,b,commited);
    if (temp1 == leaf_bdd(ELSE_LEAF))
      temp1 = my_if_then_bdd_aux(a->right,b,commited);
    }
  else 
    if (ISLEAF(b))
      if (commited)
        temp1 = b;
      else
        temp1 = leaf_bdd(ELSE_LEAF);
    else
      temp1=find_bdd(blevel,my_if_then_bdd_aux(a,b->left,commited),
                            my_if_then_bdd_aux(a,b->right,commited));

  return(temp1);
}


/* The first parameter is a satisfying path, the second
   is a bdd of all the values a specific variable can get */
bdd_ptr my_if_then_bdd(bdd_ptr a, bdd_ptr b)
{
  return(my_if_then_bdd_aux(a,b,0));
}




/***************************************************************************\
*function: swapwords							    *
*									    *
*swaps words pointed to by args						    *
\***************************************************************************/
static swapwords(bdd_ptr *a,bdd_ptr *b)
{
  bdd_ptr temp= *a;
  *a= *b;
  *b=temp;
}


/***************************************************************************\
*function: and_bdd							    *
*									    *
*and two bdds								    *
\***************************************************************************/
bdd_ptr and_bdd(bdd_ptr a, bdd_ptr b)
{
  int alevel,blevel;
  bdd_ptr temp1;
  /* anything AND false is false */
  if(a==ZERO || b==ZERO)return(ZERO);
  /* anything AND true is itself */
  if(a==ONE)return(b);
  if(b==ONE)return(a);
  /* AND is commutative, so if address of a >
     address of b, swap the two. This increases
     chance of hit in the apply cache */
  if(ISLEAF(a))type_error(leaf_value(a));
  if(ISLEAF(b))type_error(leaf_value(b));
  if(a==b)return(a);
  if(((int)a)>((int)b))swapwords(&a,&b);

  /* Check to see if we've solved this problem before */
  if(temp1=find_apply(AND_OP,a,b))return(temp1);

  /* if not, get the level fields of a and b */
  alevel=GETLEVEL(a);
  blevel=GETLEVEL(b);
  /* now break the AND problems into two subproblems */
  /* if levels are the same, do AND(a->left,b->left), AND(a->right,b->right) */
  if(alevel==blevel)
    temp1=find_bdd(alevel,and_bdd(a->left,b->left),and_bdd(a->right,b->right));
  /* else if level of a is lower, split on value of a's variable */
  else if(alevel<blevel)
    temp1=find_bdd(alevel,and_bdd(a->left,b),and_bdd(a->right,b));
  /* else (level of b is lower), split on value of b's variable */
  else temp1=find_bdd(blevel,and_bdd(a,b->left),and_bdd(a,b->right));

  /* now put result in apply cache */
  insert_apply(AND_OP,a,b,temp1);
  return(temp1);
}



/* Utility function which does a = a & b, which releasing b. */
void and_it_in(bdd_ptr *a,bdd_ptr b)
{
  release_bdd(*a); release_bdd(b);
  *a = save_bdd(and_bdd(*a,b));
  mygarbage();
}



/***************************************************************************\
*function: fast_and_bdd							    *
*									    *
*and two bdds, but once a satisfying assignment to the result has been found*
*then stop.     							    *
* It is like doing sat_bdd(and_bdd(a,b))                                    *
\***************************************************************************/
bdd_ptr fast_and_bdd(bdd_ptr a,bdd_ptr b)
{
  int alevel,blevel;
  bdd_ptr temp1;
  /* anything AND false is false */
  if(a==ZERO || b==ZERO)return(ZERO);
  /* anything AND true is itself */
  if(a==ONE) return(b);
  if(b==ONE) return(a);

  if(ISLEAF(a))type_error(leaf_value(a));
  if(ISLEAF(b))type_error(leaf_value(b));
  if(a==b)return(a);

  if(((int)a)>((int)b))swapwords(&a,&b);

  /* Check to see if we've solved this problem before */
  if(temp1=find_apply(FAST_AND_OP,a,b))return(temp1);

  /* if not, get the level fields of a and b */
  alevel=GETLEVEL(a);
  blevel=GETLEVEL(b);
  /* now break the AND problems into two subproblems */
  /* if levels are the same, do AND(a->left,b->left), AND(a->right,b->right) */
  if(alevel==blevel)
   {
    temp1 = fast_and_bdd(a->left,b->left) ;
    if ( temp1 != ZERO )
       temp1=find_bdd(alevel,temp1,ZERO);
    else
     {
       temp1 = fast_and_bdd(a->right,b->right) ;
       if ( temp1 != ZERO )
          temp1=find_bdd(alevel,ZERO,temp1);
     }
   }

  /* else if level of a is lower, split on value of a's variable */
  else if(alevel<blevel)
   {
    temp1= fast_and_bdd(a->left,b);
    if ( temp1 != ZERO )
       temp1=find_bdd(alevel,temp1,ZERO);
    else
     {
       temp1= fast_and_bdd(a->right,b);
       if (temp1 != ZERO )
          temp1=find_bdd(alevel,ZERO,temp1);
     }
   }

  /* else (level of b is lower), split on value of b's variable */
  else 
   {
    temp1=fast_and_bdd(a,b->left);
    if ( temp1 != ZERO )
       temp1=find_bdd(blevel,temp1,ZERO);
    else
     {
       temp1=fast_and_bdd(a,b->right);
       if (temp1 != ZERO)
         temp1=find_bdd(blevel,ZERO,temp1);
     }
   }

  /* now put result in apply cache */
  insert_apply(FAST_AND_OP,a,b,temp1);

  return(temp1);
}


/***************************************************************************\
*function: orbr								    *
*									    *
*or two bdds								    *
\***************************************************************************/
bdd_ptr or_bdd(bdd_ptr a,bdd_ptr b)
{
  int alevel,blevel;
  bdd_ptr temp1;
  if(a==ONE || b==ONE)return(ONE);
  if(a==ZERO)return(b);
  if(b==ZERO)return(a);
  if(ISLEAF(a))type_error(leaf_value(a));
  if(ISLEAF(b))type_error(leaf_value(b));
  if(a==b)return(a);
  if(((int)a)>((int)b))swapwords(&a,&b);
  if(temp1=find_apply(OR_OP,a,b))return(temp1);
  alevel=GETLEVEL(a);
  blevel=GETLEVEL(b);
  if(alevel==blevel)
    temp1=find_bdd(alevel,or_bdd(a->left,b->left),or_bdd(a->right,b->right));
  else if(alevel<blevel)
    temp1=find_bdd(alevel,or_bdd(a->left,b),or_bdd(a->right,b));
  else temp1=find_bdd(blevel,or_bdd(a,b->left),or_bdd(a,b->right));
  insert_apply(OR_OP,a,b,temp1);
  return(temp1);
}

/***************************************************************************\
*function: xorbr							    *
*									    *
*xor two bdds								    *
\***************************************************************************/
bdd_ptr xor_bdd(bdd_ptr a, bdd_ptr b)
{
  int alevel,blevel;
  bdd_ptr temp1;
  if(a==ONE && b==ONE)return(ZERO);
  if(a==ZERO)return(b);
  if(b==ZERO)return(a);
  if(a==b)return(ZERO);
  if(((int)a)>((int)b))swapwords(&a,&b);
  if(temp1=find_apply(XOR_OP,a,b))return(temp1);
  alevel=GETLEVEL(a);
  blevel=GETLEVEL(b);
  if(alevel==blevel){
    if(ISLEAF(a) && a!=ONE && a!=ZERO)type_error(leaf_value(a));
    if(ISLEAF(b) && b!=ONE && b!=ZERO)type_error(leaf_value(b));
    temp1=find_bdd(alevel,xor_bdd(a->left,b->left),xor_bdd(a->right,b->right));
  }
  else if(alevel<blevel){
    if(ISLEAF(a))type_error(leaf_value(a));
    temp1=find_bdd(alevel,xor_bdd(a->left,b),xor_bdd(a->right,b));
  }
  else{
    if(ISLEAF(b))type_error(leaf_value(b));
    temp1=find_bdd(blevel,xor_bdd(a,b->left),xor_bdd(a,b->right));
  }
  insert_apply(XOR_OP,a,b,temp1);
  return(temp1);
}

/***************************************************************************\
*function: notbr							    *
*									    *
* not a bdd 								    *
\***************************************************************************/
bdd_ptr not_bdd(bdd_ptr d)
{
  return(xor_bdd(ONE,d));
}


/***************************************************************************\
*function: simplify_assuming						    *
*									    *
*								    *
\***************************************************************************/
/* simplify_assuming computes a/b such that
   a-b <= a/b <= a
   trying to minimize the BDD size of the result.
   damn if I know how it works.
*/
#define DONTCARE ((bdd_ptr)(-1))
bdd_ptr simplify_assuming1(bdd_ptr a, bdd_ptr b)
{
  int alevel,blevel;
  bdd_ptr temp1,temp2;
  if(b==ZERO)return(DONTCARE);
  if(b==ONE || a==ONE || a==ZERO)return(a);
  if(ISLEAF(a))type_error(leaf_value(a));
  if(ISLEAF(b))type_error(leaf_value(b));
  if(a==b)return(a);
  if(temp1=find_apply(SIMP_OP,a,b))return(temp1);
  alevel=GETLEVEL(a);
  blevel=GETLEVEL(b);
  if(!(alevel>blevel)){
    if(alevel<blevel){
      temp1=simplify_assuming1(a->left,b);
      temp2=simplify_assuming1(a->right,b);
    }
    else{
      temp1=simplify_assuming1(a->left,b->left);
      temp2=simplify_assuming1(a->right,b->right);
    }
    if(temp1==DONTCARE)temp1=temp2;
    else if(temp2!=DONTCARE)temp1=find_bdd(alevel,temp1,temp2);
  }
  else
    return(simplify_assuming1(a,or_bdd(b->left,b->right)));
  insert_apply(SIMP_OP,a,b,temp1);
  return(temp1);
}

bdd_ptr simplify_assuming(bdd_ptr a, bdd_ptr b)
{
  bdd_ptr res = simplify_assuming1(a,b);
  if(res == DONTCARE)return(ZERO);
  return(res);
}




/*
   forsome_set_leaves(a,b) - this is like forsome but the leaves
   are not booleans. The leaves are sets. The operation on the leaves
   is that of set union.
 */

bdd_ptr forsome_set_leaves(bdd_ptr a, bdd_ptr b)
{
  if(a == ONE || ISLEAF(b)) return(b);
  if(a == ZERO)catastrophe("forsome_set_leaves: a == ZERO");
  {
    register bdd_ptr result = find_apply((int)forsome_set_leaves,a,b);
    if(result)return(result);
    {
      register int alevel = GETLEVEL(a);
      register int blevel = GETLEVEL(b);
      if(alevel < blevel)
	result = forsome_set_leaves(a->right,b);
      else if(alevel == blevel)
	result = union_bdd(forsome_set_leaves(a->right,b->left),
                           forsome_set_leaves(a->right,b->right));
      else 
	result = find_bdd(blevel,forsome_set_leaves(a,b->left),
                                 forsome_set_leaves(a,b->right));
    }
    insert_apply((int)forsome_set_leaves,a,b,result);
    return(result);
  }
}

/*
 * forsome(a,b)  
 * a represents a set of variables which are to be existentially
   quantified away from b. A set of variables is encoded as a bdd
   which only has non-zero nodes on right branches. So the set
   looks like a long stick which is tilted to the right.
   The levels of the nodes in this stick are the set of variables
   which are to be quantified away. 
 */

bdd_ptr forsome(bdd_ptr a, bdd_ptr b)
{
  if (a == ONE || b == ONE || b == ZERO) return b;
  if (a == ZERO)
    rpterr("Error in forsome: the set of variables is invalid (a == ZERO)");
  {
    register bdd_ptr result = find_apply(FORSOME_OP,a,b);
    if (result) return result;
    {
      register int alevel = GETLEVEL(a);
      register int blevel = GETLEVEL(b);
      if (alevel < blevel)
	result = forsome(a->right,b);
      else if (alevel == blevel)
	result =
          or_bdd(forsome(a->right, b->left), forsome(a->right, b->right));
      else 
	result = find_bdd(blevel, forsome(a, b->left), forsome(a, b->right));
    }
    insert_apply(FORSOME_OP, a, b, result);
    return result;
  }
}
      

/* Universal quantification.  */
bdd_ptr forall(bdd_ptr a, bdd_ptr b)
{
  if(a == ONE || b == ONE || b == ZERO)return(b);
  if(a == ZERO)
    rpterr("Error in forall: the set of variables is invalid (a == ZERO)");
  {
    register bdd_ptr result = find_apply((int)forall,a,b);
    if(result)return(result);
    {
      register int alevel = GETLEVEL(a);
      register int blevel = GETLEVEL(b);
      if(alevel < blevel)
	result = forall(a->right,b);
      else if(alevel == blevel)
	result = and_bdd(forall(a->right,b->left),forall(a->right,b->right));
      else 
	result = find_bdd(blevel,forall(a,b->left),forall(a,b->right));
    }
    insert_apply((int)forall,a,b,result);
    return(result);
  }
}
      
static bdd_ptr the_support;
static void support1(bdd_ptr d)
{
  if(TESTMARK(d))return;
  SETMARK(d);
  if(ISLEAF(d))return;
  support1(d->left); support1(d->right);
  the_support = and_bdd(the_support,find_bdd(GETLEVEL(d),ZERO,ONE));
  return;
}

/* Returns a bdd which encodes the set of varibles which appear
   in d.  */
bdd_ptr support_bdd(bdd_ptr d)
{
  the_support = ONE;
  support1(d);
  repairmark(d);
  return(the_support);
}


/* This routine accepts a bdd, and then returns a bdd
   which can be used to quatify with.  The returned
   bdd will quatify all variables which appeared in
   the input bdd. 

   THIS IS THE SAME AS "support_bdd"!!! so I erased this.

bdd_ptr quant(a)
bdd_ptr a;
{
  bdd_ptr b;

  if ( ISLEAF(a) ) return ONE;

  b = and_bdd(quant(a->left),quant(a->right));
  return and_bdd(find_bdd(GETLEVEL(a),ZERO,ONE),b);
}

*/



/***************************************************************************\
*function: count_bdd							    *
*									    *
*return as a float the number of states that satisfy a given bdd.           *
* assumes global nstates contains the total number of states                *
\***************************************************************************/


/* this routine returns the *fraction* of truth assignments
   satisfying the BDD d. If the BDD is TRUE, it returns 1.0.
   If the BDD is FALSE, it returns 0.0. Otherwise it returns
   0.5 * {fraction of assignments satisfying left branch} +
   0.5 * {fraction of assignments satisfying left branch}.
   This routine is used only for the user's amusement. */

static double auxcount_bdd(bdd_ptr d)
{
  union {float a; bdd_ptr b;} temp;     /* very dangerous!!! */
  if(d==ZERO)return(0.0);
  if(d==ONE)return(1.0);
  temp.b = find_apply(COUNT_OP,d,ZERO);
  if(temp.b)return(temp.a);
  temp.a = 0.5*auxcount_bdd(d->left)+0.5*auxcount_bdd(d->right);
  insert_apply(COUNT_OP,d,ZERO,temp.b);
  return(temp.a);
}

/* Return approximate number of states the bdd describes. */
double n_count_bdd(bdd_ptr d, int n)
{
  /*  double floor();
  double pow();*/
  if(sizeof(float) > sizeof(bdd_ptr))
    catastrophe("count_bdd: sizeof(float) > sizeof(bdd_ptr)");

  return(floor(pow(2.0,(double)n) * (double)auxcount_bdd(d)));
}

double count_bdd(bdd_ptr d)
{
  return(n_count_bdd(d,nstvars - NSTBASE));
}

/* these routines (save_bdd and release_bdd) are used to keep a
   linked list of the top level nodes of all BDD's that are
   still in use. If you have a BDD pointer which is still in
   use, and is not on this list, it may get garbage collected
   during certain operations (any routines which call mygarbage).
   Note that there may be several occurrences on the list of
   any given node. Save_bdd always adds one occurrence, and
   release_bdd always deletes one. Save_bdd returns its argument */

bdd_ptr save_bdd(bdd_ptr d)
{
  if (verbose > 3)
    fprintf(tlvstdout, "Saving bdd %p. save_bdd_list_length now %d\n", d,
            save_bdd_list_length + 1);
  save_bdd_list_length++;
  save_bdd_list = cons((node_ptr) d, save_bdd_list);
  return d;
}


static struct node *rbdd_rec(struct node *bddlist, bdd_ptr d)
{
  if (bddlist == NIL)
    catastrophe("release_bdd: not on list");
  if (bddlist->left.bddtype != d) {
    bddlist->right.nodetype = rbdd_rec(bddlist->right.nodetype, d);
    return bddlist;
  }
  else {
    struct node *temp = bddlist->right.nodetype;
    free_node(bddlist);
    return temp;
  }
}

void release_bdd(bdd_ptr d)
{
  if (verbose > 3)
    fprintf(tlvstdout, "Releasing bdd %p. save_bdd_list_length now %d\n", d,
            save_bdd_list_length - 1);

  save_bdd_list=rbdd_rec(save_bdd_list,d);
  save_bdd_list_length--;
}

/*static void oldmarkbddlist(struct node *bddlist)
{
  if(bddlist==NIL)return;
  mark_bdd(bddlist->left.bddtype);
  markbddlist(bddlist->right.nodetype);
}*/

static void markbddlist(struct node *bddlist)
{
  while (bddlist!=NIL) {
    mark_bdd(bddlist->left.bddtype);
    bddlist = bddlist->right.nodetype;
  }
}

void check_bdd(bdd_ptr d)
{
  node_ptr p = save_bdd_list;
  while(p){
    if(((bdd_ptr)car(p)) == d)return;
    p = cdr(p);
  }
  catastrophe("check_bdd: failed");
}

void pr_status(void)
{
#ifdef REORDER
  fprintf(tlvstdout,"nodes allocated: %d\n",reduce_table.elements_in_table);
#else
  fprintf(tlvstdout,"nodes allocated: %d\n",allocatecount-disposecount);
#endif
}

/* Set variable order according to variable list. */
void set_order(node_ptr vars)
{
  flush_apply();
  markbddlist(save_bdd_list);
  sweep_reduce();

  /* Set order according to variable list. */
  reorder_variables(BY_VARS, vars);

  maxnodes=(reduce_table.elements_in_table)*2;
  if(maxnodes < gc_threshold)maxnodes = gc_threshold;
  if(verbose)pr_status();
}

/* Force garbage collection. */
void force_garbage(void)
{
  flush_apply();
  markbddlist(save_bdd_list);
  sweep_reduce();

#ifdef REORDER
  if (reorder && reduce_table.elements_in_table > reorder_size)
    reorder_variables(DYNAMIC_REORDER, NIL);
  maxnodes =(reduce_table.elements_in_table) * 2;
#else
  maxnodes = (allocatecount - disposecount) * 2;
#endif

  if (maxnodes < gc_threshold) maxnodes = gc_threshold;
  if (verbose) pr_status();
}

static int bdd_nodes_allocated;

static int max_bdd_nodes_allocated;

/* Helps compute the maximum amount of bdd nodes allocaed. */
void register_bdd_nodes_allocated(int n)
{
  bdd_nodes_allocated = n;

  if (n > max_bdd_nodes_allocated)
    max_bdd_nodes_allocated = n;
}

/* Get number of bdd nodes allocated. I am not sure this
   is accurate.  */
int get_bdd_nodes_allocated()
{
#ifdef REORDER
  if(reduce_table.elements_in_table > bdd_nodes_allocated)
      register_bdd_nodes_allocated(reduce_table.elements_in_table);
#else
  if(allocatecount-disposecount > bdd_nodes_allocated)
      register_bdd_nodes_allocated(allocatecount-disposecount);
#endif
  return(bdd_nodes_allocated);
}

/* Print statistics about bdd usage.  */
void print_bdd_usage(FILE *stream)
{
  fprintf(stream,"BDD nodes allocated: %d\n",get_bdd_nodes_allocated());
  fprintf(stream,"max amount of BDD nodes allocated: %d\n",max_bdd_nodes_allocated);
  fprintf(stream,"Bytes allocated: %d\n",get_bytes_allocated());
}

/* Print the save list, with sizes. This is good for debugging tlv
   to see if there are unreleased bdds.  */
void print_save_list_sizes(FILE *stream)
{
  int nbdd = 0;

  /* Print size of all bdd's on save list. */

  node_ptr l;
  for (l= save_bdd_list; l; l = cdr(l)) {
    fprintf(stream, "%d ", size_bdd(l->left.bddtype));
    nbdd++;
  }

  fprintf(stream, "\nTotal number of bdds in save list: %d\n", nbdd);
}

/* Garbage collection routine which is called by user.  */
void mygarbage(void)
{
#ifdef REORDER
  if (((reduce_table.elements_in_table) >= maxnodes) || reorder &&
      reduce_table.elements_in_table > max(5 * last_reorder_size / 4,
                                           reorder_size)) {
    if (reduce_table.elements_in_table > bdd_nodes_allocated)
      register_bdd_nodes_allocated(reduce_table.elements_in_table);
    force_garbage();
  }
#else
  if ((allocatecount - disposecount) >= maxnodes) {
    if (allocatecount - disposecount > bdd_nodes_allocated)
      register_bdd_nodes_allocated(allocatecount - disposecount);
    force_garbage();
  }
#endif
}

void mygarbage_ensure_flush_apply(void)
{
  if ((allocatecount-disposecount) >= maxnodes) {
    if (allocatecount-disposecount > bdd_nodes_allocated)
      register_bdd_nodes_allocated(allocatecount-disposecount);
    force_garbage();
  }
  else
    flush_apply();
}

/* Erase all bdd nodes */
void restart_bdd(void)
{
  save_bdd_list = NIL;
  save_bdd(ZERO);
  save_bdd(ONE);
  force_garbage();
}

bdd_ptr r_collapse_save(bdd_ptr a, bdd_ptr b)
{
  bdd_ptr r = r_collapse(a, b);
  save_apply(NEXT_OP, a, b);
  return(r);
}

/* removal suggested by ken mcmillan */
/* #define OR_BEFORE_RECURSE */
/***************************************************************************\
*function: r_collapse							    *
*									    *
* collapse a bdd in reverse						    *
* This applies transition a to state b and returns a bdd of the next state  *
* but with current variables.                                               *
*                                                                           *
*   r_collapse = prev(\exists V : a(V,V') & b(V))
*
* This is actually "Succ_P"
\***************************************************************************/
bdd_ptr r_collapse(bdd_ptr a, bdd_ptr b)
{
  int alevel,blevel;
  bdd_ptr temp1;
  if(a==ZERO || b==ZERO)return(ZERO);
  if(a==ONE)return(ONE);
  alevel=GETLEVEL(a);
  blevel=GETLEVEL(b);

  /* Check if this operation has already been done, if yes return result */
  if(temp1=find_apply(NEXT_OP,a,b))return(temp1);

  if(alevel<blevel){
    if(IS_CURRENT_VAR(alevel)) temp1=
#ifndef OR_BEFORE_RECURSE
      or_bdd(r_collapse(a->left,b),r_collapse(a->right,b));
#else
      r_collapse(or_bdd(a->left,a->right),b);
#endif
    else temp1=find_bdd(NEXT_TO_CURRENT(alevel),
			r_collapse(a->left,b),r_collapse(a->right,b));
  }
  else if(alevel==blevel){
    if(IS_CURRENT_VAR(alevel))temp1=
      or_bdd(r_collapse(a->left,b->left),r_collapse(a->right,b->right));
    else 
      rpterr("Error in succ : the second argument contains primed variables\n"
             "(r_collapse) !IS_CURRENT_VAR(blevel)");
  }
  else {
    if(IS_CURRENT_VAR(blevel))temp1=
#ifndef OR_BEFORE_RECURSE
      or_bdd(r_collapse(a,b->left),r_collapse(a,b->right));
#else
      r_collapse(a,or_bdd(b->left,b->right));
#endif
    else
      rpterr("Error in succ : the second argument contains primed variables\n"
             "(r_collapse) !IS_CURRENT_VAR(blevel)");
  }
  insert_apply(NEXT_OP,a,b,temp1);
  return(temp1);
}

/***************************************************************************\
*function: r_shift							    *
*									    *
* shift a bdd from current vars to next vars				    *
\***************************************************************************/
bdd_ptr r_shift(bdd_ptr a)
{
  int alevel;
  bdd_ptr temp1;
  if(ISLEAF(a))return(a);
  if(temp1=find_apply((int)r_shift,a,0))return(temp1);
  alevel = GETLEVEL(a);
  if(IS_CURRENT_VAR(alevel)){
    temp1 = find_bdd(CURRENT_TO_NEXT(alevel),
		     r_shift(a->left),r_shift(a->right));
    insert_apply((int)r_shift,a,0,temp1);
    return(temp1);
  }
  else
    rpterr("Error in prime/next: found primed variable");
}


/***************************************************************************\
*function: r_shift_bounded							    *
*									    *
* shift a bdd from current vars to next vars				    *
\***************************************************************************/
bdd_ptr r_shift_bounded(bdd_ptr a, int bound)
{
  int alevel;
  bdd_ptr temp1;
  if(ISLEAF(a))return(a);

  /* DONT LOOK in apply cache since the shifted bdds
     are very small */
  /*  if(temp1=find_apply(r_shift_bounded,a,0))return(temp1);*/

  alevel = GETLEVEL(a);
  if (alevel>bound)
    return a;    
  else if(IS_CURRENT_VAR(alevel)){
    temp1 = find_bdd(CURRENT_TO_NEXT(alevel),
		     r_shift_bounded(a->left,bound),
                     r_shift_bounded(a->right,bound));
    /*    insert_apply(r_shift_bounded,a,0,temp1);*/
    return(temp1);
  }
  else
    catastrophe("r_shift_bounded: !IS_CURRENT_VAR(alevel)");
}


/***************************************************************************\
*function: f_shift							    *
*									    *
* shift a bdd from current next to current vars				    *
\***************************************************************************/
bdd_ptr f_shift(bdd_ptr a)
{
  int alevel;
  bdd_ptr temp1;
  if(ISLEAF(a))return(a);
  if(temp1=find_apply((int)f_shift,a,0))return(temp1);
  alevel = GETLEVEL(a);
  if(!IS_CURRENT_VAR(alevel)){
    temp1 = find_bdd(NEXT_TO_CURRENT(alevel),
		     f_shift(a->left),f_shift(a->right));
    insert_apply((int)f_shift,a,0,temp1);
    return(temp1);
  }
  else
    rpterr("Error in unprime: found unprimed variable");
}


/***************************************************************************\
*function: collapse							    *
*									    *
* collapse a bdd, elimating all odd level forks (next)			    *

* collapse = \Exists V' : a(V,V') & b(V')
\***************************************************************************/
bdd_ptr collapse(bdd_ptr a,bdd_ptr b)
{
  int alevel,blevel;
  bdd_ptr temp1;
  if(a==ZERO || b==ZERO)return(ZERO);
  if(a==ONE)return(ONE);
  alevel=GETLEVEL(a);
  blevel=(GETLEVEL(b));

  /* b is AUTOMATICALLY shifted to next variables. */
  if(IS_CURRENT_VAR(blevel))blevel=CURRENT_TO_NEXT(blevel);

  /* Check if this operation has already been done, if yes return result */
  if(temp1=find_apply(PREV_OP,a,b))return(temp1);

  if(alevel<blevel){
    if(IS_NEXT_VAR(alevel)) temp1=
#ifndef OR_BEFORE_RECURSE
      or_bdd(collapse(a->left,b),collapse(a->right,b));
#else
      /* This line is executed */
      collapse(or_bdd(a->left,a->right),b);
#endif
    else temp1=find_bdd(alevel,collapse(a->left,b),collapse(a->right,b));
  }

  else if(alevel==blevel){
    if(IS_NEXT_VAR(alevel))temp1=
      or_bdd(collapse(a->left,b->left),collapse(a->right,b->right));
    else 
      catastrophe("Error in pred : The second argument contains unprimed variables\n"
             "collapse: !IS_NEXT_VAR(blevel)");
  }

    /* alevel > blevel */
  else { 
    if(IS_NEXT_VAR(blevel))temp1=
#ifndef OR_BEFORE_RECURSE
      or_bdd(collapse(a,b->left),collapse(a,b->right));
#else
      collapse(a,or_bdd(b->left,b->right));
#endif
    else
      catastrophe("Error in pred : The second argument contains unprimed variables\n"
             "collapse: !IS_NEXT_VAR(blevel)");
  }

  /* Insert operation and result in apply hash */
  insert_apply(PREV_OP,a,b,temp1);

  return(temp1);
}

/***********************************************************************
     Like collapse, but b is not automatically converted to 
     primed varialbes. Instead, it is left as is and thus can
     contain both primed and unprimed variables and is interpreted
     in this manner. (the no_shift means that b is not shifted to 
     primed variables.
 
      collapse_no_shift = \Exists V' : a(V,V') & b(V,V') 
***********************************************************************/
bdd_ptr collapse_no_shift(bdd_ptr a,bdd_ptr b)
{
  int alevel,blevel;
  bdd_ptr temp1;
  if(a==ZERO || b==ZERO)return(ZERO);
  if(a==ONE && b == ONE)return(ONE);
  if(temp1=find_apply((int)collapse_no_shift,a,b))return(temp1);
  alevel=GETLEVEL(a);
  blevel=GETLEVEL(b);
  if(alevel<blevel){
    if(IS_NEXT_VAR(alevel)) temp1=
      collapse_no_shift(or_bdd(a->left,a->right),b);
    else temp1=find_bdd(alevel,
			collapse_no_shift(a->left,b),
			collapse_no_shift(a->right,b));
  }
  else if(alevel==blevel){
    if(IS_NEXT_VAR(alevel))temp1=
      or_bdd(collapse_no_shift(a->left,b->left),
	     collapse_no_shift(a->right,b->right));
    else temp1 = find_bdd(alevel,
			  collapse_no_shift(a->left,b->left),
			  collapse_no_shift(a->right,b->right));
  }
  else {
    if(IS_NEXT_VAR(blevel))temp1=
      collapse_no_shift(a,or_bdd(b->left,b->right));
    else temp1=find_bdd(blevel,
			collapse_no_shift(a,b->left),
			collapse_no_shift(a,b->right));
  }
  insert_apply((int)collapse_no_shift,a,b,temp1);
  return(temp1);
}

bdd_ptr collapse_vars(bdd_ptr a,bdd_ptr b,bdd_ptr v)
{
  int alevel,blevel,vlevel;
  bdd_ptr temp1;
  if(a==ZERO || b==ZERO)return(ZERO);
  if(a==ONE && b == ONE)return(ONE);
  if(temp1=find_apply((int)collapse_vars,a,b))return(temp1);
  alevel=GETLEVEL(a);
  blevel=GETLEVEL(b);
  vlevel=GETLEVEL(v);
  while(vlevel < alevel && vlevel < blevel){
    v = v->right;
    vlevel=GETLEVEL(v);
  }
  if(alevel<blevel){
    if(alevel == vlevel) temp1=
      collapse_vars(or_bdd(a->left,a->right),b,v->right);
    else temp1=find_bdd(alevel,
			collapse_vars(a->left,b,v),
			collapse_vars(a->right,b,v));
  }
  else if(alevel==blevel){
    if(alevel == vlevel)temp1=
      or_bdd(collapse_vars(a->left,b->left,v->right),
	     collapse_vars(a->right,b->right,v->right));
    else temp1 = find_bdd(alevel,
			  collapse_vars(a->left,b->left,v),
			  collapse_vars(a->right,b->right,v));
  }
  else {
    if(blevel == vlevel)temp1=
      collapse_vars(a,or_bdd(b->left,b->right),v->right);
    else temp1=find_bdd(blevel,
			collapse_vars(a,b->left,v),
			collapse_vars(a,b->right,v));
  }
  insert_apply((int)collapse_vars,a,b,temp1);
  return(temp1);
}

/* Return value of bdd as an integer. This is done by searching
   a non-zero leaf and returning its integer value.  */
int value_bdd(bdd_ptr a)
{
  int temp;
  if(ISLEAF(a))return((int)(a->left));
  temp = value_bdd(a->left);
  if(temp == (int)ELSE_LEAF) temp = value_bdd(a->right);
  return(temp);
}

/* Same like value_bdd but returns node_ptr instead of int. */
node_ptr leaf_value_bdd(bdd_ptr a)
{
  node_ptr temp;
  if(ISLEAF(a))return((node_ptr)(a->left));
  temp = leaf_value_bdd(a->left);
  if(temp == (node_ptr)ELSE_LEAF || temp == zero_number ) temp = leaf_value_bdd(a->right);
  return(temp);
}

static void wl_bdd(void (*f)(node_ptr n),bdd_ptr d)
{
  if(TESTMARK(d)) return;
  SETMARK(d);
  if(ISLEAF(d))f((node_ptr)(d->left));
  else{
    wl_bdd(f,d->left);
    wl_bdd(f,d->right);
  }
}

/* Routine for walking over the leaves of a bdd, and performing
   some function f on each leaf.  */
void walk_leaves(void (*f)(node_ptr n),bdd_ptr d)
{
  wl_bdd(f,d);
  repairmark(d);
  return;
}

static int is_an_mtbdd;
  

static void bool_check(node_ptr n)
{
  if(n == NIL || n->type != NUMBER || 
     n->left.inttype > 1 || n->left.inttype < 0) 
    is_an_mtbdd = 1;
}


/* Check whether all leaves of bdd are boolean.  */
int is_mtbdd(bdd_ptr b)
{
  int is_an_mtbdd = 0;
  walk_leaves(bool_check,b); 

  return is_an_mtbdd;
}


static int aux_lowest_var_bdd(bdd_ptr d,int n)
{
  int i;
  if(TESTMARK(d) || ISLEAF(d))return(n);
  SETMARK(d);
  i = VAR_NUM(GETLEVEL(d));
  if(i > n)n = i;
  return(aux_lowest_var_bdd(d->right,aux_lowest_var_bdd(d->left,n)));
}

/* Return the number of the LARGEST variable number in bdd d.
   (It does not the level, but level/2). */
int lowest_var_bdd(bdd_ptr d)
{
  int res = aux_lowest_var_bdd(d,0);
  repairmark(d);
  return(res);
}

static bdd_ptr aux_make_var_mask(bdd_ptr d, int n, int l)
{
  if(l > n)return(ONE);
  if(ISLEAF(d))
    return(find_bdd(THE_CURRENT_VAR(l),aux_make_var_mask(d,n,l+1),ZERO));
  l = VAR_NUM(GETLEVEL(d));
  return(find_bdd(THE_CURRENT_VAR(l),
		  aux_make_var_mask(d->left,n,l+1),
		  aux_make_var_mask(d->right,n,l+1)));
}

int bits_encoding_var;
bdd_ptr make_var_mask(bdd_ptr d)
{
  int i = lowest_var_bdd(d);
  int j = ISLEAF(d)?1:VAR_NUM(GETLEVEL(d));
  bits_encoding_var = i - j + 1;
  return(aux_make_var_mask(d,i,j));
}

bdd_ptr varset_diff(bdd_ptr a, bdd_ptr b)
{
  if(a == ZERO || b == ZERO)catastrophe("varset_diff: a == ZERO || b == ZERO");
  if(a == ONE)return(a);
  if(GETLEVEL(a)<GETLEVEL(b))return(find_bdd(GETLEVEL(a),ZERO,varset_diff(a->right,b)));
  if(GETLEVEL(a)==GETLEVEL(b))return(varset_diff(a->right,b->right));
  return(varset_diff(a,b->right));
}

int check_bdd_order_aux(bdd_ptr d)
{
  if(TESTMARK(d))return(GETLEVEL(d));
  SETMARK(d);
  if(!ISLEAF(d)){
    int a = check_bdd_order_aux(d->left);
    int b = check_bdd_order_aux(d->right);
    if(GETLEVEL(d) >= a || GETLEVEL(d) >= b)catastrophe("bdd vars out of order");
  }
  return(GETLEVEL(d));
}

void check_bdd_order(bdd_ptr d)
{
  check_bdd_order_aux(d);
  repairmark(d);
}

void check_bdd_free_list(void)
{
  rec_ptr l = (bdd_mgr->free.link);

  while(l){
    rec_ptr m;
    if(l->link)m = l->link->link;
    l = l->link;
  }
}

/* Trims bdd from above to the level n */
bdd_ptr bdd_trim_to_level(bdd_ptr d, int n)
{
  int level=GETLEVEL(d);
  if(ISLEAF(d) || level >= n)return(d);
  if(d->left != ZERO) return(bdd_trim_to_level(d->left,n));
  else return(bdd_trim_to_level(d->right,n));
}


/* v is a bdd which represents a set of variables V.
   This function returns a bdd which represnts the expression V = V'.
   It is assumed that v does not have any prime variables. */
bdd_ptr id_of(bdd_ptr v) 
{
  int level=GETLEVEL(v);
  bdd_ptr temp, temp1;

  if(ISLEAF(v)) return(v);

  /* Get id of rest of the set. */
  temp = id_of(v->right);

  /* Connect id of current level with id of rest of set. */
  temp1 = find_bdd(level, 
                   find_bdd(CURRENT_TO_NEXT(level),
                            temp,ZERO),
                   find_bdd(CURRENT_TO_NEXT(level),
                            ZERO,temp)
                  );

  return temp1;
}


bdd_ptr replace_leaves_generic(bdd_ptr a,
                               node_ptr (*f)(node_ptr n))
{
  if ( ISLEAF(a) )
    return leaf_bdd(f((node_ptr)a->left));
  else
    return find_bdd(GETLEVEL(a),
                    replace_leaves_generic(a->left,f),
                    replace_leaves_generic(a->right,f));
}


bdd_ptr replace_leaves(bdd_ptr a,
                       node_ptr from, node_ptr to)
{
  if ( ISLEAF(a) )
    {
      while (from) {
        if (((node_ptr)a->left) == car(from))
          return leaf_bdd(car(to));

        from = cdr(from);
        to = cdr(to);
      }
      return a;
    }
  else
    return find_bdd(GETLEVEL(a),
                    replace_leaves(a->left,from,to),
                    replace_leaves(a->right,from,to));
}

/**********************************************************************
  Numeric operations on bdds.
**********************************************************************/

bdd_ptr equal_bdd(bdd_ptr a, bdd_ptr b)
{
  return(apply_bdd(equal_node,a,b));
}

bdd_ptr plus_bdd(bdd_ptr a, bdd_ptr b)
{
  return(apply_bdd(plus_node,a,b));
}

bdd_ptr minus_bdd(bdd_ptr a, bdd_ptr b)
{
  return(apply_bdd(minus_node,a,b));
}

/* Define * numeric operation on bdd's */
bdd_ptr times_bdd(bdd_ptr a, bdd_ptr b)
{
  return(apply_bdd(times_node,a,b));
}

/* Define / numeric operation on bdd's */
bdd_ptr divide_bdd(bdd_ptr a, bdd_ptr b)
{
  return(apply_bdd(divide_node,a,b));
}

/* Define mod numeric operation on bdd's */
bdd_ptr mod_bdd(bdd_ptr a, bdd_ptr b)
{
  return(apply_bdd(mod_node,a,b));
}

bdd_ptr union_bdd(bdd_ptr a, bdd_ptr b)
{
  return(apply_bdd(union_node,a,b));
}

bdd_ptr setin_bdd(bdd_ptr a, bdd_ptr b)
{
  return(apply_bdd(setin_node,a,b));
}

bdd_ptr lt_bdd(bdd_ptr a, bdd_ptr b)
{
  return(apply_bdd(lt_node,a,b));
}

bdd_ptr gt_bdd(bdd_ptr a, bdd_ptr b)
{
  return(apply_bdd(gt_node,a,b));
}


node_ptr new_BDD_node(bdd_ptr b)
{
  return new_node(BDD,(node_ptr) b, NIL);
}
node_ptr find_BDD_node(bdd_ptr b)
{
  return find_node(BDD,(node_ptr) b, NIL);
}


#include "bdd_sat.c"
#include "bdd_print.c"
