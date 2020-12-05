#ifndef BDDHDEF
#define BDDHDEF 1

#include "node.h"
#include <stdio.h>

/***********************************************************************
 This file provides bdd structure and functions.


  I ) Basic functions on bdd nodes:

    1) void init_bdd();

       Initialize the BDD package. Called by main.c .
       This creates the keytable and the apply cache.
       Size of the keytable is given by global KEYTABLESIZE
       Size of the apply cache is given by global APPLY_CACHE_SIZE

    2) bdd_ptr find_bdd(int level, bdd_ptr d1, d2)

       find_bdd returns a BDD node whose left
       pointer is to d1, right pointer is to d2,
       and whose level is "level".
       if such a node already exists, a pointer
       to this node is returned, else a 
       new node is created. This routine is
       used to keep BDD's in reduced form.
       Note also, that if d1 == d2, this node
       is redundant, so we return d1.

    3) void mygarbage();

       Sweep bdds in reduce table. 
       Deletes any BDD nodes which do not have their
       mark field set. This is done by scanning the keytable structure
       which is called "reduce_table" in bdd.c .
       This is done to free memory .

  II) Functions on apply cache:

      The apply cache is used in order to avoid recalculating operations
      on bdd's.

    4) void save_apply(int op, bdd_ptr d1,d2)

       Mark entry in apply cache to be saved ( i.e. not deleted by
       garbage collection ) .

    5) void insert_apply(int op,bdd_ptr d1,d2,d);

       Insert an apply record into the apply cache 

    6) bdd_ptr find_apply(int op, bdd_ptr d1,d2);

       Find an apply record in the apply cache. If it is found then
       the result of the apply is returned.
       Else - Null is returned.

    7) void flush_apply();

       empty the apply cache of all entries except
       those with SAVE bit set. This is in preparation
       for garbage collection. Call mark_bdd on all
       results with SAVE bit set to protect them
       from garbage collection.

  III) Node markings and bdd renumbering.

       A node which is marked is not erased by garbage collection.

    8) void repairmark(bdd_ptr d);

       Repair (clear) mark field recursivly. 

    9) void renumber( bdd_ptr d,int* pcount);

       Redo depth-first numbering of bdd. 
       Each node in the tree gets a unique id starting with id "pcount".
       When calling renumber pcount should initially be zero.
       After execution of renumber "pcount" contains the id of the
       last node, so if we called "renumber" with pcount=0 then pcount
       will contain the number of nodes in the bdd.

    10)int size_bdd(bdd_ptr d);

       Return number of nodes in bdd graph starting from d.

    11)void mark_bdd(bdd_ptr d);

       Redo depth-first marking of bdd. 
       This routine is called to mark all
       nodes in a BDD to protect them from garbage collection 

  IV) Operations on bdd's.

      All the results of these operations enter the apply cache.
 
    12)bdd_ptr and_bdd(bdd_ptr a,b);

       void and_it_in(bdd_ptr *a,bdd_ptr b)  is a convenience 
       function which uses and_bdd. 
       It ands b into a, doing all the release_bdd's for you.
       After execution of and_it_in, b is released.


    13)bdd_ptr or_bdd(bdd_ptr a,b);
    14)bdd_ptr xor_bdd(bdd_ptr a,b);
    15)bdd_ptr not_bdd(bdd_ptr a);
    16)bdd_ptr forsome(bdd_ptr a,b)
       bdd_ptr forall(bdd_ptr a,b)



    17)bdd_ptr simplify_assuming(bdd_ptr a,b);
       simplify_assuming computes a/b such that a-b <= a/b <= a
       trying to minimize the BDD size of the result.

    19)bdd_ptr sat_bdd(bdd_ptr d);
       returns a bdd which is <= bdd d, but has at most one node at each level
       This function is used in finding counterexamples
       It is intended to produce one element of a set which is
       represented by the BDD d.


  V) Find fraction of satisfying assignments.
       static double auxcount_bdd(bdd_ptr d)

       Return approximate number of states the bdd describes
    20)double count_bdd(bdd_ptr d)
    21)double n_count_bdd(bdd_ptr d,int n)


  VI) Save bdd nodes from garbage collection.

     These routines (save_bdd and release_bdd) are used to keep a
     linked list of the top level nodes of all BDD's that are
     still in use. If you have a BDD pointer which is still in
     use, and is not on this list, it may get garbage collected
     during certain operations (any routines which call mygarbage).
     Note that there may be several occurrences on the list of
     any given node. Save_bdd always adds one occurrence, and
     release_bdd always deletes one. Save_bdd returns its argument 

    22)bdd_ptr save_bdd(bdd_ptr d);
    23)void release_bdd(bdd_ptr d);


  VII)

    24)bdd_ptr leaf_bdd()

       Take a node, and return a leaf bdd where the node is the leaf.

    25)bdd_ptr atomic_bdd(int n);

       returns bdd whose root is a CURRENT_VAR of n ( level = 2*n )
       and whose left and right sons are ZERO,ONE.
       This is a bdd of one variable. It is a bdd of the boolean
       function "x_n"

  VIII) Shift from current vars to next and back.

    26)bdd_ptr r_shift(bdd_ptr a)

       shift a bdd from current vars to next vars.

    27)bdd_ptr f_shift(bdd_ptr a)

       shift a bdd from next vars to current vars.

    28)bdd_ptr r_collapse()
    29)bdd_ptr collapse();

      bdd_ptr apply_bdd(int (*f)(),bdd_ptr a,b)
      bdd_ptr if_then_else_bdd();
      bdd_ptr if_then_bdd();
      bdd_ptr value_bdd();
      support_bdd

      void restart_bdd()

      Erase all bdd nodes 
 ***********************************************************************/


/* Structure of bdd record */
typedef struct bdd {
   unsigned dfield;      /* Field which contains id,level,mark */
   struct bdd *left, *right, *next;  /* Left,right sons of bdd. ( next is for
                                        the linked lists in bdd hash table */
} bdd_rec, *bdd_ptr;

#ifndef NULL
#define NULL 0
#endif

/* Exported constant bdd's - contain leafs of the '1' and '0' nodes. */
extern bdd_ptr ZERO,ONE;


/* The following two structures are only used internally in bdd.c */

/* Data structure for the key table                                */
/* This data stucture holds a hash table which contains all of the */
/* bdd records.                                                    */
typedef struct {
   int n;            /* Size of hash table ( prime close to KEYTABLE_SIZE */
   int elements_in_table;   /* Number of elements in all list of hash table*/
   bdd_ptr *hash_table_buf; /* Hash table of bdd records */
} keytable_rec, *keytable_ptr;

/* Data structure for apply record                                  */
/* This is used in order to define a cache which contains various    */
/* applications of operations to bdd's with the results.            */
typedef struct {
  int op;             /* Operations */
  bdd_ptr arg1,arg2;  /* Bdd on which operations were performed */
  bdd_ptr res;        /* The result of the operation */
} apply_rec;



/* Bits packed in dfield (field of bdd_rec ) as follows:     */
/* 19:0  --- id    (0 to IDMASK : depth first id)            */
/* 30:20 --- level (0 to LEAFLEVEL)                          */
/* 31    --- mark  (TRUE or FALSE : used in graph traversal) */

/*#define IDMASK    0X000FFFFF
#define LEVELMASK 0X7FF00000
#define MARKMASK  0X80000000 
#define IDLOW    0
#define LEVELLOW 20 
#define LEAFLEVEL 2047 */

#define LEVELMASK 0X7FFFFFFF
#define MARKMASK  0X80000000

#define LEVELLOW 0
#define MARKLOW  31

#define LEAFLEVEL LEVELMASK 
#define ISLEAF(d) (GETLEVEL(d) == LEAFLEVEL)


/* Generic macro for getting field from packed dfield of bpp_ptr */
#define GETFIELD(var, mask, low) ((int) ((var & mask) >> low))
#define PUTFIELD(var, val, mask, low) \
        (var = (var & ~(mask)) | (((unsigned) val) << low))

/* Specific macros for getting/setting specific fields of dfield */
/* The parameter d is of type "bdd_ptr" in all following macros. */

/*#define GETID(d)        ((d)->dfield & IDMASK)
#define SETID(d, idval) (PUTFIELD((d)->dfield, idval, IDMASK, IDLOW))*/

#define GETLEVEL(d) (GETFIELD((d)->dfield, LEVELMASK, LEVELLOW))
#define SETLEVEL(d, lval) (PUTFIELD((d)->dfield, lval, LEVELMASK, LEVELLOW))

#define SETMARK(d)   ((d)->dfield |= MARKMASK)
#define CLEARMARK(d) ((d)->dfield &= ~MARKMASK)
#define TESTMARK(d)  (((d)->dfield & MARKMASK) != 0X0)


/* The following codes are used in the apply cache as one of the elements
   of the key by which the "application" ( on an operation to bdd's )
   is applied */
#define AND_OP 1
#define OR_OP 2
#define XOR_OP 3
#define FORSOME_OP 4
#define NEXT_OP 11         /* r_collapse */
#define PREV_OP 12         /* collapse */
#define COMP_OP 6          /* Not used */
#define SIMP_OP 7
#define COUNT_OP 8
#define ELIM_OP 9          /* Not used */
#define SATISFY_OP 10      /* Not used */
#define USE_BIG_CACHE 11   /* Used internally */
#define FAST_AND_OP 13


/**********************************************************************
  Initialize package
**********************************************************************/

void init_bdd(void);
void restart_bdd();


/**********************************************************************
  Creating bdds.
**********************************************************************/

/* Create a leaf bdd from a node_ptr, which will serve as the value of 
   the leaf. */
bdd_ptr leaf_bdd(node_ptr value);  

bdd_ptr atomic_bdd(int n);

bdd_ptr find_bdd(register int level, 
                 register bdd_ptr d1, register bdd_ptr d2);


/**********************************************************************
  Get leaf values from a bdd. 
**********************************************************************/

/* Get the node_ptr (the value) from a bdd which is a leaf bdd. */
node_ptr leaf_value(bdd_ptr b);    


/* Similar "leaf_value_bdd", but get the value as an integer.
   The bdd does not have to be a leaf bdd. The routine searches
   for a leaf. */
int value_bdd(bdd_ptr a);

/* Same like value_bdd but returns node_ptr instead of int.
   The difference from leaf_value is that the parameter of 
   this routine doesn't have to be a leaf. */
node_ptr leaf_value_bdd(bdd_ptr a);


/* Return true iff bdd has leaves which are not 0 or 1. */
int is_mtbdd(bdd_ptr b);


/**********************************************************************
  Apply operations
**********************************************************************/
bdd_ptr apply_bdd(node_ptr (*f)(node_ptr la, node_ptr lb),
                  bdd_ptr a, bdd_ptr b);
void save_apply();
void insert_apply(int op,
                  register bdd_ptr d1,register bdd_ptr d2,
                  register bdd_ptr d);
bdd_ptr find_apply(int op,
                   register bdd_ptr d1, register bdd_ptr d2);
void flush_apply(void);


/**********************************************************************
  Basic bdd operations 
**********************************************************************/
bdd_ptr and_bdd(bdd_ptr a, bdd_ptr b);
void and_it_in(bdd_ptr *a,bdd_ptr b);

/* Like sat_bdd(and_bdd(a,b)), but much faster. */
bdd_ptr fast_and_bdd(bdd_ptr a, bdd_ptr b);

bdd_ptr  or_bdd(bdd_ptr a, bdd_ptr b);
bdd_ptr xor_bdd(bdd_ptr a, bdd_ptr b);
bdd_ptr not_bdd(bdd_ptr d);

bdd_ptr forsome(bdd_ptr a, bdd_ptr b);
bdd_ptr  forall(bdd_ptr a, bdd_ptr b);

bdd_ptr r_shift(bdd_ptr a);
bdd_ptr r_shift_bounded(bdd_ptr a, int bound);
bdd_ptr f_shift(bdd_ptr a);

bdd_ptr r_collapse(bdd_ptr a,bdd_ptr b);
bdd_ptr collapse(bdd_ptr a,bdd_ptr b);

bdd_ptr if_then_else_bdd(bdd_ptr a,bdd_ptr b, bdd_ptr c);
bdd_ptr else_bdd(bdd_ptr a, bdd_ptr b);
bdd_ptr if_then_bdd(bdd_ptr a,bdd_ptr b);

bdd_ptr my_if_then_bdd(bdd_ptr a, bdd_ptr b); /* New functions I added */

bdd_ptr default_in_bdd(bdd_ptr default_bdd, bdd_ptr b);

bdd_ptr support_bdd(bdd_ptr d);

/* v is a bdd which represents a set of variables V.
   This function returns a bdd which represnts the expression V = V'.
   It is assumed that v does not have any prime variables. */
bdd_ptr id_of(bdd_ptr v);


bdd_ptr simplify_assuming(bdd_ptr a, bdd_ptr b);


void walk_leaves(void (*f)(node_ptr n),bdd_ptr d);


/**********************************************************************
 Satisfiability routines.
 **********************************************************************/

/* Return ONE state on which the bdd "d" holds.
   In the "rand" procedure, the state is chosen at random. */
bdd_ptr sat_bdd(bdd_ptr d);
bdd_ptr rand_original_sat_bdd(bdd_ptr d);

/* Do satisfy while trying to fill all levels which appear in set "var_set" */
bdd_ptr sat_bdd_from_set(bdd_ptr d,bdd_ptr var_set);

bdd_ptr rand_sat_bdd(bdd_ptr d);

/* Returns a single path in a bdd. This is almost
   like sat (which also returns a single path), but it does not
   introduce a bdd node at every level. Although this bdd 
   is still likely to represent a set of states rather than a 
   single state, it is more "user friendly" then the regular
   sat_bdd. For example, it is easier to use when printing out counter
   examples. */
bdd_ptr sparse_sat_bdd(bdd_ptr n);  

/* Very strange routine. Returns the smallest bdd such that
   each leaf in "n" is reachable by only one path in the returned
   bdd. The rest of the paths are linked to "rejecting". */
bdd_ptr multisat(bdd_ptr n,int rejecting);


bdd_ptr sat_bdd_from_state_space(bdd_ptr d, bdd_ptr ss);

/**********************************************************************
  Statistics about bdds.
**********************************************************************/

int size_bdd(register bdd_ptr d);
double count_bdd(bdd_ptr d);
double n_count_bdd(bdd_ptr d, int n);

void print_bdd_usage(FILE *stream);
void print_save_list_sizes(FILE *stream);


/**********************************************************************
  Mark bdds. This is used mostly internally, by other routines.
**********************************************************************/
void repairmark();
void mark_bdd(bdd_ptr b);

/**********************************************************************
  Memory management: garbage collection
**********************************************************************/

bdd_ptr save_bdd(bdd_ptr d);
void release_bdd(bdd_ptr d);
void mygarbage(void);
void force_garbage(void);

/* val = {0,1}. If val = 1 then during variable reordering the
   process of the algorithm will be printed out. */
void set_bdd_verbose(int val);


/**********************************************************************
  Information about bdd levels. Translate levels to variable numbers.
**********************************************************************/

/* The input parameter for all the following macros is a level number */
/* Each level corresponds to a variable.                              */
/* The least significant bit of a level indicates if the variable is  */
/* NEXT or CURRENT.                                                   */
#define IS_CURRENT_VAR(s) (((s)&1)==0)
#define IS_NEXT_VAR(s) (((s)&1)==1)

/* ( s<<1  double s by 2)  */
#define THE_CURRENT_VAR(s) (((s)<<1))
#define THE_NEXT_VAR(s) (((s)<<1)+1)

#define VAR_NUM(s) ((s)>>1)
#define NEXT_TO_CURRENT(s) ((s)-1)
#define CURRENT_TO_NEXT(s) ((s)+1)


/* MISC */

bdd_ptr forsome_set_leaves(bdd_ptr a, bdd_ptr b);

bdd_ptr replace_leaves(bdd_ptr a,
                       node_ptr from, node_ptr to);
bdd_ptr replace_leaves_by_partition();
bdd_ptr replace_leaves_generic(/* bdd_ptr a,
                                  node_ptr (*f)(node_ptr b)*/);

bdd_ptr bdd_trim_to_level(bdd_ptr d, int n);

/* Returns the level of this variable in the global bdd.
   Assumes the set_variable_names() has been executed. */
int var_level(node_ptr v);

void set_var_names(void);


bdd_ptr limit_to(bdd_ptr b, bdd_ptr limit);

/***********************************************************************
 Print bdds in various ways.
***********************************************************************/

void print_bdd(bdd_ptr a, int col);

/* This routine prints a bdd as a boolean formula. */
void print_bdd_by_shannon(bdd_ptr b);

/* This routine prints a bdd as a cnf boolean formula. */
void print_bdd2cnf(bdd_ptr b);

/* Takes a list of bdd's which represents the formula F : b1 & b2 & ... & bk 
   and print the cnf of the negation of F. */
void print_bdd2cnf2(node_ptr bdd_list);

/* This routine resets sharing of variables names of formulas
printed by print_bdd_by_shannon and print_bdd2cnf */
void reset_sharing(void);


/***********************************************************************
  Dump bdds to files in "dotty" format 
***********************************************************************/

#define NO_REJECT -1

/* Used from tlvt. Print bdd with "Q" leaves. */
void graph_nodes_bdd(FILE *stream,
                     bdd_ptr a,
                     char* prefix,
                     char* connect_to,
                     char **name_table,
                     int reject);

/* Dump a "stand-alone" bdd graph. (used from tlv) */
void new_graph_bdd(char* fname,bdd_ptr a);

/* dump bdd's as part of other data structures. Used from tlvp*/
void graph_bdd(char* fname,bdd_ptr a);
void subgraph_bdd(FILE *stream,
                  bdd_ptr a,
                  char* prefix,
                  char* connect_to,
                  char* label);

/* Used from tlvt and tlvp */
void sym_subgraph_bdd(FILE *stream,
                      bdd_ptr a,
                      char* prefix,
                      char* connect_to,
                      char* label,
                      char **name_table);

/***********************************************************************
 Operations on bdd using apply. When an operation is done on bdds it 
  is actually applied to all the corresponding nodes in the leaves of 
  the two bdds. 
***********************************************************************/
bdd_ptr  equal_bdd(bdd_ptr a, bdd_ptr b);
bdd_ptr   plus_bdd(bdd_ptr a, bdd_ptr b);
bdd_ptr  minus_bdd(bdd_ptr a, bdd_ptr b);
bdd_ptr  times_bdd(bdd_ptr a, bdd_ptr b);
bdd_ptr divide_bdd(bdd_ptr a, bdd_ptr b);
bdd_ptr    mod_bdd(bdd_ptr a, bdd_ptr b);
bdd_ptr  union_bdd(bdd_ptr a, bdd_ptr b);
bdd_ptr  setin_bdd(bdd_ptr a, bdd_ptr b);
bdd_ptr     lt_bdd(bdd_ptr a, bdd_ptr b);
bdd_ptr     gt_bdd(bdd_ptr a, bdd_ptr b);

/***********************************************************************
  Allocate node_ptr nodes with bdd's in the car and NIL in cdr. 
***********************************************************************/
node_ptr new_BDD_node(bdd_ptr b);
node_ptr find_BDD_node(bdd_ptr b);

/**********************************************************************
  Output order of variables to file.
**********************************************************************/
void set_output_order_file(char *fname);
void output_order();

#endif

