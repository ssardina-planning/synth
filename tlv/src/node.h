
#ifndef NODEHDEF
#define NODEHDEF 1
#include <stdio.h>
/***********************************************************************
 This file defines the node structure and operators.
 It is made to simulate lisp lists where each list has a head and a tail.
 If a node is a list then the head data is in the left leaf ( car )
 and the tail is in the right leaf ( cdr ) which might also be a list.

 Many internal functions of node.c are not used by any other file.

 Here are the provided functions:


  I) Basic functions:

     1) node_ptr new_node(int type,node_ptr left,node_ptr right)

            Create a node of two sons with type "type".

     2) node_ptr find_node(int type,node_ptr left,node_ptr right);

            Returns pointer to a cononical node of such a record
            in the hash table.
            If the node doesn't already exist in the hash table
            then it is inserted.

     2.1) node_ptr find_atom(node_ptr a);

            Takes a node (usually an atom, but can be others) which
            may have been created using the new_node function, and
            returns a pointer to a cannonical node which contains the
            same data. (uses find_node.

            For example, the function is used in grammar.y to
            cannonize atoms.

     2.2) node_ptr string_to_atom(char *s);

            Returns cannonical atom which corresponds to the string.

     3) void init_node()

            This routine initializes this file. It is called from main.c .
            It creates the hash structure for the nodes, and an
            association hash strucuture.

     4) void free_node(node_ptr a)

            Free space allocated for the node.

     5) void print_node(FILE *stream,node_ptr n);
        int print_node_atcol(FILE *stream, node_ptr n, int col);

            Print node n to stream.
            The second call prints the node at a column "col" and 
            returns the column where the print ended.

     6) node_ptr subst_node(node_ptr n)

       **** Usage unknown ****

     7) node_ptr map(node_ptr (*f)(node_ptr),
                     node_ptr l)

            f is a transformation function from node_ptr to node_ptr .
            l is a node_ptr ( which is actually a list ).

            The map function executes f on all items of the list l.

     8) node_ptr key_node(node_ptr n);

       **** Usage unknown ****

  II) Lisp like functions:

     9) node_ptr cons(node_ptr x, node_ptr y)

            Concatenate two nodes into a list
            ( The pointer to the list is returned).

     10) node_ptr car(node_ptr)

             Return left son. ( logically the head of a list )

     11) node_ptr cdr(node_ptr)

             Return right son. ( logically the tail of a list 
                                 (which is also a list) )

     12) node_ptr append(node_ptr x, node_ptr y)

             Append y to the rightmost leave of the tree whose root is x.

     13) node_ptr reverse(node_ptr x)

             Reverse the order of x.

             Example:


                a                      c
               / \                    / \
              e   b       ====>      g   b
                 / \                    / \
                f   c                  f   a
                   /                      / 
                  g                      e


     14) node_ptr unify_node(node_ptr n1,n2,sl);

       **** Usage unknown ****        


 Each node has a "type" field which can be one of the following :

  name in y.tab.h    meaning
  ---------------    -------
  TRUEEXP            TRUE
  FALSEEXP           FALSE
  ATOM               string
  NUMBER             integer
  DOT 
  LIST
  ARRAY              array element n[m] , n is in car and m in cdr
  TWODOTS 
  IMPLIES            ->
  IFF                <->
  OR                 |
  AND                & 
  NOT                !
  EX                 EX
  AX                 AX
  EF                 EF
  AF                 AF
  EG                 EG
  AG                 AG
  EU
  AU
  EBU
  ABU
  EBF
  ABF
  EBG
  ABG
  EQUAL              =
  LT                 <
  GT                 >
  LE                 <=
  GE                 >=
  UNION              union
  SETIN              in
  MOD                mod
  PLUS               +
  MINUS              -
  TIMES              *
  DEVIDE             /
  NEXT
 ***********************************************************************/


/* Define a unionized value type which can be one of int,node,str,bdd */
typedef union {
  int inttype;
  struct node *nodetype;
  struct string *strtype;
  struct bdd *bddtype;
  void *voidtype;
} value;

/* Define node */
typedef struct node {
  struct node *link;      /* Link for storage in hash table. */
  unsigned short int type   : 10 ;
  unsigned short int fileno : 6 ;
  unsigned short int lineno;  /* The type of the node and the line number. */
  value left,right;       /* Each node has left and right values */
} node_rec,*node_ptr;


/**********************************************************************/
/* Constants                                                          */
/**********************************************************************/

#define NIL ((node_ptr)0)
#define FAILURE_NODE ((node_ptr)(-1))
#define TYPE_ERROR ((node_ptr)(-1))

/* Pointers to nodes which contain the numbers 0,1 */
extern node_ptr zero_number,one_number;

/* Pointer to node which is a list of the two previous node :
   zero_number and one_number.  Types in SMV are represented
   as lists of items, so this variable will contain the
   boolean type: a list of {0,1} */
extern node_ptr boolean_type;

/**********************************************************************/
/* Initialize package. Allocate and free nodes. */
/**********************************************************************/

void init_node(void);

node_ptr new_node (int type, node_ptr left, node_ptr right);
node_ptr find_node(int type, node_ptr left, node_ptr right);
void free_node(node_ptr n);
void free_list(node_ptr a);


/**********************************************************************/
/* Strings and atoms                                                  */
/**********************************************************************/

node_ptr new_string_node(int type,char *s,node_ptr right);

node_ptr find_atom(node_ptr a);

node_ptr string_to_atom(char *s);
char *atom_to_string(node_ptr a);

char *op_string(node_ptr n);
int number_of_operands(node_ptr n);


/**********************************************************************
   View nodes as integers and do operations on
   them by converting from node to integer and then back to nodes 
**********************************************************************/

node_ptr new_NUMBER_node (int num);
node_ptr find_NUMBER_node (int num);
#define is_NUMBER_node(n) (n->type == NUMBER)
#define number_of(n) (n->left.inttype)

node_ptr numeric_op(int (*op)(int a, int b),
                    node_ptr n1, node_ptr n2);

node_ptr equal_node(node_ptr n1, node_ptr n2); /* Check that nodes are equal */
node_ptr plus_node(node_ptr n1, node_ptr n2);
node_ptr minus_node(node_ptr n1, node_ptr n2);
node_ptr times_node(node_ptr n1, node_ptr n2);
node_ptr divide_node(node_ptr n1, node_ptr n2);
node_ptr mod_node(node_ptr n1, node_ptr n2);
node_ptr lt_node(node_ptr n1, node_ptr n2);    /* Numeric "<" */
node_ptr gt_node(node_ptr n1, node_ptr n2);    /* Numeric ">" */


/**********************************************************************
/* List operations */
/**********************************************************************/

node_ptr cons(node_ptr x, node_ptr y);
node_ptr car(node_ptr n);
node_ptr cdr(node_ptr n);

#define caar(n) car(car(n))
#define cdar(n) cdr(car(n))
#define cadr(n) car(cdr(n))
#define cddr(n) cdr(cdr(n))
#define caaar(n) car(car(car(n)))
#define cdaar(n) cdr(car(car(n)))
#define cadar(n) cdr(cdr(car(n)))
#define cddar(n) cdr(cdr(car(n)))

node_ptr append(node_ptr x, node_ptr y);
node_ptr reverse(node_ptr n);
node_ptr last(node_ptr n);

node_ptr odd_elements(node_ptr l);
node_ptr even_elements(node_ptr l);

int in_list(node_ptr n, node_ptr r); /* Check if item n is in list r */
int length(node_ptr n); int list_length(node_ptr n);

/* Remove members of l1 which are in the second parameter.
   l2 is a list, and member is a single member.  
   list_minus preserves the arguments, wheras list_minus_one
   modifies l1. */
node_ptr list_minus(node_ptr l1, node_ptr l2);
node_ptr list_minus_one(node_ptr l1, node_ptr member);

node_ptr map(node_ptr (*f)(node_ptr n), node_ptr l);
void walk(void (*f)(node_ptr n),node_ptr l);


/* Stack operations */
void     push_node (node_ptr *stack, node_ptr n);
node_ptr top_node  (node_ptr *stack);
node_ptr pop_node  (node_ptr *stack);
int      empty     (node_ptr stack);


/* Set operations. */
node_ptr union_node(node_ptr n1, node_ptr n2); /* Union of lists */
int setin(node_ptr n1, node_ptr n2);           /* Returns 1 if n1 is in list n2 */
node_ptr setin_node(node_ptr n1, node_ptr n2); /* Returns the "1" node if n1 is in list n2 */
node_ptr set_minus_node(node_ptr l1, node_ptr l2); /* Return list of elements in l1 that are 
                                                      not in l2. */

/**********************************************************************/
/* Printing nodes                                                     */
/**********************************************************************/

void add_to_indent(int i);
void indent_node(FILE *stream,
                 char *s1,node_ptr n,char *s2);
void print_node(FILE *stream, node_ptr n);
int sprint_node(char *str, int size, node_ptr n);

void fprint_node(FILE *ff, node_ptr n);
void print_node_stdout(node_ptr n);


/* Sort operations */

/* Merge two sorted lists. */
node_ptr merge_node(node_ptr n1, node_ptr n2);

/* Sort list. */
node_ptr sort_node(node_ptr n);

/* Assuming n1, n2, return an item in their intersection. */
node_ptr intersect_node(node_ptr n1, node_ptr n2);

/* Use - unknown. */
node_ptr subst_node(),key_node(),unify_node();


#endif
