/* This file has functions which perform various evaluations, on various
   types of expressions or terms. */

#include <stdio.h>
#include <storage.h>
#include <mystring.h>
#include <node.h>
#include <node_smv.h>
#include <hash.h>
#include <bdd.h>
#include <assoc.h>
#include <util_err.h>
#include <y.tab.h>
#include "symbols.h"
#include "instantiate.h"

#include "eval.h"

/* Buffers for printing arguments of STRING_EQ. */
#define BUFSIZE 1000
char buf1[BUFSIZE];
char buf2[BUFSIZE];


/* A flag which is 1 if DEFINE symbols are saved in
   the cache value_hash once they are evaluated. */
int cache_defined_values = 1;

/* Used for caching evaluations. */
static hash_ptr value_hash;


/* Global variable which is used inside eval_aux. It is used
   to determine which kind of assignments should be evaluated:
   next(x) :=  , x := , init(x) := */
static int assign_type;
static int assign_type_F;

/* If is 1, force DEFINE values to be constant ( not variables ) */
static int enforce_constant = 0;

#define EVALUATING_NODE ((node_ptr)(-1))

extern int verbose;



#define GOODSTATUS 1
#define BADSTATUS 0

static int next_mode = 0;

/**********************************************************************/

/* Evaluate an expression "e" to an integer number. The expression
   can contain constants, names of constants defined in the DEFINE section,
   and any numeric operations which act on numbers. */
int eval_num_status(node_ptr e,node_ptr context, int *status)
{
  node_ptr n;
  bdd_ptr d;
  int temp = enforce_constant;

  /* Force evaluation into a constant. */
  /*  enforce_constant = 1;  */

  /* Evaluate to a bdd.  */
  d = eval(e, context
           );

  enforce_constant = temp;
  release_bdd(d);

  /* A number must be a leaf bdd. */
  if (ISLEAF(d)) {
    /* Extract leaf content from bdd. */
    n = (node_ptr) (d->left);

    /* Check it is indeed a number. */
    if (n->type == NUMBER) {
      *status = GOODSTATUS;
      return n->left.inttype; /* Return number. */
    }
  }
  *status = BADSTATUS;
  return 0;
}


int eval_num(node_ptr e,node_ptr context)
{ 
  int status;
  int result = eval_num_status(e,context,&status);

  if( status == BADSTATUS ) {
     print_node(tlvstderr, e);
     rpterr("Error: numeric constant required");
  }
  else
    return result;
}

/**********************************************************************/

/* Routines used by get definition. They use value_hash as a cache,
   and to remember variables which are in the middle of evaluation.
   This is used to detect circular definitions. 
 */


/* Called when we are evaluating a new symbol.
   The symbol is registered in the value hash, to note
   that it is in the process of evaluation. */
void push_eval_stack(node_ptr n)
{
  insert_assoc(value_hash,n,EVALUATING_NODE);

  /* For error printouts. */
  push_atom(n);
}

void remove_from_value_hash(node_ptr n)
{
   node_ptr val = find_assoc(value_hash,n);

   if (val)
     remove_assoc(value_hash,n,val);
}


/* Undo push_eval_stack. */
void pop_eval_stack(node_ptr n)
{
  node_ptr val;

  pop_atom();

  if ( val = find_assoc(value_hash,n))
    if ( val == EVALUATING_NODE )
      remove_assoc(value_hash,n,val);
}

/* Needed in case of error. Clear all cached defined values which 
   are pushed on stack. */
void clear_eval_stack()
{
  next_mode = 0;

  while (!empty_atom_stack())
    {
      node_ptr n = pop_atom();
      remove_from_value_hash(n);
    }
}


/* Clear the value cache, which caches evaluations of symbols
   which are defined in the DEFINE section, or symbols which
   are defined using Let 'x := */
void clear_value_hash(void)
{
  clear_hash(value_hash);
}

/**********************************************************************/

/*
  This routine is the only place where value_hash is used.
  This routine returns the bdd of a variable definition.
  The node "n" is a term ( atom, array or dot ).
  The value_hash is used to calculate the value of the
  bdd ( it helps to avoid circularity in the computation ),
  but it also serves as a cache for these values.
  A DEFINED_SYMBOL is s symbol which is defined in the DEFINE
  section in an smv file. The values of these are cached
  by inserting the calculated bdd into the symbol table using
  updated_bdd. PARSE_TREE_SYMBOL are dynamic variables which
  are defined in tlvbasic using the "Let 'k := ..." syntax.
  These are cached in the value_hash, so that we can erase
  all cached variables at once if we need to. To appreciate
  the problem better, consider the following example:

  Let 'd1 := 2;
  Let 'd2 := d1 + d1;
  Print d2;

  Let 'd1 := 3;

  Print d2;

  What are the printed value?  I want the first value to be 4
  and the second to be 6. Also note, that in evaluating d2,
  I don't want to evalute d1 twice. One time should be enough. 
  If d1 has been evaluated before, then the evaluation of d2
  shouldn't evaluate d1 even once. The value of d1 should be
  cached somehow. However, d2 will also be cached once it is 
  printed. If this is the case then the second printout will
  also print 4, since the evaluation in d2 was cached the first
  time it was printed.

  The problem is the second assignment to d1. Actually, this
  should be quite rare. We assume that dynamic assignments
  are not done to variables which are done in the DEFINE
  section (although it is possible now, perhaps it should
  produce an error).

  Anyway, my compramise solution is to cache values of
  PARSE_TREE_SYMBOLs using the value_hash. When an assignment
  is done into an already existing parse tree variable, the
  value_hash is cleared, so that in the case above, the
  second printout will evaluate d1 and d2 again.
*/
bdd_ptr get_definition(node_ptr n)
{
  /* Get value of symbol */
  node_ptr val = get_symbol(n);

  node_ptr res_node;
  bdd_ptr res;

  /* Handle error cases. */

  if (!val) return (bdd_ptr) 0;

  if (enforce_constant && symbol_type(val) == PROGRAM_VAR_SYMBOL) {
    enforce_constant = 0;
    print_node(tlvstderr, n);
    rpterr("Error: constant required");
  }

  /* If the symbol has a bdd, then return it (this is
     typical for dynamic variables with bdd value, or of program
     variables). */
  if (has_bdd(val)) {
    res = bdd_of(val);
    if (next_mode)
      res = r_shift(res);
    return save_bdd(res);
  }

  /* Try to retrieve value from cache. */
  res_node = find_assoc(value_hash, n);

  /* If we are in the middle of evaluting this symbol, then
     the symbol is circularly defined. */
  if (res_node == EVALUATING_NODE) circular(n);

  /* Try to extract bdd, from returned value cache. */
  res = (bdd_ptr) res_node;
  if (res) {
    if (next_mode)
      res = r_shift(res);
    return save_bdd(res);
  }

  if (verbose > 1) {
    add_to_indent(1);
    indent_node(tlvstderr, "evaluating ", n, ":\n");
  }

  /* If we have gotten to here, then the symbol is either
     defined in the DEFINE section, or it is a dynamic variable,
     which contains a parse tree. So we evaluated the parse
     tree recursively. */
  push_eval_stack(n);
  res = eval(parse_tree_of(val), NIL);
  pop_eval_stack(n);

  /* Store the result according to the type of the symbol. */
  if (!next_mode) {
    switch (symbol_type(val)) {
    case DEFINED_SYMBOL:
      /* If the symbol is defined in the DEFINE section, store
         the value in the symbol table. Note that in the past
         it was stored in the value cache. */
      update_bdd(val,save_bdd(res));
      break;
    case PARSE_TREE_SYMBOL:
      /* If the symbol is a dynamic variable, then store
         value in cache. */
      insert_assoc(value_hash,n,(node_ptr)save_bdd(res));
      if (verbose > 2)
        indent_node(tlvstderr, "get_definition: Caching parse tree ", n, "\n");
      break;
    default: fprintf(tlvstderr,
                     "Node is neither DEFINEd or a parse tree symbol!\n");
    }
  }
  if (verbose > 1) {
    indent_node(tlvstderr, "get_definition: size of ", n, " = ");
    fprintf(tlvstderr, "%d BDD nodes\n", size_bdd(res));
    add_to_indent(-1);
  }
  return res;
}


/* Gets bdd of node n, but if it does not exist, then raises an error. */
static bdd_ptr enforce_definition(node_ptr n)
{
/*   fprintf(tlvstdout, "enforcing definition "); */
/*   print_node(tlvstdout, n); fprintf(tlvstdout, "..\n"); */
  bdd_ptr res;
  if (res = get_definition(n)) return res;
  undefined(n);
}


/**********************************************************************/

/* The following are small routines which perform simple
   evalutations on bdd's . */


/* Return "a" (flag <> -1 ) or not "a" */
static bdd_ptr eval_sign(bdd_ptr a, int flag)
{
  switch(flag){
  case -1: return(not_bdd(a));
  default: return(a);
  }
}

/* Apply a unary operation "op", to the result of
   evaluating node n into a bdd. resflag and argflag are
   flags. If their value is -1 then the result of n is
   negated after applying op or before applying op, respectively. */
static bdd_ptr unary_op(bdd_ptr (*op)(bdd_ptr b), node_ptr n, int resflag,
                        int argflag, node_ptr context)
{
  bdd_ptr arg = eval(car(n), context);
  release_bdd(arg);
  return save_bdd(eval_sign(op(eval_sign(arg, argflag)), resflag));
}

/* Similar to unary_op, but for boolean operations. */
static bdd_ptr binary_op(bdd_ptr (*op)(bdd_ptr a, bdd_ptr b), node_ptr n,
                         int resflag, int argflag1, int argflag2,
                         node_ptr context)
{
  bdd_ptr arg1 = eval(car(n), context);
  bdd_ptr arg2 = eval(cdr(n), context);
  release_bdd(arg1);
  release_bdd(arg2);
  return
    save_bdd(eval_sign(op(eval_sign(arg1, argflag1),
                          eval_sign(arg2, argflag2)),
                       resflag));
}


static bdd_ptr eval_if_then_else(node_ptr ifexp,
                                 node_ptr thenexp, node_ptr elseexp,
                                 node_ptr context)
{
  bdd_ptr ifarg = eval(ifexp,context);
  bdd_ptr thenarg = eval(thenexp,context);
  bdd_ptr elsearg = eval(elseexp,context);
  release_bdd(ifarg);
  release_bdd(thenarg);
  release_bdd(elsearg);
  return save_bdd(if_then_else_bdd(ifarg, thenarg, elsearg));
}

/**********************************************************************/

/* "n" is a term which could be an atom or an array item, for example,
   proc.rec[3].state . This routine returns a *cannonical* represention
   of such a term. The two important operations which do this are:

   1) Replace formal parameters by actual arguments  (partially).
   2) Put the term in the correct context.  For example, a term
      rec[3].state in the context "proc" will be returned as a canonical
      term representing proc.rec[2].state .  */
node_ptr eval_struct_status(node_ptr n, node_ptr context, int *status);

static node_ptr eval_struct1_status(node_ptr n, node_ptr context, int *status)
{
  node_ptr temp,name;
  switch(n->type){
  case CONTEXT:
    /* This case is needed for evaluating actual parameters, which
       have a different context . */
    return eval_struct_status(cdr(n),car(n),status);

  case ATOM:
    name = find_node(DOT, context, find_atom(n));

    /* Check if this name is a formal parameter and if so evaluate
       the actual parameter. An infinite loop might occur if
       the parameter and its value are equivalent - this will
       happen since eval_struct is called recusively on the value
       of the parameter. Note that eval_aux only catches conflicts
       between ATOM and its parameter. In case of arrays or DOT,
       the only place we can catch such an infinite loop is here. */
    if (temp = get_value_of_by_name_param(name))
      if (find_atom(temp) != find_atom(n)) /* TRY TO AVOID INFINITE LOOPS.*/
        return eval_struct_status(temp, context, status);

    return name;

  case DOT:
    temp = eval_struct_status(car(n),context,status);
    if(temp == TYPE_ERROR)rpterr("type error, operator = .");
    return find_node(DOT,temp,find_atom(cdr(n)));

  case ARRAY: {
    int index;
    int car_status;
    node_ptr result;

    temp = eval_struct_status(car(n),context, &car_status);
    if (temp == TYPE_ERROR)rpterr("type error, operator = []");

    index = eval_num_status(cdr(n),context, status);

    if (*status == GOODSTATUS)
      result = find_node(ARRAY,temp, find_NUMBER_node(index));
    else
      result = find_node(ARRAY,temp, NIL);

    if (car_status == BADSTATUS)
      *status = BADSTATUS;

    return result;
  }
  case SELF:
    return context;
  default:
    return TYPE_ERROR;
  }
}


/* Evaluate a term and return the result.
   The main procedure it calls is eval_struct1

   The result is returned as follows
   input  output
   ----   ------
   ATOM   (DOT,context,ATOM)
   ARRAY  (ARRAY,term,NUMBER)
   DOT    (DOT,term,ATOM)   */
node_ptr eval_struct_status(node_ptr n, node_ptr context, int *status)
{
  node_ptr res;
  node_ptr temp = err_node;
  if (n == NIL) return NIL;
  err_node = n;

  *status = GOODSTATUS;
  res = eval_struct1_status(n, context, status);

  err_node = temp;
  return res;
}

/* Evaluate a term and return the result.
   The main procedure it calls is eval_struct1

   The result is returned as follows
   input  output
   ----   ------
   ATOM   (DOT,context,ATOM)
   ARRAY  (ARRAY,term,NUMBER)
   DOT    (DOT,term,ATOM)   */
node_ptr eval_struct(node_ptr n, node_ptr context)
{
  int status;
  node_ptr res = eval_struct_status(n, context, &status);

  if (status == BADSTATUS) {
    print_node(tlvstderr, n);
    rpterr("Error: term requires numeric constant");
  }

  return res;
}

/**********************************************************************/


int term_match(node_ptr term, node_ptr curr_var) 
{
  if (term == curr_var) return 1;
  if (term == NIL || curr_var == NIL) return 0;

  switch (term->type) {
  case ATOM: 
    /* If we reached here then the terms are not equal because
       we already asked above whether term == curr_var */
    return 0; 
  case ARRAY: {
    int match_car = term_match(car(term), car(curr_var));

    if ( !match_car ) 
      return 0;
    else if (cdr(term) == NIL) return 1;
    else 
        return cdr(term) == cdr(curr_var);
  }
  default: {
    int match_car = term_match(car(term), car(curr_var));
    int match_cdr = term_match(cdr(term), cdr(curr_var));
 
    return match_car && match_cdr;
    }
    
  }
}

/* Get a term which was returned from an eval_struct_status which 
   had indexes which were not constants, and return the sublist of
   variables (from list vars) which match that term. */
node_ptr get_matching_vars(node_ptr term, node_ptr vars)
{
  node_ptr result = NIL;
  node_ptr l;

  for (l = vars; l; l = cdr(l)) {
    node_ptr curr_var = car(l);
    /* If there is a match, add it to result list. */
    /*    print_node(stdout,curr_var);*/
    if ( term_match(term, curr_var) )
      result = result = find_node(LIST,curr_var, result);
  }
  return result;
}



/**********************************************************************/

/* These two structs keep information about the term.
   Actually, much more space is devoted to the indexes rather than
   the term itself. */

/* Information about a single (index) term used as an array index.
   For example, if we are talking about the term a[i+1][j+k],
   then that is entire term, and the index terms are i+1, j+k. 
   This struct keeps information about the index terms. */
typedef struct {
  bdd_ptr index;       /* The bdd evaluated from the term. */
  node_ptr subs;       /* A placeholder in the array term which is used
                          for obtaining a real variable name from the 
                          array term. */
  node_ptr value_list; /* The list of values this index term can obtain. */
  node_ptr curr_value; /* Used for looping over the value_list. */
} index_info;

typedef struct {
  node_ptr nc_term; /* Nearly canonical term. */

  int num_indexes;       /* Length of array: index */
  index_info index[100]; /* Information about the indexes. */

  int eof;
} term_info;

term_info *curr_term_i;

void add_value(node_ptr n)
{
  curr_term_i->index[curr_term_i->num_indexes].value_list =
    cons(n, curr_term_i->index[curr_term_i->num_indexes].value_list);
}

/* Return a node_ptr which can act as a key for substitution.
   We need such keys to mark places in a term which are intended
   to be substituted for some other term, later on. The key
   should be such that it doesn't appear anywhere else in the term. */
node_ptr subs_key(int i)
{
  char st[4];

  st[0] = '_';
  st[1] = '^';
  st[2] = '0' + i;
  st[3] = 0;

  return string_to_atom(st);
}

void add_index(bdd_ptr index, term_info *term, node_ptr subs)
{
  term->index[term->num_indexes].index = index;
  term->index[term->num_indexes].subs = subs;/*subs_key(term->num_indexes + 1);*/
  term->index[term->num_indexes].value_list = NIL;

  /* Generate value list. */
  curr_term_i = term;
  walk_leaves(add_value, index);

  term->num_indexes++;

  /*  return term->index[term->num_indexes - 1].subs;*/
}


/* This is similar to eval_struct, but it does not evaluate indexes as part
   of the struct. */
static node_ptr eval_term(node_ptr n, node_ptr context, term_info *term)
{
  node_ptr temp,name;

  if (n == NIL) return NIL;

  switch (n->type) {
  case CONTEXT:
    /* This case is needed for evaluating actual parametrs, which
       have a different context . */
    return eval_term(cdr(n), car(n), term);

  case ATOM:
    name = find_node(DOT, context, find_atom(n));

    /* Check if this name is a formal parameter and if so evaluate
       the actual parameter. An infinite loop might occur if
       the parameter and its value are equivalent - this will
       happen since eval_struct is called recusively on the value
       of the parameter. Note that eval_aux only catches conflicts
       between ATOM and its parameter. In case of arrays or DOT,
       the only place we can catch such an infinite loop is here. */
    if (temp = get_value_of_by_name_param(name)) {
      node_ptr find_temp = find_atom(temp);
      if (find_temp != find_atom(n) &&
          find_temp != name ) /* TRY TO AVOID INFINITE LOOPS.*/
        return eval_term(temp, context, term);
    }
    return name;
  case DOT: {
    node_ptr result;

    temp = eval_term(car(n),context, term);
    if (temp == TYPE_ERROR)
      rpterr("type error, operator = .");
    result = find_node(DOT, temp, find_atom(cdr(n)));

    /* Check again for formal parameters, so that from tlvbasic,
       it will be possible to refer to a formal parameter, and 
       get back the arguement. */
    if (temp = get_value_of_by_name_param(result))
      return eval_term(temp, context, term);
    else
      return result;
  }
  case ARRAY: {
    node_ptr substitution_key;
    int remember_next_mode = next_mode;

    node_ptr temp = eval_term(car(n), context, term);
    if (temp == TYPE_ERROR) rpterr("type error, operator = []");

    /* Evaluate index, but as current variable. */
    next_mode = 0;
    substitution_key = find_node(ARRAY,temp, NIL);
    add_index(eval(cdr(n), context), term, substitution_key);
    next_mode = remember_next_mode;

    return substitution_key;
  }
  case SELF:
    return context;
  default:
    return TYPE_ERROR;
  }
}

/*********/

void start_index_iteration(term_info *term)
{
  int i;

  /* Set all curr_value's to start of value_list. */
  for (i=0; i < term->num_indexes; i++)
    term->index[i].curr_value = term->index[i].value_list;

  term->eof = 0;
}

int endof_index_iteration(term_info *term)
{
  /* If there are no indexes then we are always at the end. */
  if (term->num_indexes == 0)
    return 1;
  else
    return term->eof;
}

void next_index_iteration(term_info *term)
{
  int i;

  /* Set all curr_value's to start of value_list. */
  for (i=0;
       i < term->num_indexes && cdr(term->index[i].curr_value) == NIL;
       i++)
    term->index[i].curr_value = term->index[i].value_list; /* Reset curr. */

  if (i < term->num_indexes)
    term->index[i].curr_value = cdr(term->index[i].curr_value);
  else
    /* If the index reached the end of the array, then this means
       that all of the curr_value's were at the last item of the list,
       so we have reached the end of the iteration. */
    term->eof = 1;
}

/********/

static hash_ptr subst_hash = 0 ;

void clear_substitution(void) 
{
  if ( ! subst_hash)
      subst_hash = new_assoc();

  clear_hash(subst_hash); 
}

void add_substitution(node_ptr from, node_ptr to)
{
  if (find_assoc(subst_hash,from)) {
    fprintf(stderr, "Multiple substitution for ");
    print_node(tlvstderr, from);
  }
  insert_assoc(subst_hash, from, to);
}

node_ptr substitute(node_ptr n)
{
  node_ptr m;

  if(n==NIL) return NIL;
  switch(n->type){
  case ARRAY:
    m = find_assoc(subst_hash,n);
    if(m)
        return find_node(ARRAY, substitute(n->left.nodetype), m);
    else 
        return n;

  case ATOM: return n;

  default:
    return(find_node(n->type,
		     substitute(n->left.nodetype),
		     substitute(n->right.nodetype)));
  }
}

node_ptr current_canonical_term(term_info *term)
{
  int i;

  clear_substitution();
  for (i=0; i < term->num_indexes; i++)
    add_substitution(term->index[i].subs, car(term->index[i].curr_value));

  return substitute(term->nc_term);
}

bdd_ptr current_cond(term_info *term)
{
  int i;
  bdd_ptr result = ONE;

  for (i=0; i < term->num_indexes; i++) {
    result = and_bdd(result,
                     equal_bdd(term->index[i].index,
                               leaf_bdd(car(term->index[i].curr_value))));
  }
  return save_bdd(result);
}


/* Get the symbol information about the term, even if this term
   is an array, with indexes which are program variables.
   The old code for this routine was simply:

   return get_symbol(eval_struct(t,context));
*/
node_ptr get_symbol_from_term(node_ptr t, node_ptr context)
{
  term_info term_i;
  node_ptr nc_term; /* Nearly canonical term */
  node_ptr result;

  /* Get a "nearly" canonical term, and a list of bdd's
     which should serve as indexes for the term.  If the term has
     no array references then the list of bdd's will be empty, and
     the term will really be canonical. Otherwise, the "nearly" canonical
     term should have NIL in places where the index should have been. */
  term_i.num_indexes = 0;
  nc_term = eval_term(t, context, &term_i);

  /* If the term has no array indexes, then no substitutions
     are needed, so evaluate it directly. */
  if (term_i.num_indexes == 0)
    result = get_symbol( nc_term );
  else {
    /* Otherwise, we need the symbol information about an item of the array.
       We assume that all of the items are of the same type, so it
       is OK just to find the first actual variable item, and get information
       about it. */
    term_i.nc_term = nc_term;

    start_index_iteration(&term_i);
    result = get_symbol(current_canonical_term(&term_i));
    int i;
    for (i = 0; i < term_i.num_indexes; i++)
      release_bdd(term_i.index[i].index);
  }
  return result;
}


/* This function is instead of doing
   enforce_definition(eval_struct(()). The difference is that this
   procedure also handles indexes of arrays. */
bdd_ptr eval_term_to_bdd(node_ptr n, node_ptr context)
{
  /* fprintf(tlvstdout, "eval_term_to_bdd..\n"); */

  term_info term_i;
  node_ptr nc_term; /* Nearly canonical term */
  bdd_ptr result, temp_result;
  node_ptr temp = err_node;

  /* Update line number in case of error, so that the error message will
     refer to the right line. */
  err_node = n;

  /* Get a "nearly" canonical term, and a list of bdd's
     which should serve as indexes for the term.  If the term has
     no array references then the list of bdd's will be empty, and
     the term will really be canonical. Otherwise, the "nearly" canonical
     term should have NIL in places where the index should have been. */
  term_i.num_indexes = 0;

  if (verbose > 2) {
    fprintf(tlvstdout, "eval_term_to_bdd: evaling term ");
    print_node(tlvstdout, n); fprintf(tlvstdout, "..\n");
  }

  nc_term = eval_term(n, context, &term_i);

  if (verbose > 2) {
    fprintf(tlvstdout, "eval_term_to_bdd: evaled term ");
    print_node(tlvstdout, n); fprintf(tlvstdout, "\n");
  }

  /* If the term has no array indexes, then no substitutions
     are needed, so evaluate it directly. */
  if (term_i.num_indexes == 0) {
    result = enforce_definition(nc_term);
     /*     if (next_mode) {
	  bdd_ptr temp = save_bdd(r_shift(result));
          release_bdd(result);
          result = temp;
          }*/
  }
  else {
    term_i.nc_term = nc_term;

    /* Go over the values of each bdd.
       Use the values and the nearly canonical terms to create real
       canonical terms, and use a "case" type of operator, in order to
       get the bdd which corresponds to applying the case on all
       values of each bdd. */
    result = save_bdd(ZERO);
    for (start_index_iteration(&term_i);
         !endof_index_iteration(&term_i);
         next_index_iteration(&term_i)) {

      bdd_ptr cond = current_cond(&term_i);
      bdd_ptr var = enforce_definition(current_canonical_term(&term_i));

      /*        if (next_mode) {
                bdd_ptr temp = save_bdd(r_shift(var));
                release_bdd(var);
                var = temp;
                }*/

      /*  result := case
          indexes == leaf : array_name[leaf] ;
          1 : result */
      temp_result = save_bdd(if_then_else_bdd(cond, var, result));

      release_bdd(cond);
      release_bdd(var);
      release_bdd(result);
      result = temp_result;
    }
    /* Ittai: This save seems redundant. Also, I think BDD's of indices need to
       be released */
    /* result = save_bdd(result); */
    int i;
    for (i = 0; i < term_i.num_indexes; i++)
      release_bdd(term_i.index[i].index);
  }
  err_node = temp;
  return result;
}

/* range_check is called by walk_leaves, which traverses
   a bdd and performs actions on the leaves of the bdd.
   range_check checks that these leaves are withing
   a type which is stored in the_range. the_range is
   a list of nodes, each of which is one value of the type. */

static node_ptr the_range,the_var;

static void range_check(node_ptr n)
{
  if(n == NIL)catastrophe("range_check: n == NIL");

  /* If the bdd leaf is a list itself, then check that
     each item on the list is in the range of the type. */
  if(n->type == LIST){
    while(n){
      if(!in_list(car(n),the_range))range_error(car(n),the_var);
      n = cdr(n);
    }
  }
  else if(!in_list(n,the_range))range_error(n,the_var);
}


/* This does a more thorough job in replacing formal arguments by
   the actual arguments.  It is very similar to eval_struct. */
node_ptr eval_formal_to_actual(node_ptr n, node_ptr context)
{
  if (n == NIL) return NIL;
  switch (n->type) {
  case ATOM: {
    node_ptr name = find_node(DOT,context,find_atom(n));
    node_ptr temp1 = get_value_of_by_name_param(name);
    node_ptr temp2 = get_symbol(name);
    bdd_ptr  temp3 = get_constant(find_atom(n));
    if (temp1 && temp2 || temp2 && temp3 || temp3 && temp1)
      rpterr("Error: atom \"%s\" is ambiguous", n->left.strtype->text);
    if (temp1) return eval_formal_to_actual(temp1,context);
    if (temp3) return find_atom(n);
  } /* fall through on purpose here */
  case DOT:
  case ARRAY:
    return eval_struct(n,context);
  case CONTEXT: return eval_formal_to_actual(cdr(n), car(n));
  default: return n;
  }
}

node_ptr eval_symbol(node_ptr n);

/* eval_aux is the main subroutine of eval. attempts
   to evaluate n in context, to a bdd. */
static bdd_ptr eval_aux(node_ptr n, node_ptr context)
{
  if (verbose > 2) {
    fprintf(tlvstdout, "eval_aux ");
    print_node(tlvstdout, n); fprintf(tlvstdout, "..\n");
  }

  if (n == NIL)
    return save_bdd(ONE);
  switch (n->type) {
  case ATOM: {
    bdd_ptr result;

    /* Canonical form.  */
    node_ptr name = find_node(DOT, context, find_atom(n));

    /* Check if this symbol might be a name of a formal
       parameter, which needs to be replaced by the actual argumet.  */
    node_ptr temp1 = get_value_of_by_name_param(name);

    /* Check if the symbol is stored in the symbol table.  */
    node_ptr temp2 = get_symbol(name);

    /* Check if the symbol is a constant.  */
    bdd_ptr temp3 = get_constant(find_atom(n));

    /* A symbol may only be evaluated using one of the three
       previous lines. It is an error if it can be evaluated in
       several ways.  */
    if (temp1 && temp2 || temp2 && temp3 || temp3 && temp1)
      rpterr("Error: atom \"%s\" is ambiguous", n->left.strtype->text);

    /* If name is a formal parameter, then take the actual argument
       and evaluate that into a bdd.  */
    if (temp1) result = eval_aux(temp1, context);

    /* If name is a constant then turn it into a leaf bdd and
       return it.  */
    else if (temp3)
      result = save_bdd(temp3);
    else
      result = enforce_definition(eval_struct(n, context));
    return result;
  }
  case DOT:
  case ARRAY: {
    /* fprintf(tlvstdout, "eval_aux: array "); */
    /* print_node(tlvstdout, n); fprintf(tlvstdout, "..\n"); */

    /* return enforce_definition(eval_struct(n,context)); */
    bdd_ptr result = eval_term_to_bdd(n, context);
    /* fprintf(tlvstdout, "eval_aux: Evaled array\n"); */
    return result;
  }
  case CONTEXT: return eval_aux(cdr(n), car(n));
  case LIST:
  case AND: return binary_op(and_bdd, n, 1, 1, 1, context);
  case FASTAND: return binary_op(fast_and_bdd, n, 1, 1, 1, context);
  case OR: return binary_op(or_bdd, n, 1, 1, 1, context);
  case FORALL: return binary_op(forall, n, 1, 1, 1, context);
  case FORSOME: {
    /* fprintf(tlvstdout, "eval_aux: forsome..\n"); */
    return binary_op(forsome, n, 1, 1, 1, context);
  }

  case DEFAULT: {
    extern bdd_ptr global_id;

    bdd_ptr result = binary_op(default_in_bdd, n, 1, 1, 1, context);

    bdd_ptr result_limited = limit_to(result, global_id);
    release_bdd(result);

    return save_bdd(result_limited);
  }

  case NOT: return unary_op(not_bdd,n,1,1,context);
  case IMPLIES: return binary_op(or_bdd,n,1,-1,1,context);
  case IFF: return binary_op(xor_bdd,n,-1,1,1,context);
  case CASE: return eval_if_then_else(car(car(n)),cdr(car(n)),cdr(n),context);
  case NOTEQUAL: return binary_op(equal_bdd,n,-1,1,1,context);
  case EQUAL: return binary_op(equal_bdd,n,1,1,1,context);
  case PLUS: return binary_op(plus_bdd,n,1,1,1,context);
  case MINUS: return binary_op(minus_bdd,n,1,1,1,context);
  case TIMES: return binary_op(times_bdd,n,1,1,1,context);
  case DIVIDE: return binary_op(divide_bdd,n,1,1,1,context);
  case MOD: return binary_op(mod_bdd,n,1,1,1,context);
  case LT: return binary_op(lt_bdd,n,1,1,1,context);
  case GT: return binary_op(gt_bdd,n,1,1,1,context);
  case LE: return binary_op(gt_bdd,n,-1,1,1,context);
  case GE: return binary_op(lt_bdd,n,-1,1,1,context);
  case NUMBER: return save_bdd(leaf_bdd(find_atom(n)));
  case NEXT: {
    if (is_term(car(n))) {
      bdd_ptr result;
      next_mode = 1;
      result = eval(car(n),context);
      next_mode = 0;
      return result;
    }
    else
      rpterr("Error: next( %n ): next expects a term, not an expression.\n"
             "Use the function prime instead.\n", car(n));
  }
  case SAT: return unary_op(sparse_sat_bdd,n,1,1,context);
  case QUANT: return unary_op(support_bdd,n,1,1,context);

  case SIZE: {
    /* Return size of bdd.  */
    int s;
    node_ptr s_node;

    /* Find bdd operand */
    bdd_ptr arg = eval(car(n),context);
    release_bdd(arg);

    /* Calculate size */
    s = size_bdd(arg);

    /* Convert size to node */
    s_node = find_NUMBER_node(s);

    return save_bdd(leaf_bdd(s_node));
  }
  case EXIST: {
    /* Returns true if the argument is a symbol. */
    node_ptr name = eval_struct(car(n),NIL);
    node_ptr val;

    if (val = get_symbol(name))
      return save_bdd(ONE);
    else
      return save_bdd(ZERO);
  }
  case FUNC:
    /* Run a function. Defined in script.c .
       The retuned value is already "save_bdd-ed". */
    return (bdd_ptr) run_func(car(n), cdr(n), 0);

  case TRUEEXP: return save_bdd(ONE);
  case FALSEEXP: return save_bdd(ZERO);
  case EX:
  case AX:
  case EF:
  case AF:
  case EG:
  case AG:
  case EU:
  case AU:
  case EBU:
  case ABU:
  case EBF:
  case ABF:
  case EBG:
  case ABG:
   return save_bdd(ONE);

  case EQDEF: {
    /* Evaluate an assignment: := */

    node_ptr lhs,t2,r;

    /* assign_type determines what kind of assignments should 
       be evaluated.  According to the left hand side of the
       assignment, determine if we want to evaluate it.
       If not, exit routine. If yes, Let lhs be the left
       hand side, and let t2 be the variable being assigned to.  */ 
    switch (assign_type) {
    case INIT:
      if (is_init_assignment(n))
        lhs = t2 = term_of_assignment(n);
        else
          return save_bdd(ONE);
      break;

    case NEXT:
      if (is_next_assignment(n)) {
        lhs = lhs_of_assignment(n);
        t2 = term_of_assignment(n);
      }
      else
        return save_bdd(ONE);
      break;

    case NEXT_OR_CURRENT:
      if (is_init_assignment(n))
        return save_bdd(ONE);
      else {
        lhs = lhs_of_assignment(n);
        t2 = term_of_assignment(n);
      }
      break;

    default:
      if (is_current_assignment(n))
        lhs = t2 = term_of_assignment(n);
      else
        return save_bdd(ONE);
      break;
    }

    /* Put the type of the variable in "r" */
    r = get_symbol_from_term(t2, context);
    if (r == NIL)
      undefined(t2);

    if (symbol_type(r) != PROGRAM_VAR_SYMBOL)
      redefining(t2);

    if (verbose > 2) {
      add_to_indent(1);
      indent_node(tlvstderr, "evaluating ", lhs, ":\n");
    }
    {
      /* v - bdd of right hand side of assignment. */
      bdd_ptr v = eval(cdr(n),context);

      /* Check that the values of the right hand side 
         are inside the type of the variable.  */
      the_var = t2;
      the_range = get_program_var_type(r);
      walk_leaves(range_check,v);

      /* Let v be the bdd which expresses that the variable lhs,
         should be assigned according to right hand side.  */
      {
        bdd_ptr v1 = eval(lhs,context);
        release_bdd(v1); release_bdd(v);
        v = save_bdd(setin_bdd(v1,v));
      }
      if (verbose > 2) {
        indent_node(tlvstderr, "eval_aux: size of ",lhs," = ");
        fprintf(tlvstderr,"%d BDD nodes\n",size_bdd(v));
        add_to_indent(-1);
      }
      return v;
    }
  }
  case STRING_EQ: {
    /* Check that the two arguments have equivalent string 
       representation. */
    node_ptr result1 = eval_symbol(car(n));
    node_ptr result2 = eval_symbol(cdr(n));

    /* Print as strings and compare. */
    strcpy(buf1, "");
    strcpy(buf2, "");
    sprint_node(buf1, BUFSIZE, result1);
    sprint_node(buf2, BUFSIZE, result2);

    if (!strcmp(buf1, buf2))
      return save_bdd(ONE);
    else
      return save_bdd(ZERO);
  }

  case TWODOTS: {
    /* Create union list from range.  */
    int dim1,dim2,i;
    dim1 = eval_num(car(n), context);
    dim2 = eval_num(cdr(n), context);

    /* If empty range, print error. */
    if (dim1 > dim2)
      rpterr("Error: empty range: %d..%d", dim1, dim2);
    else if (dim1 == dim2) 
      return eval(find_NUMBER_node(dim2), NIL);
    else {
      node_ptr t = find_NUMBER_node(dim2);
      for(i = dim2-1; i >= dim1; i--)
        t = find_node(UNION,find_NUMBER_node(i),t);
      n = t;
    }
  } /* fall through on purpose here */

  case UNION: return binary_op(union_bdd, n, 1, 1, 1, context);
  case SETIN: return binary_op(setin_bdd, n, 1, 1, 1, context);

  case FOR: {
    node_ptr expand = expand_for_once(n, context);
    return eval(expand, context);
  }
  case QUOTE:
    rpterr("Cannot evaluate string \"%s\" to bdd\n", atom_to_string(n));
    break;
  case NEXT_LTL: case EVENTUALLY:  case ALWAYS:
  case WEAKPREVIOUS: case PREVIOUSLY: case  ONCE:
  case HASALWAYSBEEN: case LTLUNTIL:  case  WAITINGFOR:
  case SINCE: case BACKTO:
    rpterr("Cannot evaluate temporal operator to bdd in expression \"%n\" to "
           "bdd\n", n);
  default:
    catastrophe2("Cannot evaluate type = %d to bdd\n", n->type);
  }
}


/* Function which converts an expression, "n", to a bdd. */
bdd_ptr eval(node_ptr n, node_ptr context)
{
  bdd_ptr res;
  node_ptr temp = err_node;
  if (n == NIL)
    return save_bdd(ONE);

  err_node = n;
  res = eval_aux(n, context);
  err_node = temp;

  mygarbage();
  return(res);
}

/**********************************************************************/

/* Take a tree of nodes (non leaf nodes are of type LIST),
   and evaluate all nodes. The results are returned as a tree. */
static node_ptr eval_tree(node_ptr n, node_ptr context)
{
  if (n == NIL) return(NIL);
  if (n->type == LIST)
    return(find_node(LIST, eval_tree(n->left.nodetype, context),
		     eval_tree(n->right.nodetype, context)));
  return(find_BDD_node(eval(n, context)));
}

/* ??  */
static bdd_ptr eval_simplify(node_ptr n, node_ptr context,
                             bdd_ptr assumption)
{
  if(n == NIL)return(save_bdd(ONE));
  err_node = n;
  switch(n->type){
  case AND:
    {
      bdd_ptr l = eval_simplify(car(n),context,assumption);
      bdd_ptr r = eval_simplify(cdr(n),context,assumption);
      bdd_ptr res = save_bdd(simplify_assuming(and_bdd(l,r),assumption));
      release_bdd(l); release_bdd(r); mygarbage();
      return(res);
    }
  case CONTEXT:
    return(eval_simplify(cdr(n),car(n),assumption));
  default:
    return(eval(n,context));
  }
}


/* Like eval, but the third parameter is a type which can be either
   INIT, NEXT, or 0. If it is INIT, then in assign section only init(x)
   assignments will be evaluated. If it is NEXT, then in assign section only
   next(x) assignments will be evaluated. If it is 0 then only assignments x := 
   will be evaluated. */
bdd_ptr eval_type(node_ptr n, node_ptr context, int type)
{
    assign_type = type;
    return eval(n,context);
}


/**********************************************************************
 
 The following are routines which are similar to the evaluation 
 routines for tlv, but they are for formulas. See the corresponding
 routines for bdds for an explanation of what they mean.

**********************************************************************/


/* And two formulas/parse-trees. */
node_ptr and_F(node_ptr a, node_ptr b)
{
  if (a == NIL)
    return b;
  else if (b == NIL)
    return a;
  else
    return find_node(AND,a,b);
}


node_ptr get_definition_F(node_ptr n)
{
  /* Get value of symbol */
  node_ptr val = get_symbol(n);

  /* Handle error cases. */
  if (!val) return NIL;
  if (enforce_constant && symbol_type(val) == PROGRAM_VAR_SYMBOL )
    {
      enforce_constant = 0;
      print_node(tlvstderr, n);
      rpterr("Error: constant required");
    }

  /* If symbol has a bdd, then return it (this is typical for dynamic
     variables with bdd value, or of program variables). */
  if (symbol_type(val) == PROGRAM_VAR_SYMBOL || 
      symbol_type(val) == DYNAMIC_VAR_SYMBOL)
    return n;

  /* If we have gotten to here, then the symbol is either defined in
     the DEFINE section, or it is a dynamic variable, which contains a
     parse tree. Evaluated the parse tree recursively. */
  return eval_F(parse_tree_of(val),NIL);
}


/* Gets formula of node n, but if it does not exist, then raises an error. */
static node_ptr enforce_definition_F(node_ptr n)
{
  node_ptr res;
  if ((res = get_definition_F(n)) != NIL) return res;
  undefined(n);
}



/* This function is instead of doing
   enforce_definition_F(eval_struct(()). The difference is that this
   procedure also handles indexes of arrays. */
node_ptr eval_term_to_F(node_ptr n, node_ptr context) 
{
  node_ptr temp,name;

  if (n==NIL) return NIL;

  switch(n->type){
  case CONTEXT: 
    /* This case is needed for evaluating actual parametrs, which 
       have a different context . */
    return eval_term_to_F(cdr(n),car(n));

  case ATOM:
    name = find_node(DOT,context,find_atom(n));

    /* Check if this name is a formal parameter and if so evaluate
       the actual parameter. An infinite loop might occur if
       the parameter and its value are equivalent - this will 
       happen since eval_struct is called recusively on the value
       of the parameter. Note that eval_aux only catches conflicts
       between ATOM and its parameter. In case of arrays or DOT,
       the only place we can catch such an infinite loop is here. */
    if(temp = get_value_of_by_name_param(name))
      {
        node_ptr find_temp = find_atom(temp);

        if (find_temp != find_atom(n) &&
            find_temp != name ) /* TRY TO AVOID INFINITE LOOPS.*/
          return eval_term_to_F(temp,context);
      }

    return name;

  case DOT: {
    node_ptr result;

    temp = eval_term_to_F(car(n),context);
    if(temp == TYPE_ERROR)rpterr("type error, operator = .");
    result = find_node(DOT,temp,find_atom(cdr(n)));

    /* Check again for formal parameters, so that from tlvbasic,
       it will be possible to refer to a formal parameter, and 
       get back the arguement. */
    if(temp = get_value_of_by_name_param(result))
        return eval_term_to_F(temp,context);
    else
      return result;
  }

  case ARRAY: {

    /* Evaluate index */
    node_ptr index = eval_F(cdr(n),context);

    /* Evaluate name of array. */
    node_ptr arr_name = eval_term_to_F(car(n),context);
    if(arr_name == TYPE_ERROR)rpterr("type error, operator = []");

    return find_node(ARRAY,arr_name, index);
  }
  case SELF:
    return context;
  default:
    return TYPE_ERROR;
  }
}

/* This is used for translating fragments of the smv file into
   formulas. */
node_ptr eval_F(node_ptr n, node_ptr context)
{
  if (n == NIL) return NIL;

  switch (n->type) {
  case CONTEXT: return eval_F(cdr(n),car(n));

  case ATOM: {
    node_ptr atom_n = find_atom(n);

    /* Cannonical form.  */
    node_ptr name = find_node(DOT,context,atom_n);

    /* Check if this symbol might be a name of a formal
       parameter, which needs to be replaced by the actual argumet.  */
    node_ptr temp1 = get_value_of_by_name_param(name);

    /* Check if the symbol is stored in the symbol table.  */
    node_ptr temp2 = get_symbol(name);

    /* Check if the symbol is a constant.  */
    bdd_ptr  temp3 = get_constant(atom_n);

    /* A symbol may only be evaluated using one of the three 
       previous lines. It is an error if it can be evaluated in
       several ways.  */
    if(temp1 && temp2 || temp2 && temp3 || temp3 && temp1)
      rpterr("Error: atom \"%s\" is ambiguous",n->left.strtype->text);

    /* If name is formal parameter, evaluate actual argument. */
    if (temp1) return eval_F(temp1,context);

    /* If name is a constant then return it as is. 
       Perhaps we could have opted instead to return its value as an integer. */
    if (temp3) return atom_n;

    /* Evaluate symbol. */
    return enforce_definition_F(eval_struct(n,context));
  }
  case DOT:  case ARRAY:
        return eval_term_to_F(n,context);

  /* Unary Operators */
  case NOT:
  case NEXT:
      return find_node(n->type, eval_F(car(n), context), NIL);



  /* Binary operators */
  case FASTAND:   case OR:
  case IMPLIES:  case IFF:
  case FORALL:   case FORSOME:
  case NOTEQUAL: case EQUAL:
  case LT:       case GT:      case LE:      case GE:
  case PLUS:     case MINUS:   case TIMES:   case DIVIDE:   case MOD:
  case CASE:     case COLON:  /* COLON handles a single line of CASE */
  case UNION:
  case SETIN:
  case DEFAULT:
    return find_node(n->type, eval_F(car(n), context),
                     eval_F(cdr(n), context));
  case AND:
  case LIST: return and_F(eval_F(car(n), context), eval_F(cdr(n), context));

  case EQDEF: {
    /* Evalutate an assignment: := */

    node_ptr lhs,t2,r;

    /* assign_type determines what kind of assignments should 
       be evaluated.  According to the left hand side of the
       assignment, determine if we want to evaluate it.
       If not, exit routine. If yes, Let lhs be the left
       hand side, and let t2 be the variable being assigned to.  */ 
    switch (assign_type_F) {
    case INIT:
      if(is_init_assignment(n))
        lhs = t2 = term_of_assignment(n);
      else
        return NIL;
      break;

    case NEXT:
      if (is_next_assignment(n)) {
        lhs = lhs_of_assignment(n);
        t2 = term_of_assignment(n);
      }
      else
        return NIL ;

      break;

    case NEXT_OR_CURRENT:
      if (is_init_assignment(n)) 
        return NIL;
      else {
        lhs = lhs_of_assignment(n);
        t2 = term_of_assignment(n);
      }

      break;

    default:
      if (is_current_assignment(n))
        lhs = t2 = term_of_assignment(n);
      else
        return NIL;

      break;
    }

    /* Put the type of the variable in "r" */
    r = get_symbol_from_term(t2, context);
    if(r == NIL) undefined(t2);
    if(symbol_type(r) != PROGRAM_VAR_SYMBOL) redefining(t2);

    if(verbose > 2){
      add_to_indent(1);
      indent_node(tlvstderr,"evaluating formula for", lhs, ":\n");
    }

    return find_node(SETIN, eval_F(lhs, context), eval_F(cdr(n), context));
  }
  case TWODOTS: {
    /* Create union list from range.  */
    int dim1,dim2;
    dim1 = eval_num(car(n), context);
    dim2 = eval_num(cdr(n), context);

    /* If empty range, print error. */
    if(dim1 > dim2 )
      rpterr("Error: empty range: %d..%d", dim1, dim2);
    else if (dim1 == dim2) 
      return find_NUMBER_node(dim2);
    else
      {
        int i;
        node_ptr t = find_NUMBER_node(dim2);
        for(i=dim2-1;i>=dim1;i--)
          t = find_node(UNION,find_NUMBER_node(i),t);

        return t;
      }
  }
  case FOR: {
    node_ptr expand = expand_for_once(n, context);
    return eval_F(expand,context);
  }

  /* Constants: should be returned as is */
  case NUMBER:
  case TRUEEXP:           case FALSEEXP:
  case QUOTE:

  /* Temporal operators. There is nothing we can do with them. */
  case EX:    case AX:    case EF:   case AF:
  case EG:    case AG:    case EU:   case AU:
  case EBU:   case ABU:   case EBF:  case ABF:   case EBG:   case ABG:
  case NEXT_LTL:      case EVENTUALLY:  case ALWAYS:
  case WEAKPREVIOUS:  case PREVIOUSLY:  case  ONCE:
  case HASALWAYSBEEN: case LTLUNTIL:    case  WAITINGFOR:
  case SINCE:         case BACKTO:
    return n;

  /* TLVBasic functions which are not expected inside SMV input files. */
  case SAT:   case QUANT:
  case SIZE:  case EXIST:
  case STRING_EQ:
  case FUNC:
  default:
    fprintf(tlvstderr, "Error: \n");
    fprint_node(tlvstderr, n);
    catastrophe2("Cannot evaluate type = %d to formula\n", n->type);
  }
}

node_ptr eval_type_F(node_ptr n, node_ptr context, int type)
{
    assign_type_F = type;
    return eval_F(n,context);
}

/**********************************************************************

 The following are routines which are called by eval_symbol.

**********************************************************************/

#define push_neg(p) positive_form( find_node(NOT,p,NIL) )

/* Return the temporal dual of a temporal operator.  */
int temporal_dual(int op)
{
  switch(op) {
  case EVENTUALLY:   return ALWAYS;
  case ALWAYS:       return EVENTUALLY;
  case WEAKPREVIOUS: return PREVIOUSLY;
  case PREVIOUSLY:   return WEAKPREVIOUS;
  case HASALWAYSBEEN: return ONCE;
  case ONCE:          return HASALWAYSBEEN;
  case LTLUNTIL:      return WAITINGFOR;
  case WAITINGFOR:    return LTLUNTIL;
  case SINCE:         return BACKTO;
  case BACKTO:        return SINCE;
  }
}

/* n is a parse tree of an ltl formula. This function returns
   the formula in "positive form", i.e. if the root is NOT
   then it is pushed downwards, as far as possible. 
   I am not sure this is really used anywhere, and I am not
   sure it works. */
node_ptr positive_form(node_ptr n)
{
  node_ptr p,q,r;

  switch (n->type) {
  case NOT:
    p = car(car(n));
    q = cdr(car(n));

    switch (car(n)->type) {
    case NOT:
        return positive_form(p);
    case OR:
        return find_node(AND, push_neg(p), push_neg(q) ); 
    case AND:
        return find_node(OR, push_neg(p), push_neg(q) ); 
    case NEXT_LTL: 
        return find_node(NEXT_LTL,push_neg(p),NIL); 

    case EVENTUALLY:  case ALWAYS:
    case WEAKPREVIOUS:  case PREVIOUSLY:  
    case HASALWAYSBEEN:  case ONCE:
        return find_node(temporal_dual(car(n)->type),
                         push_neg(p), NIL);

    case LTLUNTIL:  case WAITINGFOR:  case SINCE:  case BACKTO:
        r = push_neg(q);
        return find_node(temporal_dual(car(n)->type),
                         r,
                         find_node(AND,push_neg(p),r));
    }
  default:
    return n;
  }
}

/* Take a parse tree, and perform some manipulatios on it,
   to return another parse tree. The manipulations are preferomed
   mostly near the root.  This routine was the implementation
   of eval_symbol until tlv 4.13 */
node_ptr eval_symbol_old(node_ptr n)
{
  node_ptr context = NIL;
  switch(n->type){
  case ATOM:
    {
      node_ptr name = find_node(DOT,context,find_atom(n));
      node_ptr temp1 = get_value_of_by_name_param(name);
      node_ptr temp2 = get_symbol(name);
      bdd_ptr  temp3 = get_constant(find_atom(n));
      if(temp1) return(temp1); /* Return actual argument of formal parameter.  */
      if(temp3) return(n);  /* Return constant as is.  */
    } /* fall through on purpose here */
  case DOT:
  case ARRAY:
    {
      node_ptr val = get_symbol(eval_struct(n,context));
      switch ( symbol_type(val) ) {
        /*      case UNDEFINED_SYMBOL:  undefined(n); */
      case DEFINED_SYMBOL:    return cdr(parse_tree_of(val));/* Return value without context. */
      case PARSE_TREE_SYMBOL: return parse_tree_of(val);
      default:                return n;
      }
    }
  case FUNC:
    {
      /* Run a function. Defined in script.c .The retuned value is a node_ptr. */
      node_ptr result = (node_ptr) run_func(car(n),cdr(n), 1);
      if (result == NULL)
        return n;
      else
        return result;
    }
  default: return n;
  }
}

/* Take a parse tree/formula, n and perform some manipulations on it,
   to return another parse tree.  This is used to evaluate
   "Let '" and similar interactive commands.  */
node_ptr eval_symbol(node_ptr n)
{
  node_ptr context = NIL;

  if (n == NIL) return NIL;

  switch (n->type) {
  /* Expand dynamic variable which holds a formula/parse-tree.*/
  case ATOM: {
    node_ptr name = find_node(DOT, context, find_atom(n));
    node_ptr temp1 = get_value_of_by_name_param(name);
    node_ptr temp2 = get_symbol(name);
    bdd_ptr temp3 = get_constant(find_atom(n));
    if (temp1) return temp1; /* Return actual argument of formal parameter.  */
    if (temp3) return n;  /* Return constant as is.  */
  } /* fall through on purpose here */
  case DOT:
  case ARRAY: {
    node_ptr val = get_symbol(eval_struct(n, context));
    /* Note that we are not recursively evaluating the formulas.
       We just return them as is. */
    switch (symbol_type(val)) {
      /*      case UNDEFINED_SYMBOL:  undefined(n); */
    case DEFINED_SYMBOL:
      return cdr(parse_tree_of(val)); /* Return value without context. */
    case PARSE_TREE_SYMBOL: return parse_tree_of(val);
    default: return n;
    }
  }
  case FUNC: {
    /* Run a function. Defined in script.c. The returned value is a node_ptr. */
    /* Note that the parameters are not evaluated recursively. */
    node_ptr result = (node_ptr) run_func(car(n),cdr(n), 1);
    if (result == NULL)
      return n;
    else
      return result;
  }
    /* Recursively decend down the formula. */
  case NEXT:
  case NOT: return find_node(NOT, eval_symbol(car(n)), NIL);

  case AND:      case OR:       case IMPLIES:  case IFF:    case FASTAND:
  case FORALL:   case FORSOME:
  case NOTEQUAL: case EQUAL:
  case PLUS:     case MINUS:    case TIMES:    case DIVIDE: case MOD:
  case LT:       case GT:       case LE:       case GE:
  case SETIN:    case UNION:    case LIST:
    return find_node(n->type, eval_symbol(car(n)), eval_symbol(cdr(n)));

  case CASE: return find_node(CASE,
                              find_node(COLON,eval_symbol(car(car(n))),
                                        eval_symbol(cdr(car(n)))),
                              eval_symbol(cdr(n)));
  /* Expand for */
  case FOR: {
    node_ptr expand = expand_for_once(n, NIL);
    return eval_symbol(expand);
  }
    /* If the expression is quoted, return the quoted content
       as is, without recursion. */
  case QUOTE_LP: return car(n);

  case NUMBER:   case TRUEEXP:  case FALSEEXP:
  default: return n;
  }
}

/* The following two routines find canonical nodes
   (key) for the name of variables. */
node_ptr var_key(char *st)
{
  node_ptr temp = string_to_atom(st);
  return eval_struct(temp, NIL);
}

/* Find connanical name for variable which is an item "ind"
   of array whose name is in "st". */
node_ptr array_key(char *st, int ind)
{
  return find_node(ARRAY, var_key(st), find_NUMBER_node(ind));
}

/* Find connanical name for variable which is an item "ind"
   of array whose name is in "st". */
node_ptr array_key_from_node(node_ptr n, int ind)
{
  return find_node(ARRAY,
                   eval_struct(n, NIL),
                   find_NUMBER_node(ind));
}

/* Find canonical name for variable which is an item "ind1,ind2"
   of array whose name is in "st". */
node_ptr double_array_key(char *st, int ind1, int ind2)
{
  return find_node(ARRAY, array_key(st, ind1), find_NUMBER_node(ind2));
}

void init_eval(void)
{
  value_hash = new_assoc();
}
