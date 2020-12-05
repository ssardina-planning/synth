/*
  This file implements a symbols package which is referenced
  by tlv. Some symbols should initialy be inserted by the input language.

  The following symbol types are supported:

    Program variable - PROGRAM_VAR_SYMBOL
      This is a program variable. Tlv cannot assign to it.
      It can be used to compare expressions.
      There is a type associated with a variable.
      This is stored in the symbol table. A bdd is also
      associtated with a variable. The bdds are created from
      the type by the part of the program which translates the
      input file into an fts. This is not done immediatly since
      first all the variables should be defined and then there
      should be a way to assign bdd variables to the program
      variables in a specific order to minimize the bdd sizes.

    Definition -     DEFINED_SYMBOL
      This is a symbol which has been declared in the SMV DEFINE
      section. It cannot be assigned to. It does not have a bdd
      associated with it. It is associated with a context and
      a parse tree of the definition of the symbol.
      In a sense - using a defined symbol is similar to a macro
      expansion.

    dynamic variable - DYNAMIC_VAR_SYMBOL
      These are the variables which can be assigned by tlv.
      Have a bdd  associated with them.

    dynamic parse-tree variables: PARSE_TREE_SYMBOL

 Note that many routines here obtain data about symbols not using
 the symbol name, but by using the data returned by the function
 get_symbol.

 For example, to get a bdd of a symbol, whose canonical
 name is stored in variable k, you can do:

 symb_val = get_symbol(k);

 if (has_bdd(symb_val))
   return bdd_of(symb_val);

 The following is old, probably irrelevant documentation.

   Assoc hash table in which each symbol name is associated with:
   Symbols are variables and defines.

   In procedure "inst_one_var" :
     Boolean var       -  new_node(VAR,NIL,boolean_type)   
     Numeric range var -  new_node(VAR,NIL,(LIST,(NUMBER,dim1,NIL)
                                                ,(LIST,(NUMBER,dim1+1,NIL)...
                                                        
                                                (LIST,(NUMBER,dim2,NIL),NIL))))
     Scalar var        -  new_node(VAR,NIL,enum type)

  In procedure "instantiate" :
     Define            -  find_node(CONTEXT,n,def)  where n is context and 
                                                    def value of define


  One of the main structures used in is the symbols_hash.
  A symbol value can be of one of the following types:
 
     (VAR,bdd,type)  - 
       This symbols is a variable. The left branch contains its
       corresponding bdd and the right one contains the actual
       parse tree of the type of the variable.

     (BDD,bdd,NIL) - Contains a bdd. This bdd can be a dynamic 
                     variable with a bdd value.


   VAR - program variable.
   CONTEXT - DEFINED - cannot be assigned to or changed.
   BDD -   Dynamic variables which contain bdds.         - can be changed.
*/

#include <node.h>
#include <storage.h>
#include <hash.h>
#include <util_err.h>
#include <assoc.h>
#include <y.tab.h>
#include "symbols.h"

/* List of all dynamic variables. */
node_ptr dynamic_vars = NIL;

node_ptr dtemp;

/* Symbol table. */
static hash_ptr symbol_hash;

/* "frame" is a stack. The current frame is always at the top of this stack. */
static node_ptr frame = NIL;

/* Assoc hash table in which each formal parameter is associated
   with an actual paramter. Indirectly used by "make_params" */
static hash_ptr param_hash;

/* Constant table. */
static hash_ptr constant_hash;


/* Initialize tables */
void init_symbols()
{
  symbol_hash = new_assoc();
  param_hash = new_assoc();
  constant_hash = new_assoc();
}


/* Return type of symbol, according to data about symbol. */
enum symbol_enum symbol_type(node_ptr val)
{
  if (val == NIL)
    return UNDEFINED_SYMBOL;
  else
    return val->type;
}


/**********************************************************************
  Generic routines.
 **********************************************************************/

void insert_symbol(node_ptr name, node_ptr val)
{
  insert_assoc(symbol_hash, name, val);
}

/* Get the value/data about the symbol ( NIL if symbol does not exist ) */
node_ptr get_symbol(node_ptr name)
{
  return find_assoc(symbol_hash, name);
}

/* Remove symbol from the symbol hash.
   It returns the value the symbol had if it existed */
node_ptr remove_symbol(node_ptr name)
{
  node_ptr val = get_symbol(name);

  if (val != NIL) {
    remove_assoc(symbol_hash,name,val);
    return (val);
  }
  else
    return NIL;
}

/* Like get_symbol, but tries to find a program variable.
   If it finds another variable, it may be the case that
   the program variable is pushed on the frame, since it
   was overridden by a parameter or by a dynamic variable.
   So we search for the program varialbe on the frame.

   This is ugly... */
node_ptr get_program_var_symbol(node_ptr name)
{
  node_ptr val = get_symbol(name);

  if (val->type != PROGRAM_VAR_SYMBOL) {
    /* Traverse frames. */
    node_ptr frame_ptr = frame;
    for (; frame_ptr; frame_ptr = cdr(frame_ptr)) {
      /* Get list of stored variables of frame.  */
      node_ptr stored_vars = caar(frame_ptr);
      for (; stored_vars; stored_vars = cdr(stored_vars)) {
        node_ptr name2 = caar(stored_vars);
        node_ptr val2 = cdar(stored_vars);

        if (name == name2 && val2->type == PROGRAM_VAR_SYMBOL)
          return val2;
      }
    }
  }
  return val;
}

/**********************************************************************
 Insert and get information about specific types of symbols.          */

/* Enter program variable to symbol table */
void insert_program_var(node_ptr name, bdd_ptr b, node_ptr type)
{
  insert_assoc(symbol_hash, name,
               new_node(PROGRAM_VAR_SYMBOL, (node_ptr) b, type));
}

node_ptr get_program_var_type(node_ptr val)
{
  return cdr(val);
}

/* Insert dynamic variable with bdd value */
void insert_dynamic_var(node_ptr name, bdd_ptr b)
{
   insert_assoc(symbol_hash, name,
                new_node(DYNAMIC_VAR_SYMBOL, (node_ptr) b, NIL));

   /* Add to list. This is done so we can print the list of dynamic
      variables. */
   dynamic_vars = cons(name, dynamic_vars);
}

/* Inserts the variable if doesn't exist. If it does it updates it.
   Returns 1 if successful, and 0 if variable already exists as program
   variable. */
int insert_update_dynamic_var(node_ptr var, bdd_ptr b)
{
  node_ptr x = get_symbol(var);

  switch (symbol_type(x)) {
  case UNDEFINED_SYMBOL:
    /* Create dynamic variable */
    insert_dynamic_var(var, b);
    return 1;

  case DYNAMIC_VAR_SYMBOL:
    /* Update dynamic variable. */
    release_bdd(bdd_of(x));
    mygarbage();
    update_bdd(x, b);
    return 1;

  default:
    /* Error,
       The assigned variable already exists (e.g. as a program variable */
    return 0;
  }
}

void delete_dynamic_var(node_ptr var)
{
  node_ptr dvar;

  node_ptr x = remove_symbol(var);

  release_bdd(bdd_of(x));

  /* Delete var from list. */
  dynamic_vars = list_minus_one(dynamic_vars, var);
}

void duplicate_dynamic_var_from(node_ptr new, node_ptr from)
{
  node_ptr sym_info = get_symbol(from);

  insert_update_dynamic_var(new,save_bdd(bdd_of(sym_info)));
}


void insert_define(node_ptr name, node_ptr def, node_ptr context, bdd_ptr b)
{
  insert_assoc(symbol_hash, name,
               new_node(DEFINED_SYMBOL,
                        (node_ptr) b ,
                        find_node(CONTEXT,context,def)));
}

/* Insert dynamic variable with parse tree value */
void insert_parse_tree(node_ptr name, node_ptr def)
{
  insert_assoc(symbol_hash, name,
               new_node(PARSE_TREE_SYMBOL, NIL, def));
}

/**********************************************************************/

/* Print all dynamic variables (with bdd values) with their sizes. */
void print_all_dynamic_vars()
{
  int nvars = 0;
  node_ptr l = dynamic_vars;

  for (;l; l = cdr(l)) {
      node_ptr val;

      val = get_symbol(car(l));

      if (val) {
        fprint_node(tlvstderr,car(l));
        fprintf(tlvstderr," : %d\n",size_bdd(bdd_of(val)));
        nvars++;
      }
  }

  fprintf(tlvstderr,"Total number of dynamic variables: %d\n",
                    nvars);
}
/**********************************************************************/

/* Return 1 if this symbol has a bdd. */
int has_bdd(node_ptr val)
{
  if (val != NIL &&
      ((val->type == PROGRAM_VAR_SYMBOL && val->left.bddtype != 0) ||
       val->type == DYNAMIC_VAR_SYMBOL ||
       (val->type == DEFINED_SYMBOL && val->left.bddtype != 0)))
    return 1;
  else
    return 0;
}

/* Return the value of the bdd. */
bdd_ptr bdd_of(node_ptr val)
{
  return val->left.bddtype;
}

/* Add bdd to a program var (which until now only had a type). */
void update_bdd(node_ptr val, bdd_ptr b)
{
  val->left.bddtype = b;
}

/**********************************************************************/

/* Return 1 if this symbol has a parse tree. */
int has_parse_tree(node_ptr val)
{
  switch (symbol_type(val)) {
  case DEFINED_SYMBOL:
  case PARSE_TREE_SYMBOL:
    return 1;
  default:
    return 0;
  }
}

/* Return parse tree of symbol. */
node_ptr parse_tree_of(node_ptr val)
{
  switch (symbol_type(val)) {
  case DEFINED_SYMBOL:
  case PARSE_TREE_SYMBOL:
    return cdr(val);
  default:
    return NIL;
  }
}

/**********************************************************************/

/* Frame stack routines.
   The frame stack is implemented as a list of frames. Each frame
   is a list node with a left and right son. The left son contains
   a list of (name,value) pairs which are name/value of symbols which
   have been superseeded by local declarations, or formal arguments
   of subprograms (procedures, functions). These values are
   restored when the tlv-basic routine is exited (which causes the frame to
   get poped). The right son contains associations of formal parameters
   of tlv-basic subprograms, to their actual arguments, when the formal
   parameters are defined to pass the value by name. This is done
   by adding & in front of the parameter name.
 */

#define store_stack_of_current_frame &(top_node(&frame)->left.nodetype)
#define param_stack_of_current_frame &(top_node(&frame)->right.nodetype)

#define new_frame() new_node(LIST,NIL,NIL)
void free_frame(node_ptr frame)
{
  free_node(frame);
}

/* Push frame onto frame stack. */
void push_frame(void)
{
  push_node(&frame, new_frame());
}

/*
  Searches for a (key, value) pair in a list. If found, returns the
  pair. Otherwise returns NIL.
 */
node_ptr find_list_assoc(node_ptr list, node_ptr key)
{
  while (list != NIL)
    if (car(car(list)) == key)
      return car(list);
    else
      list = cdr(list);
  return NIL;
}

int exists_local(node_ptr name)
{
  if (empty(frame))
    catastrophe("Error: Trying to store symbol on empty frame\n");
  else {
    node_ptr *store_vars = store_stack_of_current_frame;
    return find_list_assoc(*store_vars, name) != NIL;
  }
}

/* Delete the symbol from the symbol table, but remember its value
   on the frame. */
void delete_symbol_and_store_on_frame(node_ptr name)
{
  if (empty(frame))
    catastrophe("Error: Trying to store symbol on empty frame\n");
  else {
    /* Remove symbol from hash table and store it on a stack
       which is held in the car of the current frame. */
    node_ptr *store_vars = store_stack_of_current_frame;
    node_ptr val = remove_symbol(name);
    push_node(store_vars, cons(name,val));
  }
}

/* If this is true, then we probably have never entered
   interactive mode, since there are no frames. So
   we are probably still loading smv files. */
static int in_first_frame(void)
{
  return frame == NIL;
}

/*
  The following routines solve the following problem.
  We want to use parameters by name both in smv (for instantiating
  modules) and in tlv ( for passing parameters by name ).
  Furthermore, we want parameters by name which were defined in smv,
  to be retained throught the session so that the user can refer to
  variables using parameter names. But we want to throw away
  by-name parameters which were defined in tlv, as soon as the
  procedure or function has terminated.

  The solution: as long as we are in the first frame, the
  parameter-by-names are stored directly in param_hash. But if
  we are not in the first frame then this means that we are
  executing a tlv subroutine. In this case, parm-by-names are
  first looked up in the frame and only then in param_hash.
*/
node_ptr get_value_of_by_name_param(node_ptr param)
{
  /* First try to search in frame. */
  if (!in_first_frame()) {
    node_ptr *param_stack = param_stack_of_current_frame;
    node_ptr param_list = *param_stack;

    for (;param_list; param_list = cdr(param_list))
      if (car(car(param_list)) == param)
        return cdr(car(param_list));
  }
  /* Param-by-name was not found in frame, so try param_hash. */
  return find_assoc(param_hash, param);
}

/* Associate formal parameter names with actual parameters.
  This can occur in two places. It first can occur inside the
  smv file, when instantiating modules. In this case there
  is no first frame, so the associated is entered into the
  param_hash. A second place this occurs is in formal paramters
  of tlv-basic subrouties. These associations are stored on
  the frame, and are therefore eliminated once the subprogram
  is over, and the frame is poped. */
void insert_by_name_param(node_ptr param, node_ptr val)
{
  /* If we are not in the first frame, then insert param-by-name
     in frame, otherwise insert it in global hash. */
  if (! in_first_frame() )
    {
      node_ptr *param_list = param_stack_of_current_frame;
      push_node(param_list,cons(param,val));
    }
  else
    insert_assoc(param_hash,param,val);
}


/* Insert internal variable. These are only used internally for 
   implementing complex tlvbasic structures, like For and Fix.
   It is easier to put these here since they will get deallocated
   automatcially when the frame is released. */
/*void insert_internal_var(node_ptr stmt_id, int var_id, bdd_ptr value)
{
  node_ptr var_key = internal_key(stmt_id, var_id);
  
}

bdd_ptr get_internal_var(node_ptr stmt_id, int var_id)
{
  node_ptr var_key = internal_key(stmt_id, var_id);
  node_ptr temp;

  LOOP_OVER_INTERNAL_VARS(temp) {
     
  }
}
void delete_internal_var(node_ptr stmt_id, int var_id, bdd_ptr)
{
}*/

/* Pop frame. */
void pop_frame(void)
{
  if (empty(frame))
    catastrophe("Error: Trying to store symbol on empty frame\n");
  else
    {
      /* Restore symbols. */
      node_ptr *store_vars = store_stack_of_current_frame;
      node_ptr *param_vars = param_stack_of_current_frame;

      while (!empty(*store_vars)) {
        node_ptr top = top_node(store_vars);
        node_ptr name = car(top);
        node_ptr val = cdr(top);

        /* Remove symbol and deallocate bdd if needed. */
        node_ptr info = get_symbol(name);
        node_ptr oldsymbolval;

        if (info == NIL) {
          info = NIL;
          /* This can happen if a variable was declared as Local,
             without an assignment, and was never assigned to... */
          /*          fprintf(tlvstderr,"Trying to delete symbol : ");
          print_node(tlvstderr,name);
          fprintf(tlvstderr,"\n"); */
        }

        else if (info->type == DYNAMIC_VAR_SYMBOL)
          delete_dynamic_var(name);

        /* If the type of symbol is a parse tree dynamic variable,
           then make sure that the bdd value of it does not remain cached
           in value_hash. If did not do this, then the next time
           a subprogram is called with a "'p" parameter, then this
           parameter, if it was evaluted into a bdd in a previous call,
           would have its value cached in value_hash, and the current
           call would use the same value when evaluating p into a bdd, 
           even if the actual parameter had changed. */

        else if ((oldsymbolval = remove_symbol(name))!= NIL)
          {
            if (oldsymbolval->type == PARSE_TREE_SYMBOL)
              remove_from_value_hash(name);

            if (has_bdd(oldsymbolval))
              release_bdd(bdd_of(oldsymbolval));
          }

        /* If there was an old value, restore it */
        if (val != NIL)
          insert_symbol(name,val);

        free_node(top);

        pop_node(store_vars);
      }      

      /* Free list of param-by-name variables. */
      while (!empty(*param_vars)) {
        free_node(top_node(param_vars));
        pop_node(param_vars);
      }      
 
      /* Pop frame. */
      free_frame(pop_node(&frame));
    }
}


/* This is used in case there was an error in the
   execution of the procedure and we want to clear 
   all local variables. */
void pop_all_frames(void)
{
  while (!empty(frame))
    pop_frame();
}




/**********************************************************************/
/*                   Constants                                        */
/**********************************************************************/

bdd_ptr get_constant(node_ptr c)
{
   return (bdd_ptr) find_assoc(constant_hash,c);
}

void insert_constant(node_ptr c, bdd_ptr bdd_val)
{
   insert_assoc(constant_hash,c,(node_ptr)bdd_val);
}
