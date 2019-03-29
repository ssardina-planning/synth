/***********************************************************************

   This file is responsible for retrival (and storage) of information about
   symbols which can appear in expressions (except constants).

   Currently, 4 types of symbols are supported:

   * Program variable.

   * Dynamic variable (whose value is a bdd).

   * Dynamic variable (whose value is a parse tree).

   * Definition (i.e. something which is declared in the DEFINE section).
    


  On top of this there is special treatment for parameters which 
  are passed by name.

***********************************************************************/

#ifndef SYMBOLSHDEF
#define SYMBOLSHDEF

#include "bdd.h"


extern node_ptr dynamic_vars;
extern node_ptr dtemp;

/* Type of symbol */
enum symbol_enum {UNDEFINED_SYMBOL,
                  PROGRAM_VAR_SYMBOL, 
                  DYNAMIC_VAR_SYMBOL, 
                  PARSE_TREE_SYMBOL,   /* This is also a dynamic variable. */ 
                  DEFINED_SYMBOL};


/* Initialize package. */
void init_symbols(void);

/* Return type of symbol according to symbolc value (not name) */
enum symbol_enum symbol_type(node_ptr val);


/***********************************************************************
 These are GENERIC routines which insert, get and remove symbols,
 no matter what kind they are. */ 

/* insert_symbol should only be used when the type of the symbol is unknown.
  For example, if we want to delete a symbol temporarily, we can remove 
  it and put it back using insert_symbol. */
void insert_symbol(node_ptr name, node_ptr val);

/* Both get_symbol and remove_symbol return the data about the symbol. */
node_ptr get_symbol(node_ptr name);
node_ptr remove_symbol(node_ptr name);

/* Like get_symbol, but tries to find a program variable.
   If it finds another variable, it may be the case that 
   the program variable is pushed on the frame, since it
   was overridden by a parameter or by a dynamic variable.
   So we search for the program varialbe on the frame. */
node_ptr get_program_var_symbol(node_ptr name);

/**********************************************************************
 Insert and get information about specific types of symbols.  */
 
/* Insert program variable symbol.  b - associated bdd, type - node with
   type information . */
void insert_program_var(node_ptr name, bdd_ptr b, node_ptr type);

/* Get the "type" information from the symbol data. */
node_ptr get_program_var_type(node_ptr val);


/* Insert dynamic var. */
void insert_dynamic_var(node_ptr name, bdd_ptr b);

/* Inserts the variable if doesn't exist. If it does it updates it.
   Returns 1 if successful, and 0 if variable already exists as program
   variable. */
int insert_update_dynamic_var(node_ptr var, bdd_ptr b);
void delete_dynamic_var(node_ptr var);
void duplicate_dynamic_var_from(node_ptr new, node_ptr from);
#define LOOP_OVER_DYNAMIC_VARS(dvar) for (dtemp=dynamic_vars, dvar= dtemp? car(dtemp): NIL; \
                                          dtemp; \
                                          dtemp=cdr(dtemp), dvar= dtemp? car(dtemp): NIL)


/* Insert parse tree (dynamic variable which acts similar to DEFINE) */
void insert_parse_tree(node_ptr name, node_ptr def);

/* Insert define. b - cached bdd. */
void insert_define(node_ptr name, node_ptr def, node_ptr context, bdd_ptr b);


/**********************************************************************
  Handle bdd component of symbol data. */

/* has_bdd may return true if the symbol data contains a bdd. 
   This may be true for PROGRAM_VAR_SYMBOL, DYNAMIC_VAR_SYMBOL
   and DEFINED_SYMBOL. */
int has_bdd(node_ptr val);

/* Get bdd of symbol. val is the data about the symbol, and
   not the symbol name itself. */
bdd_ptr bdd_of(node_ptr val);

/* Update the bdd component of the symbol data. */
void update_bdd(node_ptr val, bdd_ptr b);

/**********************************************************************
  Handle parse tree component of symbol data. */

int has_parse_tree(node_ptr val);
node_ptr parse_tree_of(node_ptr val);



/********************************************************************
 Routines for parameters which are passed by name in tlv procedures.
   These are implemented on the frames.
*********************************************************************/

void push_frame(void);

/* Used when a local variable is defined, but the symbol
   name already exists. This routine stores the old value on
   the frame stack. */
void delete_symbol_and_store_on_frame(node_ptr name);

/* Returns true if a local has already been defined in the current frame */
int exists_local(node_ptr name);

/* Handle by_name parameters which are defined in formal
   arguments of tlv-basic procedures/functions. */
node_ptr get_value_of_by_name_param(node_ptr param);
void insert_by_name_param(node_ptr param, node_ptr val);

/* Restores all stored symbols on frame. */
void pop_frame(void);

/* This is used in case there was an error in the
   execution of the procedure and we want to clear
   all local variables - so we remove all frames. */
void pop_all_frames(void);


/*********************************************************************/
/*     Routines which store and retrieve constants.                  */
/*********************************************************************/


bdd_ptr get_constant(node_ptr c);
void insert_constant(node_ptr c, bdd_ptr bdd_val);

#endif
