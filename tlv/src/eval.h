/* This file has functions which perform various evaluations, on various
   types of expressins or terms. */


#define CURRENT 0
#define NEXT_OR_CURRENT 1


/**********************************************************************
  Evaluating expressions (parse trees) to bdds.
 **********************************************************************/

/* Function which converts an expression, "n", to a bdd. */
bdd_ptr  eval(node_ptr n, node_ptr context);


/* Like eval, but the third parameter is a type which can be either
   INIT, NEXT, or CURRENT. If it is INIT, then in assign section only init(x)
   assignments will be evaluated. If it is NEXT, then in assign section only
   next(x) assignments will be evaluated. If it is 0 then only assignments x := 
   will be evaluated. */
bdd_ptr  eval_type(node_ptr n, node_ptr context, int type);


/**********************************************************************
  Evaluating expressions originating from SMV input file,
  into parse trees/formulas. Similar to the two functions above.
 **********************************************************************/

node_ptr eval_F(node_ptr n, node_ptr context);
node_ptr eval_type_F(node_ptr n, node_ptr context, int type);

/* And two formulas/parse-trees. */
node_ptr and_F(node_ptr a, node_ptr b);

/**********************************************************************
  Evaluating parse tree to a different parse tree
 **********************************************************************/

/* Evaluates a parse tree expression but not into a bdd.
   Instead, there are special operations which can be done in tlv basic
   on parse trees. These are evaluated here. */
node_ptr  eval_symbol(node_ptr n);

/**********************************************************************
  Process small sections of parse trees.
 **********************************************************************/

/* "n" is a term which could be an atom or an array item, for example,
   proc.rec[3].state . This routine returns a *cannonical* represention
   of such a term. The two important operations which do this are:

    1) Replace formal parameters by actual arguments  (partially). 

    2) Put the term in the correct context.  For example, a term
       rec[3].state in the context "proc" will be returned as a connanical
       term representing proc.rec[2].state .  */
node_ptr eval_struct(node_ptr n, node_ptr context);

node_ptr eval_struct_status(node_ptr n, node_ptr context, int *status);

/* This does a more thorough job in replacing formal arguments by
   the actual arguments.  It is very similar to eval_struct. */
node_ptr eval_formal_to_actual(node_ptr n, node_ptr context);

/* Evaluate an expression "e" to an integer number. The expression
   can contain constants, names of constants defined in the DEFINE section,
   and any numeric operations which act on numbers. */
int eval_num(node_ptr e,node_ptr context);



/* The following two routines find connanical nodes
   (key) for the name of variables. */
node_ptr var_key(char *st);

/* Find connanical name for variable which is an item "ind"
   of array whose name is in "st". */
node_ptr array_key(char *st, int ind);

/* Find connanical name for variable which is an item "ind"
   of array whose name is in "st". */
node_ptr array_key_from_node(node_ptr n, int ind);

/* Find connanical name for variable which is an item "ind1,ind2"
   of array whose name is in "st". */
node_ptr double_array_key(char *st, int ind1, int ind2);

/**********************************************************************/

/* Clear the value cache, which caches evaluations of symbols
   which are defined in the DEFINE section, or symbols which
   are defined using Let 'x := */
void clear_value_hash(void);

/* Remove a specific symbol from the value hash.
   This is used mostly for parameters of tlv-basic programs which
   are preceeded by ' . Once the subprogram is exited, we want
   to make sure that the value of this parameter is not cached. */
void remove_from_value_hash(node_ptr n);

/**********************************************************************/

/* To use this file you must call this routine first. */
void init_eval(void);
