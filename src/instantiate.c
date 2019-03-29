/* Instantiation routines (modules, systems, etc) 
   and instantiation of variables.

   It is only called from smv.c . The main routine is "instantiation",
   at the end of the file.
*/

#include <storage.h>
#include <mystring.h>
#include <node.h>
#include <y.tab.h>
#include <node_smv.h>
#include <hash.h>
#include <assoc.h>
#include <util_err.h>
#include "symbols.h"
#include "eval.h"
#include "fts.h"


/* Assoc hash table in which each model name is associated with 
   new_node(LAMBDA,params,reverse(def)) where def are the rest of 
   the declarations.
   The hash table is created in add_modules_to_hash */
static hash_ptr module_hash = 0;

/* This stack contains a list of modules which are in
   process of instantiation. A module requires instantion
   when a variable is defined in the VAR section with
   a type of a module. Keeping this stack allows us to
   detect whether some module instantiates itself recursively. */
static node_ptr module_stack = NIL;


node_ptr variables;


/* Defined in grammar.y */
extern int yylineno;

/**********************************************************************/

/* build the module table "module_hash" */
void add_modules_to_hash(node_ptr parse_tree)
{
  node_ptr temp;
  node_ptr module;

  LOOP_OVER_MODULES( parse_tree, module, temp ) {
    node_ptr name   = name_of_module(module);
    node_ptr params = params_of_module(module);
    node_ptr def    = sections_of_module(module);

    if (find_assoc(module_hash,name)) redefining(name);
    insert_assoc(module_hash,name,new_node(LAMBDA,params,reverse(def)));
  }
}
/**********************************************************************/

static hash_ptr component_hash;

/* Routines to save and retrieve the type and actual parameters of
   a component according to it's name. */

static void insert_associate_component(node_ptr name, 
                                       node_ptr type, node_ptr actual)
{
   insert_assoc(component_hash,name,cons(type,actual));
}

static int get_associated_component(node_ptr name,
                                    node_ptr *type, node_ptr *actual)
{
   node_ptr result = find_assoc(component_hash,name);

   if (!result)
       return 0;

   *type = car(result);
   *actual = cdr(result);

   return 1;
}



/*************************************************************************
   Instanitation:

   An SMV file can have definitions of many modules. The module named
   "main" is considered the main module of the program. This module
   is where instaniation starts from. module main is instantiated.
   This requires that all the definitions in the VAR section are
   instantiated. Some of the VAR definitions are of variables:
   their instantiation involves inserting them into the symbol table.
   Other definitions are of other modules: these are instantiated
   recursively. Note that the same module may be instantiated several
   times. The place where the module is instantiated is called the
   "context". context is represented as a node_ptr. NIL is the
   context of the main module. Each instantiated module has a unique
   name which is composed of the context and the variable name of
   the instantiade module. For example:

   MODULE main
   VAR
      A : p;
   
   MODULE p
   VAR 
      B : q;
      D : q;

   MODULE q
   VAR 
      C : boolean

   This would create modules, A, A.B and A.D .
   The context of module A.B is A.

   The following are the main procedures which deal with instantiation:

     instantiate
     instantiate_by_name
     system_by_name
     inst_one_var
     instatntiate_vars
     make_params

   In the  three routines, (instantiate_by_name, process_by_name
   and system_by_name) the parameters are as follows:

    module_name -> Pointer to ATOM which contains the module name
    context -> Name of variable which is the context,
               usually in the form (DOT,context,name)
    fts    -> Data structure for current transition system.
    actual -> argument list of process: A list of (CONTEXT,context,expr)

**********************************************************************/

static component_ptr instantiate(node_ptr l, node_ptr n, fts f,
                                 node_ptr actual);

/* Instantiate a synchronous module, and return the corresponding
   component */
static component_ptr instantiate_by_name(node_ptr module_name, node_ptr context,
                                         fts f, node_ptr actual)
{
  component_ptr returned_c;
  node_ptr s;
  node_ptr cannonical_module_name = find_atom(module_name);

  /* Find module in module_hash. If it doesn't exist this is an error */
  node_ptr m = find_assoc(module_hash, cannonical_module_name);

  yylineno = module_name->lineno;

  if (!m)
    undefined(module_name);

  /* Scan module stack to check if module is recursively defined (error). */
  for (s = module_stack; s; s = cdr(s))
    if (car(s) == cannonical_module_name)
      rpterr("module \"%s\" is recursively defined",
             module_name->left.strtype->text);

  /* Push c1 ( atom which contains module name ) on module stack */
  module_stack = cons(cannonical_module_name, module_stack);

  /* Instantiate module. */
  returned_c = instantiate(m, context, f, actual);

  /* Pop module stack */
  s = cdr(module_stack); free_node(module_stack); module_stack = s;

  return returned_c;
}

/* Handle system. */
static void system_by_name(node_ptr sys_name, node_ptr module_name,
                           node_ptr actual)
{
  /* My name is actually the context of the instantiation of the
     module. */
  node_ptr context = sys_name;

  /* Allocate new transition system. */
  fts f = new_fts(sys_name);

  /* Instantiate the module. */
  component_ptr c = instantiate_by_name(module_name, context, f, actual);

  /* Add the component to the transition system. */
  add_component_as_top_process_of_fts(f,c);
}

/**********************************************************************/

/* This variable is only used in this routine and in inst_one_var */
static node_ptr param_context;

/* Put the node "v" under a CONTEXT node, with context param_context */
static node_ptr put_in_context(node_ptr v)
{
    return(find_node(CONTEXT,param_context,v));
}

/* Put a list of nodes and put each node into context. */
static node_ptr put_list_in_context(node_ptr list, node_ptr context)
{
    param_context = context;
    return map(put_in_context,list);
}


/**********************************************************************/

/* Handle one variable with known name and type.
   The type is simply a pointer to "type" in the parse tree.
   "name" is a node_ptr with a root of DOT or ARRAY.
   is_structure is true if this module contains a STRUCTURE (COMPOSED)
   section. */
component_ptr inst_one_var(node_ptr name, node_ptr type, fts f,
                           node_ptr context, int is_structure)
{
  component_ptr new_c = 0;

  yylineno = type->lineno;

  switch (type->type) {
  case BOOLEAN:
    /* Create a boolean variable */

    /* Update symbol table. */
    insert_program_var(name, 0, boolean_type);

    /* Remember set of declared variables. */
    variables = cons(name, variables);
    f->variables = cons(name, f->variables);

    /* The cdr of the type contains its kind.
       The kind of specified by a "kind of <name>" syntax,
       where name is any string you want.
       This line notes what kind the variable is. */
    add_kinds(f, name, cdr(type));
    break;
  case TWODOTS: {
    /* Create an integer ranged variable */

    node_ptr t = NIL;
    int dim1,dim2,i;

    /* Extract range */
    dim1 = eval_num(car(car(type)),context);
    dim2 = eval_num(cdr(car(type)),context);

    /* Create a range tree to be similar to SCALAR, i.e.
       create a data structure which would have been created
       had we used the syntax {1,2,3,4,5} instead of 1..5 */
    for (i = dim2; i >= dim1; i--)
      t = cons(find_NUMBER_node(i), t);
    if (t == NIL) {
      start_err();
      fprintf(tlvstderr, "empty range type %d..%d for ", dim1, dim2);
      print_node(tlvstderr, name);
      finish_err();
    }
    /* Insert variable with range tree */

    insert_program_var(name, 0, t);

    variables = cons(name, variables);
    f->variables = cons(name, f->variables);

    add_kinds(f, name, cdr(type));
    break;
  }
  case SCALAR:
    /* Insert variable with list of possible values */

    insert_program_var(name, 0, car(type));

    variables = cons(name, variables);
    f->variables = cons(name, f->variables);

    add_kinds(f, name, cdr(type));
    break;

  case MODTYPE:        /* Create a syncronous module */

    /* If there is a STRUCTURE section, then do not instantiate the module.
       This will be done by handling the STRUCTURE section. */
    {
      /* Make "actual" be a list of actual arguments (expressions) for
         the module whose name is car(type) ( an ATOM ).
         cdr(type) is an "neexprlist" .
         The list of actual arguments is put into context by replacing
         each expr node in the neexprlist by (CONTEXT,context,expr) */
      node_ptr actual = put_list_in_context(cdr(type),context);


      if (is_structure) {
        /* Save data about component for later processing of the
           COMPOSED section. */
          node_ptr name_key = eval_struct(name,context);
          insert_associate_component(name_key ,type,actual);
          /*          print_node(tlvstderr, name_key);*/
      }
      else{
          /* Handling the synchronous module */
        /*          node_ptr name_key = eval_struct(name,context);*/
          new_c = instantiate_by_name(car(type), name, f, actual);
      }
    }
    break;

  case PROCESS:  /* Create an asyncronous process */
  case SYSTEM:
    if (is_structure)
      rpterr("A module with a STRUCTURE section cannot have a process or "
             "system");
    else {
      /* Make "actual" be a list of actual arguments (expressions) for
         the module whose name is car(car(type)) ( an ATOM ).
         cdr(car(type)) is an "neexprlist" .
         The list of actual arguments is put into context by replacing
         each expr node in the neexprlist by (CONTEXT,context,expr) */
      node_ptr actual = put_list_in_context(cdr(car(type)), context);

      if ( type->type == SYSTEM ) {
        /* Handle new system. */
        system_by_name( name, car(car(type)), actual);
      }
      else {
        /* Handling the asynchronous process */
        component_ptr c = instantiate_by_name( car(car(type)), name, f, actual);
        add_component_as_top_process_of_fts(f,c);
      }

      break;
    }
  case ARRAY:
    {
      /* Create an array of variables */

      int dim1,dim2,i;

      /* Exctract array dimensions */
      dim1 = eval_num(car(car(type)),context);
      dim2 = eval_num(cdr(car(type)),context);

      /* Create many variables, one for each item of the array */
      for(i=dim1;i<=dim2;i++)
	new_c = 
          synch_compose(new_c,
                        inst_one_var(find_node(ARRAY,name,find_NUMBER_node(i)),
		                     cdr(type),f, context, is_structure)
                       );
      break;
    }
  default:
    catastrophe2("instantiate_vars: type = %d",type->type);
  }

  return new_c;
}


/* This function is used interactively from tlv.c */
void inst_one_variable(node_ptr name, node_ptr type,node_ptr context)
{
  /* Bogus transition system for defining program variables
     interactivley. */
  static struct fts_data interactive_f;  
  /*  static component_rec interactive_c;*/

  inst_one_var(name, type,
               &interactive_f, /*&interactive_c, */
               context, 0);
}

/* Handle VAR section of a module */
static component_ptr instantiate_vars(node_ptr var_list, node_ptr context,
                                      fts f, int is_structure)
{
  /* This is a recursive function.
     Instatiate other variables in the list first. This means that the last
     variable in the "vlist" is instantiated first, but this should be the case
     since we didn't reverse the var list */
  if (var_list == NIL) return 0;

  {
    /* Instantiate the rest of the variables. */
    component_ptr new_c =
      instantiate_vars(cdr(var_list), context, f, is_structure);

    node_ptr v = car(var_list);    /* v points to "COLON" node */
    node_ptr type = cdr(v);        /* type points to "type" node */
    /* name is variable name (term) which could be ARRAY or DOT */
    node_ptr name = eval_struct(car(v), context);

    /* Check if name already exists */
    if (get_symbol(name))
      redefining(name);

    /* Handle a single variable with a known name and type.
       n is the context */
    new_c =
      synch_compose(new_c, inst_one_var(name, type, f, context, is_structure));

    return new_c;
  }
}

/* Process COMPOSED section. */
static component_ptr instantiate_structure(node_ptr struct_def,
                                           node_ptr context,
                                           fts f )
{
  component_ptr c;

  switch (struct_def->type) {
  case ASYNCHCOMP:
  case SYNCHCOMP:
    c = new_component_fill(struct_def->type,
			   instantiate_structure(car(struct_def), context, f),
			   instantiate_structure(cdr(struct_def), context, f),
                           context);
    break;

  default:
    { 
      /* Instantiate the component. */

        node_ptr name = eval_struct(struct_def, context);
        node_ptr type, actual;

        /* Get data about associated component. */
        if (!get_associated_component(name,&type,&actual)) {
            print_node(tlvstderr, name);
            rpterr("Undefined component in structure declaration");
        }

        c = instantiate_by_name(car(type), name, f, actual);
    }
    break;
  }
  
  return c;
}



/* Mapping formal parameters to actual parameters of a module,
   using "param_hash". The paramter "basename" is the context in 
  which the instantiation is taking place*/
void make_params(node_ptr basename, node_ptr actual, node_ptr formal)
{
  /* Loop over all formal parameters */
  while(formal){
    node_ptr old,neww; 
    if(!actual)rpterr("Error: too few actual paramaters");

    /* Find node for formal (new) and actual (old) parameters */

    /*    neww = eval_struct(basename,car(formal));  */
    neww = find_node(DOT,basename,find_atom(car(formal))); 
    /*    neww = build_struct(basename,find_atom(car(formal)));  */
    old = car(actual);

    /* Advance pointers of parameter lists */
    formal = cdr(formal);
    actual = cdr(actual);

    /* If the formal paramter is already associated with an
       actual paramter, then the module has been defined
       using two identical formal paramters. Error. */
    if(get_value_of_by_name_param(neww)){
      start_err();
      fprintf(tlvstderr,"Multiple substitution for ");
      print_node(tlvstderr,neww);
      finish_err();
    }

    /* Insert association of formal to actual parameters in "param_hash" */
    insert_by_name_param(neww,old);
  }
  if(actual)rpterr("Error: too many actual paramaters");
}

/* n - the ltl formula. */
static node_ptr put_ltl_formula_in_context(node_ptr n, node_ptr context)
{
  if ( n == NIL )
    return NIL;

   switch(n->type){
   case ATOM: case DOT: case ARRAY:
     /* Put in context. */
     return eval_formal_to_actual(n,context);

   case NUMBER: case TRUEEXP: case FALSEEXP:
     /* return as is */
     return n;

   default: 
     /* Recursive call. */
     return find_node(n->type,
                        put_ltl_formula_in_context(car(n), context),
                        put_ltl_formula_in_context(cdr(n), context)
                        );
   } 
}

/*
 This routine defines "macros" for ltl formulas which can be 
 included in the transition relation. The macro is implemented 
 not as a normal DEFINE symbol, which is evaluated to a bdd.
 Instead it is implemented as a boolean variable. This variable
 will serve as the variable corresponding to the forumla in the
 tester which is created from the forumla.

 name - principle variable of the temporal formula.
 ltl  - the temporal formula.

 name is already given as a key (i.e. it is returned
 from eval_struct(name,context), but ltl is not.
*/
void ltl_definition(node_ptr name, node_ptr ltl, node_ptr context, fts f)
{
  node_ptr ltl_in_context;

  /* Define boolean variable for name ( or maybe symbol to a variable) */
  insert_program_var(name,0,boolean_type);

  /* Remember set of declared variables. */
  variables = cons(name,variables);
  f->variables = cons(name,f->variables);

  /* Instantiate variables in ltl forumla according to context. */
  ltl_in_context = put_ltl_formula_in_context(ltl,context);

  /* Save the name and formula in a table so that we 
     can export them as dynamic variables. */
  f->ltl_list = cons(cons(name,ltl_in_context),f->ltl_list);
}

/**********************************************************************/

/* Replace occurences of atom var_key, with replace_node, in the
   the tree template. */
node_ptr sub_it(node_ptr var_key, node_ptr replace_node, 
                node_ptr template) 
{
  if (template == NIL) return NIL;

  switch (template->type) {
  case NUMBER: case QUOTE:
    return template;

  case ATOM:
    if (var_key->left.strtype == template->left.strtype)
      return replace_node;
    else
      return template;

  default:
    return find_node(template->type, 
		     sub_it(var_key, replace_node ,car(template)),
		     sub_it(var_key, replace_node ,cdr(template)) );
  }
}


node_ptr expand_if(node_ptr if_node, node_ptr context)
{
    node_ptr result = NIL;
    node_ptr condition = condition_of_if(if_node);

    bdd_ptr cond_bdd = eval(condition, context);

    if ( cond_bdd == ONE )
      result = then_of_if(if_node);
    else
      result = else_of_if(if_node);

    release_bdd(cond_bdd);

    return result;
}

node_ptr init_loop_result(int connection_type)
{
  switch (connection_type) {
  case OR: return find_node(FALSEEXP, NIL, NIL);
  case AND: return find_node(TRUEEXP, NIL, NIL);
  default: return NIL;
  }
}

node_ptr expand_for_once(node_ptr tree, node_ptr context)
{
  node_ptr template = cdr(tree);
  int connection_type = car(tree)->type;
  node_ptr result = init_loop_result(connection_type);

  /* Extract parts of the for loop. */
  node_ptr index_var = car(car(car(tree)));
  node_ptr init_val = cdr(car(car(tree)));
  node_ptr while_expr = car(cdr(car(tree)));
  node_ptr next_val = cdr(cdr(car(tree)));

  bdd_ptr while_bdd;

  /* Evaluate initial value and insert dynamic variable. */
  bdd_ptr next_bdd = eval(init_val, context);
  node_ptr index_var_key = eval_struct(index_var, context);

  if (!insert_update_dynamic_var(index_var_key, next_bdd)) {
    print_node(tlvstderr, index_var_key);
    rpterr("Error, Variable already exists as program variable.");
  }

  /* We must evaluate this only after the dynamic variable
     has been set. */
  while_bdd = eval(while_expr, context);

  /* Perform instance iteration. */
  while (while_bdd == ONE) {
    /*node_ptr replace_node = find_NUMBER_node(value_bdd(next_bdd));*/
    node_ptr replace_node = leaf_value_bdd(next_bdd);

    /* Instantiate variable to its value using, template */
    node_ptr instance = sub_it(index_var, replace_node, template);

    /* We want to accumulate the instance into the result.
       If the instance is in intself the list, we want to preserve
       the list structure. */
    if (instance->type == LIST)
      result = append(instance, result);
    else if (connection_type == LIST)
      result = new_node(AND, instance, result);
    else {
      /* If this is not a list, then we don't want the dangling
         NIL at the final cdr. */
      /*         printf("connection_type %d  :", connection_type);*/
      if (result == NIL)
        result = instance;
      else
        result = new_node(connection_type, instance, result);
    }
    /* Evaluate next value and update dynamic variable. */
    next_bdd = eval(next_val, context);
    insert_update_dynamic_var(index_var_key, next_bdd);

    release_bdd(while_bdd);
    while_bdd = eval(while_expr, context);
  }
  release_bdd(while_bdd);
  delete_dynamic_var(index_var_key);

  return result;
}

/* Instantiate "for" structure. */
node_ptr expand_for(node_ptr tree, node_ptr context)
{
 node_ptr l;

 if (tree == NIL) return NIL;

 switch (tree->type) {
 case NUMBER: case QUOTE: case ATOM:
   return tree;

 case FOR: {
   node_ptr result = expand_for_once(tree, context);

   /* Do expansion again, in case there are nested for loops. */
   result = expand_for(result, context);
   return result;
 }
 case IFSMV: {
   node_ptr result = expand_if(tree, context);

   /* Do expansion again, in case there are nested if-s */
   result = expand_for(result, context);
   return result;
 }
 case LIST:
   if (car(tree) &&  
       (car(tree)->type == FOR || car(tree)->type == IFSMV)) {
     /* Try to expand the car to be part of the list, instead
        of being a son of the current node. */
     node_ptr expand_car = expand_for(car(tree), context);
     node_ptr expand_cdr = expand_for(cdr(tree), context);

     /* Append cdr to end of car.*/
     return append(expand_car, expand_cdr);
   }
   /* Otherwise, continue to default. */

   /*  case AND: case ASYNCHCOMP:  case SYNCCOMP: */
 default: {
   /* Try to expand the car to be part of the list, instead
      of being a son of the current node. */
   node_ptr expand_car = expand_for(car(tree), context);
   node_ptr expand_cdr = expand_for(cdr(tree), context);

   if (0 /*expand_car->type == LIST */)
     /* Append cdr to end of car, since the car was
        probably expanded by "for" */
     return append(expand_car, expand_cdr);
   else
     return new_node(tree->type,
                     expand_car, expand_cdr);
 }
 }
}

void process_define_list(fts f, node_ptr dl, node_ptr context)
{
  if (dl == NIL)
    return;
  else {
    node_ptr definition = car(dl);

    /* Process the rest of the list first. */
    process_define_list(f, cdr(dl), context);

    if (definition->type == FOR) {
      node_ptr processed_for = expand_for(definition, context);
      process_define_list(f, processed_for, context);
    }
    /* cons(car(e),for_clauses); */
    else {
      /* Find name and value of definition. */
      node_ptr name = eval_struct(car(definition),context);
      /*        node_ptr value = expand_for(cdr(definition), context);  */
      node_ptr value = expand_for(cdr(definition), context); 

      yylineno = dl->lineno;

      /* Insert definitions into symbol_hash */
      if(get_symbol(name))
        redefining(name);

      /* Check if the definition is for an LTL forumla */
      if (definition->type == LTL)
        ltl_definition(name, value, context, f);
      else
        insert_define(name,value,context,0);
    }
  }
  /*  return reverse(for_clauses);*/
}

/* Take a list, which may contain other lists, and make
   them one long single list. */
node_ptr flatten(node_ptr n)
{
  if (n != NIL && n->type == LIST) {
    node_ptr n_car = flatten(car(n));
    node_ptr n_cdr = flatten(cdr(n));

    if (n_car != NIL && n_car->type == LIST)
      return append(n_car, n_cdr);
    else
      return find_node(LIST, n_car, n_cdr);
  }
  else
    return n;
}

/* Handle all sections (DEFINE,VAR, ...) of a module ( or process ).
   This is the main procedure for instantiation.

   The function returns a component which corresponds to the module.

    l       -> Pointer to definition of module.
    context -> Name of variable which is the process(context)
               Usually in the form (DOT,context,name)
    actual -> argument list of process
              A list of (CONTEXT,context,expr)
*/
static component_ptr instantiate(node_ptr l, node_ptr context, fts f,
                                 node_ptr actual)
{
  /* new_c is the new component which is created in this routine.

     return_c  - the component which is returned to the caller. 

     Note that these are not the same, since during instantiation,
     addtional components may be created, and they are gathered
     under return_c. So return_c can actually be a tree of components,
     whereas new_c will point to the single component which is created
     in this procedure. */
  component_ptr new_c, return_c;

  /* True if there is a COMPOSED section in current module. */
  int is_structure = 0;

  node_ptr d, temp;
  /* List of formal parameters of the module/process. */
  node_ptr formal = car(l);
  /* All the other sections of a modules/process. */
  node_ptr module_sections = cdr(l);
  node_ptr struct_node;

  /* Associate formal parameters with actual parameters. */
  make_params(context, actual, formal);

  /* first, instantiate all the definitions
     we do the definitions first, in case they are constants
     used in the array declarations. We also search to see
     if there is any STRUCTURE definition. If there is such a definition,
     the meaning of a lot of declarations changes. For example, TRANS and ASSIGN
     sections are not allowed, and modules and processes are not instantiated */
  for (d = module_sections; d; d = cdr(d)) {
    node_ptr s = car(d);
    switch (s->type) {
    case DEFINE: {
      /* Evaluate "DEFINE" section. Each iteration processes one defition. */
      node_ptr e = car(s);
      process_define_list(f, e, context);
    }
      break;

    case STRUCTURE:
      /* Detect STRUCTURE (COMPOSED) section */
      if (!is_structure) {
        is_structure = 1;
        struct_node = s;
      }
      else
        rpterr("Error: Only one STRUCTURE section can be defined per module.");
      break;
    default:
      break;
    }
  }
  if (!is_structure) {
    return_c = new_c = new_component();
    new_c->context = context;
  }

  /* Now, instantiate all the variables, and the sections (TRANS, INIT, etc) */
  for (d = module_sections; d; d = cdr(d)) {
    node_ptr e = car(d);
    switch (e->type) {
    case VAR:
      temp = expand_for(car(e), context);

      /* Handle variables */
      if (is_structure)
        instantiate_vars(temp, context, f, is_structure);
      else
        /* We compose the component which results from instantiating the
           variable, since the variables can include modules or processes. */
        return_c = synch_compose(return_c,
                                 instantiate_vars(temp, context, f,
                                                  is_structure) );
      break;
    case TRANS:
      if (is_structure)
        rpterr("Error: A module exists which has both STRUCTURE and TRANS "
               "sections");
      /* Add transition section into component. */
      new_c->trans =
        find_node(AND,new_c->trans,find_node(CONTEXT,context,car(e)));
      break;

    case ASSIGN:
      if (is_structure)
        rpterr("Error: A module exists which has both STRUCTURE and ASSIGN "
               "sections");
      temp = expand_for(car(e), context);

      /* Concatenate assignments into myassign tree , where each node in
         the assignment tree is (CONTEXT,context,alist) .
         The tree is built like a list but with AND instead of LIST */
      add_assign_to_component(new_c, find_node(CONTEXT, context, temp)); 
      break;

    case OWNED:
      if (is_structure)
        rpterr("Error: A module exists which has both STRUCTURE and OWNED "
               "sections");
      {
        node_ptr o = expand_for(car(e), context);
        new_c->owned = append(new_c->owned, put_list_in_context(o, context));
        break;
      } 

    case INIT:
      add_init_to_fts(f, find_node(CONTEXT,context,car(e)));
      break;

    case JUSTICE: {
      /* Add to justice list , where each node in
         the spec list is (CONTEXT,context,expr) */
      temp = expand_for(car(e), context);
      temp = flatten(temp);

      add_justice_list_to_fts(f, reverse(put_list_in_context(temp, context)));
      break;
    }
    case COMPASSION: {
      /* Concatenate compassion expressions into comp list , where each node in
         the compassion list is 
             (LIST,
                (CONTEXT,context,expr1),    -- expr1 == process name
                (CONTEXT,context,expr2))    -- expr2 == Expression */
      node_ptr c;
      temp = expand_for(car(e), context);
      for (c = temp ; c; c = cdr(c))
        add_compassion_to_fts(f, find_node(CONTEXT,context,caar(c)),
                              find_node(CONTEXT,context,cdar(c)));
      break;
    }

      /* I don't know what the following options does. Stems from
         smv, which was not documented. */

    case ISA:
      /* Process the module which is mentioned after ISA (its name is in car(e))
         but don't change the context n. There are no actual arguments so 
         the last parameter is NIL */
      instantiate_by_name(car(e), context, f, NIL);
      break;
    default:
      break;
    }
  }

  /* If there is a structure, evaluate the modules according to what
     it specifies. "struct_node" points to the start of that section. */
  if (is_structure) {
    node_ptr expanded = expand_for(car(struct_node), context);
    return instantiate_structure(expanded, context, f);
  }
  else
    return return_c;
}

/**********************************************************************/
node_ptr instantiation(node_ptr parse_tree) 
{
  if (!module_hash) {
    module_hash = new_assoc();
    component_hash = new_assoc();
  }
  /* Add modules to module hash. */
  add_modules_to_hash(parse_tree);

  /* Handle system whose main module is "main", with context NIL
     and with no actual arguments.
     Also do the following:
     1. Collect systems into f.
     2. Collect components into a component tree.
     3. Insert all variables into symbol table and into "variables".
     4. Collect JUSTICE, COMPASSION and INIT. */
  system_by_name(NIL, string_to_atom("main"), NIL);
  return reverse(variables);
}
