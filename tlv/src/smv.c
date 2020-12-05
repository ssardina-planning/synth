/* 
  $ Revision: $

  This source has routines which translate an smv file to a transition system.
  It contains several sections:

  1) Finding errors in the system.
  2) Calculating bdds and setting dynamic variables.

  The main function of this file is smv2fts, which is called from main.c .
  It takes the parse tree from the global variable "parse_tree", calculates
  the bdd's which encode the transition system, and export these bdds as
  dynamic variables.

  I think that this file should be split into several files,
  since it is too big, and has sections which can be encapsulated.
*/

#include <stdio.h>
#include <storage.h>
#include <mystring.h>
#include <node.h>
#include <node_smv.h>
#include <hash.h>
#include <bdd.h>
#include <bdd2var.h>
#include <assoc.h>
#include <util_err.h>

#include <y.tab.h>

#include "script.h"
#include "symbols.h"
#include "eval.h"

#include "fts.h"
#include "instantiate.h"

/***********************
  External vars
 ***********************/

/* Flags are modified only in main.c */

/* Amount of dijunctive transition relations which are generated
   from smv files. */
int disj_amount       = 1; /* -disj flag should be 1 */

/* This flag can be set or unset from main.c . */
int generate_formulas = 0; 


node_ptr variables = NIL;   /* Names of all variables in program */

/* According to value of verbose print additional infomation.
   Usually used for debugging. */
extern int verbose;


/* Defined in grammar.y */
extern int yylineno;



/***********************
 Static variables 
 ***********************/

/* Global variables which contain the set of all program variables, 
   and the preservation of all program variables. Including new
   program variables whicha are created interactively. */
bdd_ptr global_vars;
bdd_ptr global_id;

/* Total number of transitions found. */
static int global_trans_num =0;


/* These hashes are used to check the program for multiple assignments,
   colliding assignments, etc. */
static hash_ptr assign_hash = 0;
static hash_ptr global_assign_hash;

/* All variables with current assignement in program */ 
static node_ptr def_variables = NIL;   



/* Calculate the support for an entire list of variable names.
   Recall that each variable may be encoded by several bdd variables.
   The support is a bdd which contains all these bdd variables.  
   The support can be used for quantification, or for preserving 
   values.  */
bdd_ptr calc_list_support(node_ptr l)
{
  node_ptr sym_val;

  if (l == NIL)
    return ONE;
  else {
    if ( ( sym_val = get_symbol(car(l))) == NIL ) {
       start_err();
       fprintf(stderr, "calc_list_support: variable not declared: ");
       print_node(stderr,car(l));
       finish_err();
    }
    else
       /* Recursive call . */
       return and_bdd(support_bdd( bdd_of( sym_val ) ),
                      calc_list_support(cdr(l))
                     );
  }
}

/* The input is a list of variables. We compute a bdd which
   preserves them. */
bdd_ptr id_of_var_list(node_ptr l)
{

  bdd_ptr id = ONE;

  for ( ; l; l = cdr(l)) {
    node_ptr sym_val = get_symbol(car(l));

    if ( sym_val == NIL ) {
       start_err();
       fprintf(stderr, "id_of_var_list: variable not declared: ");
       print_node(stderr,car(l));
       finish_err();
    } 
    else {
      bdd_ptr bdd_of_sym = bdd_of( sym_val );
      id = and_bdd(id, equal_bdd(bdd_of_sym, r_shift(bdd_of_sym)));
    }
  }

  return id;

  /* ALternative implementation
  id = save_bdd(ONE);
  {
    bdd_ptr temp_bdd2 ;
    node_ptr l = variables ;

    while(l) {
      node_ptr v = car(l);     v is the current variable in the list
      bdd_ptr r = eval(v,NIL); release_bdd(r);     Find bdd of v 

      temp_bdd2 = save_bdd(equal_bdd(r,r_shift(r)));
      and_it_in(&id,temp_bdd2);

      l = cdr(l);
    }
  } 

 */

}


node_ptr id_of_var_list_F_without_b(node_ptr l, node_ptr b)
{
  node_ptr id = NIL;

  for ( ; l; l = cdr(l)) {

      /* Check that the symbol is not owned by c. */
      node_ptr temp = b;
      int add_it = 1;
      for (;temp;temp = cdr(temp)) 
        if (car(temp) == car(l)) {
          add_it = 0;
          break;
        }

      if (add_it) 
        id = and_F(id, find_node(EQUAL, car(l), find_node(NEXT,car(l),NIL)) );
  }

  return id;
}


/* Calculate the state space for an entire list of variable names.
   Recall that each variable may be encoded by several bdd variables.
   The state space is a bdd which contains all possible bdd encodings
   of these variables. Each variable has several possible encodings
   according to the number of values it its range, so we do a disjunction
   over these encodings. We then do a conjunction for all the variables.  
   The state space can be used for satisfiability routines, so they
   will not go out of the state space.  */
bdd_ptr calc_state_space(node_ptr l)
{
  node_ptr sym_val;

  if (l == NIL)
    return ONE;
  else {
    if ( ( sym_val = get_symbol(car(l))) == NIL ) {
       start_err();
       fprintf(stderr, "calc_list_support: variable not declared: ");
       print_node(stderr,car(l));
       finish_err();
    }
    else
       /* Recursive call . */
       return and_bdd(support_bdd( bdd_of( sym_val ) ),
                      calc_state_space(cdr(l))
                     );
  }
}




/* Returns bdd which preserves owned of component c which are 
   not owned of component me. */
bdd_ptr preserve(component_ptr c, component_ptr me) 
{
  /* Find list of all variable owned by c but not by me. */
  node_ptr preserve_list = set_minus_node(c->prop_owned, me->prop_owned);

  if (preserve_list == NIL)
      return ONE;
  else
      /* Return bdd which preserves these variables. */
      return id_of_var_list(preserve_list);
}


node_ptr preserve_F(component_ptr c, component_ptr me) 
{
      /* Return node which preserves these variables. */
      return id_of_var_list_F_without_b(c->prop_owned, me->prop_owned);
}



/* Print a list of nodes to tlvstdout. */
void print_list(node_ptr n) 
{
    node_ptr l = n;
    for (;l;l=cdr(l))
      { 
         print_node(tlvstdout,car(l));
         fprintf(tlvstdout,"\n");
      }
}


/**********************************************************************/

/* Printouts for debugging and seeing how things progress. */
static print_in_process(char *s,
                        node_ptr context)
{
  fprintf(tlvstderr,"%s",s);
  if(context != NIL)
    indent_node(tlvstderr," in process ",context,"");
  fprintf(tlvstderr,"...\n");
}

/**********************************************************************/




/**********************************************************************/

/* This variable is only used in these routines */
static node_ptr param_context;

static node_ptr eval_struct_in_context(node_ptr v) 
{
    return eval_formal_to_actual(v,param_context);
}

/* Evaluate a list of variable names, and eval_struct them,
   given the context. Take into account that these variable might
   be formal arguments of the module, and we want the result
   to be the actual arguments which were passed to the module. */
static node_ptr eval_struct_list_in_context(node_ptr list, node_ptr context)
{
    param_context = context;
    return map(eval_struct_in_context,list);
}


/************************************************************
   Check program
 ************************************************************/


static void check_circular_assign(node_ptr n,node_ptr context);

static void check_circ(node_ptr n,node_ptr context)
{
  if(n == NIL)return;
  yylineno = n->lineno;
  switch(n->type){
  case NUMBER:
  case BDD:  
  case VAR:
    return;
  case ATOM:
    {
      node_ptr name = find_node(DOT,context,find_atom(n));
      node_ptr temp1 = get_value_of_by_name_param(name);
      node_ptr temp2 = get_symbol(name);
      bdd_ptr  temp3 = get_constant(find_atom(n));
      if(temp1 && temp2 || temp2 && temp3 || temp3 && temp1)
	rpterr("atom \"%s\" is ambiguous",n->left.strtype->text);
      if(temp1){check_circ(temp1,context); return;}
      if(temp3)return;
    } /* fall through on purpose here */
  case DOT:
  case ARRAY:
    {
      int status;
      node_ptr t = eval_struct_status(n,context,&status);

      /* Check circularity, only for terms which have no array indexes
         or have constant array indexes (i.e are not program variables.*/
      if (status)
        check_circular_assign(t,context);

      return;
    }
  case CONTEXT:
    check_circ(cdr(n),car(n));
    return;
  default:
    check_circ(car(n),context);
    check_circ(cdr(n),context);
    return;
  }
}

#define CLOSED_NODE (node_ptr)(-2)

/* Check for circular assignments. 
   This is done by using "assign_hash". Data is first put into to 
   assign_hash by calling check_assign with parameter 
   mode = CHECK_MULTIPLE_ASSIGNMENTS. This calls considers a set of 
   assignments and associates (using assign_hash) each left hand side
   ( e.g. x, next(x), ... )
   of the assignment with the right hand side (what comes after the := ) .

   Parameter n is a lhs of an assignment. The procedure goes over the
   corresponding right hand side, and searches it recursively for 
   circularities.
 */
static void check_circular_assign(node_ptr n,node_ptr context)
{

  /* Find right hand side which corresponds to left hand side in n. */
  node_ptr t = find_assoc(assign_hash,n);

  /* Test if we have already checked this left hand side. */
  if(t == CLOSED_NODE)return;

  /* If we this is the second time we are trying to process 
     this left hand side then we have found a circularity. */
  if(t == FAILURE_NODE)circular(n);

  /* n does not have a corresponding right hand side, so it
     was not assigned to. */
  if(t == NIL) {
      t = get_symbol(n);

      /* If t was defined in the DEFINED section, then expand the
         definition. */
      if (has_parse_tree(t))
        t = parse_tree_of(t);
  }

  /* If t == NIL, then it is either a constant, or an unknown symbol. */
  if(t == NIL){
    if(get_constant(n))return;
    undefined(n);
  }


  /* Mark this left hand side, as being in the process of being checked. */
  insert_assoc(assign_hash,n,FAILURE_NODE);

  /* Recursive call. */
  push_atom(n);
  check_circ(t,context);
  pop_atom();

  /* Mark this left hand side, as being checked already. */
  insert_assoc(assign_hash,n,CLOSED_NODE);
}


#define CHECK_MULTIPLE_ASSIGNMENTS 0
#define CHECK_CIRCULAR_ASSIGNMENTS 1
#define CALCULATE_OWNED_AND_CURRENT_ASSIGNED 2

/* Check all assignments in node n ( which is an list of AND's of
   assignemnts of one process) according to mode.   This routine can be
   used as a framework to traverse over all assignments in node "n". To check
   something (or do) else, add code to the internal switch on the "mode".

   Most of the switch(n->type) structure implements a recursive call to
   reach the assignments. */
static void check_assign(node_ptr n, node_ptr context, component_ptr c, int mode)
{
  if(n == NIL)return;
  yylineno = n->lineno;
  switch(n->type){
  case DEFAULT:
    check_assign(car(n),context, c, mode);
    break;
  case AND: 
    check_assign(car(n),context, c, mode);
    check_assign(cdr(n),context, c, mode);
    break;
  case CONTEXT:
    check_assign(cdr(n),car(n), c, mode);
    break;
  case EQDEF:
    {
      /* We have reached an assignment, so break it down into its components
         can perform a check according to mode. */

      int status;
      node_ptr var;  /* Variable name of left hand side. */
      node_ptr var_symbol_val;
      node_ptr lhs;  /* Entire Left Hand Side, including next/init .  */

      /*print_node(stdout,car(n));*/

      if(is_current_assignment(n))
        var = lhs = eval_struct_status(term_of_assignment(n), context, &status);
      else {
	var = eval_struct_status(term_of_assignment(n), context, &status);
	lhs = find_node(car(n)->type,var,NIL);
      }
      

      /* If the term is not an array variable, with indexes which are 
         program variables, check it. */
      if (status) {

          /* Perform check according to mode. */
          switch (mode) {
          case CHECK_MULTIPLE_ASSIGNMENTS: /* (and also check some other trivial errors)*/
            
            /* Find variable in symbol hash. If it's not there it is an error */
            if( (var_symbol_val = get_symbol(var)) == NIL)
                undefined(var);      
    
            /* If it's not a variable then it is a define so it is used already */
            if(symbol_type(var_symbol_val) != PROGRAM_VAR_SYMBOL) 
                redefining(var);
    
            /* Find out if this variable is multiply-assigned */
            if(find_assoc(assign_hash,lhs))
                multiple_assignment(lhs);
    
            /* Store the assignment in hashes */
            insert_assoc(assign_hash,lhs,find_node(CONTEXT,context,cdr(n)));
            insert_assoc(global_assign_hash,lhs,(node_ptr)yylineno);
    
            break;
    
          case CHECK_CIRCULAR_ASSIGNMENTS:
    
            check_circular_assign(lhs,context);
            break;
    
          case CALCULATE_OWNED_AND_CURRENT_ASSIGNED:
    
            /* Remember not to preserve this variable in this process */
            if( ! is_init_lhs(lhs) ) 
               c->owned = cons(eval_struct(var,context),c->owned );
    
            /* Remember for calculating def_ constant into dynamic variable. */
            if( is_current_lhs(lhs) )
               def_variables = cons(var,def_variables);
    
            break;
    
          default:
            break;
          }
      }
      /*      else {
	node_ptr matches = get_matching_vars(var,variables);
        printf("Matching vars");
        print_node(tlvstderr, var);
        print_list(matches);
	} */
      break;
    }
  default:
    catastrophe2("check_assign: type = %d",n->type);
  }
}
	

/**********************************************************************/

/* This structure is used to generate all sets of processes which can 
   run synchronously. For example, suppose we have a composition of the
   form ( A || B ) ||| ( C || D )  ( where || is ansychronous composition).
   Lets say we want to check if the same variable is assigned twice in
   the same transition. However, several transitions can occur, each 
   having a different set of assignments. In the example above there
   are four possible (synchornous transitions):
   A ||| C, A ||| D, B ||| C, B ||| D  . We have to check each of these
   four possibilities and see if there are conflicting assignments.

   The procedure "generate_all_actual_processes" generates all possible
   syncronous transitions. The set of processes which are participating
   in the current synchronous trnasition, are stored in the array "yield".
 */

/* yield is a stack. flag is just used by generate_all_actual_processes
   in order to produce all transitions. The components of the transition
   are stored in yield.arr . */
struct {
  int top;
  component_ptr arr[1000];
  int           flag[1000];
} yield;


/* Initialize yield. */
void init_yield(void)
{
   yield.top = 0;
}

/* Puch component onto yield. */
void push_yield(component_ptr c) 
{
   yield.arr[yield.top] = c;
   yield.flag[yield.top] = 0;  /* Initialize flag to 0 . */
   yield.top++;
}

void pop_yield(void)
{
   yield.top--;
}

/* A component is "expanded" if its subcomponents have already been
   added to the yield. */
#define expanded(i) (yield.flag[i] > 0)
#define expanded_1(i) (yield.flag[i] == 1)
#define expanded_2(i) (yield.flag[i] == 2)
#define expanded_both(i) (yield.flag[i] == 3)


#define mark1_expanded(i) yield.flag[i] = 1
#define mark2_expanded(i) yield.flag[i] = 2
#define markboth_expanded(i) yield.flag[i] = 3
#define unmark_expanded(i) yield.flag[i] = 0

#define CHECK_MULTIPLE_AND_CIRCULAR_ASSIGNMENTS 0
#define BUILD_TRANSITION 1


static bdd_ptr preserve_all_except_yield(component_ptr c)
{
  int i;

  /* Find  c in yield. */
  for (i=0 ; i < yield.top; i++ ) {
    if ( yield.arr[i] == c ) {
      if ( expanded( i ) ) {
         if ( expanded_1( i ) ) {
           bdd_ptr owned = id_of_var_list(c->c2->prop_owned);
           return and_bdd(owned, preserve_all_except_yield(c->c1));
         }
         else if ( expanded_2( i ) ) {
           bdd_ptr owned = id_of_var_list(c->c1->prop_owned);
           return and_bdd(owned, preserve_all_except_yield(c->c2));
         } 
         else /* Both are expanded. */ {
           return and_bdd(preserve_all_except_yield(c->c1),
                          preserve_all_except_yield(c->c2) );
         }
      }  
    }
  }
}


/* Export t, d, pres as dynamic variables (array items). */
void insert_t_d_pres(bdd_ptr t, bdd_ptr d, bdd_ptr pres)
{
    global_trans_num++;      

    insert_dynamic_var(array_key("_t",global_trans_num),t);
    insert_dynamic_var(array_key("_d",global_trans_num),d);
    insert_dynamic_var(array_key("_pres",global_trans_num),pres);
}


/* By actual processes, I mean to generate all combinations of
   processes which can execute synchronously in a single step. 
   It is possible to view the entire system as an asynchronous composition
   of such processes. The mode determines what action will be taken on the
   generated processes. */
static void generate_all_actual_processes(int mode)
{
  int cur_item;

  /* Find an item in yield, which is composed of other components, yet
     has not been expanded. */
  for ( cur_item = yield.top - 1; 
        cur_item >= 0 && 
          (yield.arr[cur_item]->composition_type == 0 || expanded(cur_item) );
        cur_item-- ) 
      ;

  if (cur_item < 0) {

    /* All components in yield have been expanded, so the yield contains
       a set of components which can run synchronously. Now we
       can perform an appropriate check. */

    switch (mode) {
  
    case CHECK_MULTIPLE_AND_CIRCULAR_ASSIGNMENTS: 
      {
        /* Go over all modules (which are a single process and check the assign sections) */
        int i;

        if(verbose)fprintf(tlvstderr,"checking for multiple assignments\n");
        for (i=0; i<yield.top; i++) 
            check_assign(yield.arr[i]->assign, NIL, yield.arr[i], 0);


        if(verbose)fprintf(tlvstderr,"checking for circular assignments\n");
        for (i=0; i<yield.top; i++) 
            check_assign(yield.arr[i]->assign, NIL, yield.arr[i], 1);

        clear_hash(assign_hash);
        break;
      }

    case BUILD_TRANSITION:
      {
        int i;
        bdd_ptr next_bdd = save_bdd(ONE);
        bdd_ptr curr_bdd = save_bdd(ONE);
        bdd_ptr id_of_owned = save_bdd(ONE);
        bdd_ptr pres;
  
        for (i=0; i< yield.top ; i++) {

           /* Calculate next() and TRANS. */
          and_it_in(&next_bdd, eval(yield.arr[i]->trans, NIL));
          and_it_in(&next_bdd, eval_type(yield.arr[i]->assign, NIL, NEXT));

           /* Calculate current assignments. */
          and_it_in(&curr_bdd, eval_type(yield.arr[i]->assign, NIL, CURRENT));

          /* Calculate preservation. */
          and_it_in(&id_of_owned, save_bdd(id_of_var_list(yield.arr[i]->prop_owned)));
        }

        /* yield.arr[0] is the root component. */
        pres = save_bdd( forsome(id_of_owned, 
                                 preserve_all_except_yield(yield.arr[0])));

        release_bdd(id_of_owned);

        insert_t_d_pres(next_bdd, curr_bdd, pres);
        break;
      }
    }

  } 
  else if (yield.arr[cur_item]->composition_type == ASYNCHCOMP) {

    /* Expand an asynchronously composed component. */

    /* Recursively generate yield including first component. */
    mark1_expanded(cur_item);
    push_yield( yield.arr[cur_item]->c1 );
    generate_all_actual_processes(mode);
    pop_yield();

    /* Recursively generate yield including second component. */
    mark2_expanded(cur_item);
    push_yield( yield.arr[cur_item]->c2 );
    generate_all_actual_processes(mode);
    pop_yield();

    unmark_expanded(cur_item);
  }
  else if (yield.arr[cur_item]->composition_type == SYNCHCOMP) {

    /* Expand a synchronously composed component. */

    /* Recursively generate yield including both component. */

    markboth_expanded(cur_item);

    push_yield( yield.arr[cur_item]->c1 );
    push_yield( yield.arr[cur_item]->c2 );
    generate_all_actual_processes(mode);
    pop_yield();
    pop_yield();

    unmark_expanded(cur_item);
  }
}


static void visit_all_actual_processes(fts f, int mode)
{
  /* Put the root component of f onto the yield. */
  push_yield(f->components);

  generate_all_actual_processes(mode);
  pop_yield();
}


/* This routine checks if an assignment of type "type" (which is
   either NEXT of SMALLINIT) is made to the variable v.
   If there is, an error is printed. This is called from
   check_program. */
static void check_assign_both(node_ptr v,int type, int curr_assign_lineno)
{
  node_ptr v1 = find_node(type,v,NIL);

  int lineno2 = (int)find_assoc(global_assign_hash,v1);

  if(lineno2){
    yylineno = curr_assign_lineno;
    err_node = NIL;
    start_err();
    fprintf(tlvstderr,"assigned ");
    print_node(tlvstderr,v);
    fprintf(tlvstderr,", line %d: assigned ", lineno2);
    print_node(tlvstderr,v1);
    finish_err();
  }
}


/* Check for colliding assignments (across the entire system). 
   A variable is collidingly assigned if 
   it has both current assignment and also either init() or NEXT (even
   if these are in different processes) . */
static check_system_colliding_assignments(fts f)
{
  node_ptr l;

  /* Loop over all variables */
  for (l = f->variables; l; l = cdr(l)){

    node_ptr v = car(l);  /* v is the current variable in the list */

    /* Find out if current assignment of the variable in "v" exists. */
    int curr_assign_lineno = (int)find_assoc(global_assign_hash,v);

    /* If a current assignment exists then a NEXT or SMALLINIT cannot
       exist. This is a colliding assignment error. The following just
       checks whether a NEXT or SMALLINIT assignment exists. If it does,
       an error is printed. */
    if(curr_assign_lineno){
      check_assign_both(v,NEXT,curr_assign_lineno);
      check_assign_both(v,SMALLINIT,curr_assign_lineno);
    }
  }

  clear_hash(global_assign_hash);
}


/* Check system for multiple, circular assignments, and assignments
   of different types ( combinational(x:=)/sequential(next(x):=)
   to the same variable. */
void check_system(fts f)
{
  /* Check multiple and circular assignments for all possible
     synchronous transitions. */
  visit_all_actual_processes(f, CHECK_MULTIPLE_AND_CIRCULAR_ASSIGNMENTS);

  /* Check that there are no variables which are assigned as current
     and also with either next() or init().  This procedure requires
     that global_assign_hash be updated properly. */
  check_system_colliding_assignments(f);
}

/* Depth first search traversal over components, which
   propogates the owned variables upwards. */
static void component_dfs(component_ptr c)
{
  bdd_ptr t, t1,t2;
  node_ptr temp;

  /* Recusion over component tree. */
  if (c->composition_type != 0) {
    component_dfs(c->c1);
    component_dfs(c->c2);
  }

  /* Evaluate list of owned to cannonical form. */
  c->owned = eval_struct_list_in_context(c->owned,NIL);

  /* Calcualte owned */
  check_assign(c->assign,NIL,c,CALCULATE_OWNED_AND_CURRENT_ASSIGNED);

  /* Calculate propogated owned, by collected owned of subcomponents
     and current component. */

  c->prop_owned = c->owned = sort_node(c->owned);

  /* Check for conflicts in owned variables in synchronous composition. */
  if (c->composition_type == SYNCHCOMP) {

    /* Check for conflict in owned. */

    if (temp = intersect_node(c->c1->prop_owned, c->c2->prop_owned) )
        variable_owned_by_two(temp);

    if (temp = intersect_node(c->owned, c->c2->prop_owned) )
        variable_owned_by_two(temp);

    if (temp = intersect_node(c->owned, c->c1->prop_owned) )
        variable_owned_by_two(temp);
  }

  if (c->composition_type !=0) 
      c->prop_owned = merge_node(merge_node(c->owned, c->c1->prop_owned),
                                 c->c2->prop_owned);
}

/* Compute transition relation of component into bdd variable t. */
static bdd_ptr build_total(component_ptr c)
{
  bdd_ptr t, t1, t2;

  fprintf(tlvstdout, "build_total..\n");

  /* Depth first processing of sons. */
  if (c->composition_type != 0) {
    fprintf(tlvstdout, "Handling sub-components..\n");
    /* Empty components (which are asynchronously composed) are interpreted
       as ZERO because otherwise they would be one, and when disjuncted with
       the other async process the entire result would be ONE. */
    if (c->composition_type == ASYNCHCOMP && empty_component(c->c1))
      t1 = save_bdd(ZERO);
    else
      t1 = build_total(c->c1);

    if (c->composition_type == ASYNCHCOMP && empty_component(c->c2))
      t2 = save_bdd(ZERO);
    else
      t2 = build_total(c->c2);
  }
  else
    fprintf(tlvstdout, "No sub-components.\n");

  /* Local calculations. */
  t = eval(c->trans, NIL);
  and_it_in(&t, eval_type(c->assign, NIL, NEXT_OR_CURRENT));

  /* Combine local computations with computations of sons. */

  if (c->composition_type == SYNCHCOMP) {
    fprintf(tlvstdout, "  synchronous composition\n");
    and_it_in(&t,t1);
    and_it_in(&t,t2);
  }
  else if (c->composition_type == ASYNCHCOMP) {
    fprintf(tlvstdout, "  asynchronous composition\n");
    if (t != ONE)
      catastrophe("t!=ONE in asynchronous component");

    release_bdd(t);

    t = save_bdd(or_bdd(and_bdd(t1, preserve(c->c2 , c->c1)),
                        and_bdd(t2, preserve(c->c1 , c->c2))));
    release_bdd(t1);
    release_bdd(t2);
  }
  else
    fprintf(tlvstdout, "  no composition\n");
  return t;
}

/* Build one process which starts from component c.
   The t, d, and pres components are calculated for each component. */
static void build_process(component_ptr c) 
{
  /* Depth first processing of sons. */
  if (c->composition_type !=0) {
      build_process(c->c1);
      build_process(c->c2);
  }
   
  /* Local calculations. */
  c->prop_t = eval(c->trans, NIL);
  and_it_in(&c->prop_t, eval_type(c->assign, NIL, NEXT));
  c->prop_d = eval_type(c->assign, NIL, CURRENT);

  /* Combine local computations with computations of sons. */
  /*  if ( empty_component(c->c1)*/

  if (c->composition_type == SYNCHCOMP) {
    /* All second parameters are released... */
    and_it_in(&c->prop_t, c->c1->prop_t);
    and_it_in(&c->prop_t, c->c2->prop_t);

    and_it_in(&c->prop_d, c->c1->prop_d);
    and_it_in(&c->prop_d, c->c2->prop_d);
  }
  else if (c->composition_type == ASYNCHCOMP) { 

    /* If we reached this point, then this asynchronous component was
       not generated by a "process" keyword, but by asynchronous composition
      in a "COMPOSED" section of the smv file. Such sections should not have
      any transition of their own, but should only combine the transition of
      their sons. So if c has a transition in it, then its a bug. */
    if (c->prop_t != ONE || c->prop_d != ONE)
      catastrophe("t!=ONE or d!=ONE in asynchronous component");

    release_bdd(c->prop_t);     
    c->prop_t = save_bdd(
                   or_bdd(and_bdd(and_bdd(c->c1->prop_t, c->c1->prop_d), 
                                  preserve(c->c2, c->c1)),
                          and_bdd(and_bdd(c->c2->prop_t, c->c2->prop_d), 
                                  preserve(c->c1, c->c2))
                         )
                        ); 

    release_bdd(c->c1->prop_t);
    release_bdd(c->c1->prop_d);

    release_bdd(c->c2->prop_t);
    release_bdd(c->c2->prop_d);
  }

  if (generate_formulas) {

      /* Local calculations. */
      c->prop_t_F = eval_F(c->trans, NIL);
      c->prop_t_F = and_F(c->prop_t_F, eval_type_F(c->assign, NIL, NEXT));
      c->prop_d_F = eval_type_F(c->assign, NIL, CURRENT);

      /* Combine local computations with computations of sons. */
      /*  if ( empty_component(c->c1)*/

      if (c->composition_type == SYNCHCOMP) {
        /* All second parameters are released... */
        c->prop_t_F = and_F(c->prop_t_F, c->c1->prop_t_F);
        c->prop_t_F = and_F(c->prop_t_F, c->c2->prop_t_F);

        c->prop_d_F = and_F(c->prop_d_F, c->c1->prop_d_F);
        c->prop_d_F = and_F(c->prop_d_F, c->c2->prop_d_F);

      }
      else if (c->composition_type == ASYNCHCOMP) 
        /* c->prop_t_F and c->prop_d_F should be NIL, so just combine sons. */
        c->prop_t_F = find_node(OR,
                              and_F( and_F(c->c1->prop_t_F, c->c1->prop_d_F), 
                                     preserve_F(c->c2, c->c1) ),
                              and_F( and_F(c->c2->prop_t_F, c->c2->prop_d_F), 
                                     preserve_F(c->c1, c->c2) )
                             ); 
  }
}

/* Returns preservation of all owned variables except those of component c
  ( and his sons) */
static bdd_ptr preserve_all_except_c(component_ptr root, component_ptr c)
{
  if (root==c)
    return ONE;
  else if (root->composition_type == ASYNCHCOMP) 
    return and_bdd(preserve_all_except_c(root->c1,c),
                   preserve_all_except_c(root->c2,c));
  else
    return id_of_var_list(root->prop_owned);
}


/* Returns preservation of all owned variables except those of component c
  ( and his sons) */
static node_ptr preserve_all_except_c_F(component_ptr root, component_ptr c)
{
  if (root==c)
    return NIL;
  else if (root->composition_type == ASYNCHCOMP) 
    return and_F(preserve_all_except_c_F(root->c1,c),
                 preserve_all_except_c_F(root->c2,c));
  else
    return id_of_var_list_F_without_b(root->prop_owned,c->prop_owned);
}

/* This is like build_total, but it tries to simulate the way tlv
   used to create transition systems. The number of transitions
   created is the number of "upper level" asynchrously composed processes.

   If these processes do not have as sons other asynchronous processes,
   then it is possible to correctly generate the t,d,pres components. 

   The procedure recursively goes down the tree of components
   while they are composed asynchronously. It then produces 
   transitions for non empty components. */
static void build_processes(fts f, component_ptr c)
{
  if (c->composition_type == ASYNCHCOMP) {
     build_processes(f,c->c1);
     build_processes(f,c->c2);
  }
  else if (!empty_component(c)) {
    /* Compute preservation. Preserve all variables which are assigned to 
       by other processes, except variables which process c assigns.
       If this is run after "component_dfs" is executed, then the
       variables process c owns, includes all its sons.*/
     bdd_ptr pres = 
       save_bdd( forsome(id_of_var_list(c->prop_owned),
                         preserve_all_except_c(f->components,c))
                );

     /* compute t,d of component c. */
     build_process(c);

     /* Export into _t, _d, _pres dynamic arrays. */
     insert_t_d_pres(c->prop_t, c->prop_d, pres);

     if ( generate_formulas ) {
       node_ptr pres_F = preserve_all_except_c_F(f->components, c);
       insert_parse_tree(array_key("_t_F",global_trans_num),
                         and_F(and_F(c->prop_t_F, c->prop_d_F),pres_F) );
     }
  }
}



/* This is the main routine in the second pass. (The first
    pass is the instantiation done by "system_by_name").
   This is the part which actually generates the transition
   as dynamic variables.

 There are three ways to do this second pass:
   1. Compute total by traversing the component tree recursively.
   2. Reconstruct the way the transition was calculated in old tlv's.
      Construct transitions only for top asynchronous processes.
      This can be done by traversing only the higher parts of the
      component tree, and computing the transition of each asycnronous part by
      dfs from there.
   3. Compute transitions corresponding to all actual processes by
      using "generate_all_actual_processes".

   Currently, both methods 1 and 2 are implemented. To implement 3
   one has to modify generate_all_actual_processes by adding the section
   after BUILD_TRANSITION and call it appropriately.
   */
void second_pass(fts f)
{
  int num_of_transitions;

  /* Calculate owned. */
  component_dfs(f->components);

  switch (disj_amount) {
  case 0: {
    /* Build a single transition. */
    bdd_ptr t = build_total(f->components);

    num_of_transitions = 1;

    /* Export transition as dynamic variables. */
    insert_t_d_pres(t, save_bdd(ONE), save_bdd(ONE));
    break;
  }
  case 1:
    num_of_transitions = global_trans_num;

    /* Build several transitions, according to the amount of
       outer asynchronous compositions. */
    build_processes(f, f->components); /*build_fts(f); */

    /* Compute the number of transitions this system consists of. */
    num_of_transitions = global_trans_num - num_of_transitions;
    break;
  case 2:
    visit_all_actual_processes(f, BUILD_TRANSITION);
    break;
  }

  /* Put the number of transitions found in symbol table : _tn[] */
  insert_dynamic_var(array_key("_tn",FTS_NUM(f)),
                     save_bdd( leaf_bdd(find_NUMBER_node(num_of_transitions))));
}

/**********************************************************************
  read_variable_list_from_file
  read_order_and_allocate_bdd_variables
 **********************************************************************/

node_ptr read_variable_list_from_file(char *fname)
{
  node_ptr var_list = NIL;
  extern char do_prompt;
  char old_do_prompt = do_prompt;
 
  int token;

  open_input(fname); /* Open input file */

  /* Do not get input using gnu readline, when using yylex. */
  do_prompt = 2;

  token = yylex();

  /* Loop which reads variable names from file and adds them to 
     the list "var_list".
     The external loop reads tokens from the input file. */
  while(token){

    node_ptr var = NIL;

    /* Read an ATOM ( a variable name ) */
    while(1){
      if(token != ATOM) {
        do_prompt = old_do_prompt;
        rpterr("syntax error");
      }
      var = find_node(DOT,var,find_atom(yylval.node));
      token = yylex();
      if(token != DOT)
        if (token == LB)
         {
          token = yylex();
          if ( token != NUMBER )
            {
             do_prompt = old_do_prompt;
             rpterr("syntax error: Array index must be constant number in order file!");
            }
          else
           {
              int i;

              i = yylval.node->left.inttype;
              var = find_node(ARRAY,var,find_NUMBER_node(i));

              token = yylex();
              if(token != RB)
                {
                 do_prompt = old_do_prompt;
                 rpterr("syntax error: No right bracket in order file!");
                }

              token = yylex();
              if(token != DOT)
                break;
           }
          } 
        else
          break;
      token = yylex();
    }
    /* Add variable to end of list */
    var_list = cons(var,var_list);
  }

  do_prompt = old_do_prompt;

  close_input();

  /* Put the list of var_list in the correct order and return it */
  return reverse(var_list);
}


/* Write a list of variables to a file. This is usually an order file . */
void write_var_list_to_file(node_ptr variables, char *fname)
{
  node_ptr l;
  FILE *stream;

  stream = fopen(fname,"w");

  for(l = variables; l; l = cdr(l))
  {
    fprint_node(stream, car(l));
    fprintf(stream,"\n");
  } 

  fclose(stream);
}

void read_order_and_allocate_bdd_variables(void)
{
  extern char *input_order_file;

  /* Save list of all variables in program in "orig_variables" */
  node_ptr orig_variables = variables;

  node_ptr l = variables;

  /* Read order from file (if requested in command line) */
  if (input_order_file)
    variables = read_variable_list_from_file(input_order_file);

  /* This loop does certain checks on all variables and adds a bdd
     to all variables in the "symbol_hash" */
  for (l = variables; l; l = cdr(l)) {
    node_ptr n = car(l);

    /* Check if the variable is in the symbol_hash (it should be) */
    node_ptr q = get_symbol(n);
    if (!q || symbol_type(q) != PROGRAM_VAR_SYMBOL) {
      start_err();
      indent_node(tlvstderr, "unknown variable in order file :", n, "");
      finish_err();
    }

    /* Check if the left son of the variable node is empty.
       If is not then it appeared twice in the input order */
    if (has_bdd(q)) {
      start_err();
      indent_node(tlvstderr, "variable appears twice in order file :", n, "");
      finish_err();
    }
    if (verbose > 1) {
      print_node(tlvstderr, n);
      fprintf(tlvstderr, ":\n");
    }

    /* Add bdd to left son of variable node in symbol_hash. */
    update_bdd(q, save_bdd(scalar_var(get_program_var_type(q))));
  }

  /* Loop which checks that all the variables appear in the ordering. */
  /* If not then this is an error.                                    */
  for (l = orig_variables; l; l = cdr(l)) {
    node_ptr n = car(l);
    node_ptr q = get_symbol(n);

    /* This should never happen (a previously detected variable should
       always appear in the symbol hash ( and as a VARiable ) */
    if (!q || symbol_type(q) != PROGRAM_VAR_SYMBOL)
      catastrophe("read_order: orig_variables");

    /* If there is a left branch then this variable was in the order file */
    if (!has_bdd(q)) {
      start_err();
      indent_node(tlvstderr, "not in order file: ", n, "");
      finish_err();
    }
  }

  /* Its important to do this right after the variables have been
     created because any subsequent procedures which manipulate
     bdds may trigger reordering which uses the array created by
     the following routine. */
  set_var_names();
}

/***********************************************************************/


/* Install constants like :

    _vars - all current state variables in bdd (i.e. variables of current state )
    _id   - all variables preserve their values 

*/
void install_constants(fts f)
{
  /* Insert _vars[] */
  bdd_ptr vars = save_bdd(calc_list_support(f->variables));
  insert_dynamic_var(array_key("_vars",FTS_NUM(f)),vars);

  /* Insert _id[] */
  f->id = save_bdd(id_of_var_list(f->variables));
  insert_dynamic_var(array_key("_id",FTS_NUM(f)),f->id);
}

void install_temporal_definitions(fts f)
{
  node_ptr current = f->ltl_list;
  int ltl_n = 0;

  while (current) {
    node_ptr pair = car(current);
    node_ptr name = car(pair);
    node_ptr ltl = cdr(pair);

    /* Create dynamic variables.  There are two variables (per iteration).
       Both are parse tree variables.

       ltl_var[f][i]  ltl_exp[f][i]. 

       where f is the number of the fts, and i is an additional index
       for all the formulas inside a single system. 
       ltl_var is for the principle variable, and ltl_for is for the
       formula itself. 
    */  

    ltl_n++;

    insert_parse_tree(double_array_key("_ltl_var", FTS_NUM(f), ltl_n),
                      name );
    insert_parse_tree(double_array_key("_ltl_exp", FTS_NUM(f), ltl_n),
                      ltl );
    
  
    current = cdr(current);  
  }

  /* In addition we also export the varialbe _ltl_n[f], which states
     how many formulas does this fts have. */
  /* Insert _sn */
  insert_dynamic_var(array_key("_ltl_n", FTS_NUM(f)),
                     save_bdd( leaf_bdd(find_NUMBER_node(ltl_n)) )  );

}

/* For each kind, create an array item,
   where the name of the array is the name if the kind, and the index
   is the number of the transition system. This array item contains
   the bdd which is the support of all variables of that kind. */
void install_kinds(fts f)
{
    node_ptr l, v;

    bdd_ptr set;

    /* Loop over all kinds. For each kind create an entry. */
    LOOP_OVER_ALL_KINDS(l) {

        node_ptr curr_kind = car(l);

        set = ONE;

        /* Loop over all variables for which kinds were specified,
           and create in variable "set" the support bdd of all variables
           of kind "curr_kind". */
        for (v = f->kinds; v; v = cdr(v)) {
            if ( strcmp(atom_to_string(curr_kind), atom_to_string(car(car(v)))) == 0 )
               set = and_bdd(set, 
                             support_bdd( bdd_of(get_symbol(cdr(car(v)))) ) 
                            );
        }

       /* Insert set as dynamic variable. */
       insert_dynamic_var(array_key_from_node(curr_kind,FTS_NUM(f)),
                          save_bdd(set));
    }
}

/* Install constants like :

    _vars - all current state variables in bdd (i.e. variables of current state )
    _id   - all variables preserve their values 
    
    _i    - Global initial condition.
    
    tn    - number of transitions.
    
    nj,nc - number of justice and compassion conditions.

    This is used for quatification.
    _def  - all defined variables (variables whose assignement is current )*/
void install_global_constants(bdd_ptr vars, bdd_ptr init, 
                              int tn, int nj, int nc)
{
  static bdd_ptr def ;  /* Bdd of variables with current assignments */


  /* Insert _vars */
  insert_dynamic_var(var_key("_vars"),vars);

  /* Insert _i */
  insert_dynamic_var(var_key("_i"),init);

  /* Insert _tn */
  insert_dynamic_var(var_key("_tn"),
           save_bdd( leaf_bdd(find_NUMBER_node(tn)) )  );

  /* Insert jn */
  insert_dynamic_var(var_key("_jn"),
           save_bdd( leaf_bdd(find_NUMBER_node(nj)) )  );

  /* Insert cn */
  insert_dynamic_var(var_key("_cn"),
           save_bdd( leaf_bdd(find_NUMBER_node(nc)) )  );


  insert_dynamic_var(var_key("_id"),save_bdd(global_id) );


  /* Calculate def */
  def = calc_list_support(def_variables);
  def = and_bdd(def,r_shift(def));
  insert_dynamic_var(var_key("_def"),save_bdd(def) );
}


/* This process build justice arrays. The list given in just
   is a list of expressions (they should hold infinitely often in 
   a program according to the definition given in class). */
int build_justice_array(fts f)
{
  static int jn = 0;
  int system_jn = 0;

  /* Search in just list */
  node_ptr j = f->just;
  while (j)
   {
    jn++;  system_jn++;

    /* Insert value into symbol hash */
    insert_dynamic_var(array_key("_j",jn),eval(car(j),NIL) );

    if (generate_formulas) 
        insert_parse_tree(array_key("_j_F",jn),  eval_F(car(j),NIL) );
    

    j = cdr(j);
   }

  /* Insert size of just array in variable _jn */
  insert_dynamic_var(array_key("_jn",FTS_NUM(f)),
                save_bdd( leaf_bdd(find_NUMBER_node(system_jn)) ) ); 

  return jn;
}



/* The list of compassion requirements each compassionate pair
   is two expressions (p,q). According to Amir's definition
   in class an infinite path is compassionate if it contains
   either finitly many p-states or inifinitly many q-states. */
int build_compassion_arrays(fts f)
{
  static int cn = 0;

  /* Scan compassion list */
  node_ptr c = f->compassion;
  int system_cn = 0;

  while (c)
   {
    cn++;
    system_cn++;

    /* Insert values into symbol hash */

    insert_dynamic_var(array_key("_cp",cn),
                       eval(car(car(c)),NIL) );

    insert_dynamic_var(array_key("_cq",cn),
                       eval(cdr(car(c)),NIL) );

    if (generate_formulas) {
        insert_parse_tree(array_key("_cp_F",cn),
                           eval_F(car(car(c)),NIL) );

        insert_parse_tree(array_key("_cq_F",cn),
                           eval_F(cdr(car(c)),NIL) );
    }

    c = cdr(c);
   }

  /* Insert size of compassion array in variable _cn */
  insert_dynamic_var(array_key("_cn",FTS_NUM(f)),
                     save_bdd( leaf_bdd(find_NUMBER_node(system_cn)))
                    ); 

  return cn;
}

/* Evaluate bdd of initial condition (but only the part stated using "init()"
   assignments inside the ASSIGN section), by recursively traversing all the 
   components. */
static bdd_ptr eval_init_from_components(component_ptr c)
{
  bdd_ptr b = eval_type(c->assign,NIL,INIT);

  /* If this component has sons, then traverse them. */
  if (c->composition_type !=0) {
    and_it_in(&b,eval_init_from_components(c->c1));
    and_it_in(&b,eval_init_from_components(c->c2));
  }

  return b;
}


static node_ptr eval_init_from_components_F(component_ptr c)
{
  node_ptr b = eval_type_F(c->assign,NIL,INIT);

  /* If this component has sons, then traverse them. */
  if (c->composition_type !=0) {
    b = and_F(b, eval_init_from_components_F(c->c1));
    b = and_F(b, eval_init_from_components_F(c->c2));
  }

  return b;
}


/* Build bdd of initial condition of system. */
static bdd_ptr build_init(fts f)
{
  bdd_ptr init;

  /* Translate expressions of INIT sections to bdd */
  if (verbose) print_in_process("evaluating INIT statements",NIL);
  init = eval(f->init,NIL);

  /* Add to init only assignments which start with "init()" */
  if(verbose)print_in_process("evaluating init() assignments",f->components->context);
  and_it_in(&init, eval_init_from_components(f->components));

  if(verbose)fprintf(tlvstderr,
		     "size of global initial set = %g states, %d BDD nodes\n",
		     count_bdd(init),size_bdd(init));

  /* Find the init bdd and insert into symbol table as dynamic var : _i[] */
  /* It is important to save_bdd again, because the "init" returned
     in the next statement can be released by the calling function. */
  insert_dynamic_var(array_key("_i",FTS_NUM(f)), save_bdd(init));

  if (generate_formulas) {
     node_ptr init_F = and_F(f->init, eval_init_from_components_F(f->components));
     insert_parse_tree(array_key("_i_F",FTS_NUM(f)), init_F);
  }

  return init;
}


/* This is an old routine. I don't think it is called by anybody anymore.

Returns number of transitions. */
static int build_fts(fts f)
{
  node_ptr context, assign_expr, trans_expr;
  bdd_ptr trans,defined;

  int system_trans_num = 0;

    /* Print process name */
    fprintf(tlvstderr,"Finding transition of ");
    /*    if ( context == NIL )
      fprintf(tlvstderr,"main");
    else
      print_node(tlvstderr,context); */

    /* Evaluate TRANS sections into "trans" */
    if(verbose)print_in_process("evaluating TRANS statements",context);
    trans = eval(trans_expr,NIL);

    /* Evaluate next() assignments of current process into "trans" */
    if(verbose)print_in_process("evaluating next() assignments",context);
    and_it_in(&(trans),eval_type(assign_expr,NIL,NEXT));

    if(verbose)fprintf(tlvstderr,
			 "size of transition relation = %d  BDD nodes\n",
			 size_bdd(trans));

    /* Put normal assignment bdd into defined */
    if(verbose)print_in_process("evaluating normal assignments",context);
    defined = save_bdd(eval_type(assign_expr,NIL,CURRENT));

    mygarbage();

    if (trans == ONE && defined == ONE) {
       fprintf(tlvstderr," ... This transition is empty\n");
    }
    else
     {
       bdd_ptr not_pres;

       fprintf(tlvstderr," ... This transition is named _t[%d],_d[%d]\n",
                         global_trans_num,global_trans_num);

       /*                     */
       /* Insert preserve bdd */
       /*                     */
        {
           node_ptr l;  /*       = car(curr_owned) ;*/
         not_pres=ONE; 
         while(l) {
            node_ptr v = car(l);  /* v is the current variable in the list */

            bdd_ptr r = eval(v,NIL); release_bdd(r);  /* Find bdd of v */
            r = support_bdd(r);
            not_pres = and_bdd(not_pres,and_bdd(r,r_shift(r)));

            l = cdr(l);
          }

         system_trans_num++;                             
         insert_t_d_pres(trans, defined, save_bdd(forsome(not_pres,f->id)) );
        }
     }

  return system_trans_num;
}




/****************************************************************/


/* Initialiaze hash tables which are used in this file. */
void init_hashes_if_needed(void)
{
  if (!assign_hash) {
      assign_hash = new_assoc();
      global_assign_hash = new_assoc();
  }
}


/*****************************************************************/
/*                    Main procedure of symbols.c                */
/*****************************************************************/


/* void smv2fts(node_ptr *varset) */
void smv2fts(node_ptr *varset)
{
  extern node_ptr parse_tree; /* Parse tree returned by yyparse */

  settime_command();

  parse_tree = reverse(parse_tree);

  init_yield();

  /* Initialize hash tables */
  init_hashes_if_needed();

  /************************************************************
     FIRST PASS
  ************************************************************/
  variables = instantiation(parse_tree);

  /************************************************************
     Allocate bdds.
  ************************************************************/

  /* Read order of variables from file (for bdd order) and create the bdd
     variables. */
  read_order_and_allocate_bdd_variables();

  output_order();   /* Print the variable order into a file (if requested
                       in command line.) */

  /************************************************************
     SECOND PASS
  ************************************************************/

  /* Number the fts, and set dynamic variable _sn (number of systems) */
  number_fts();

  global_id = save_bdd(id_of_var_list(variables));

  {
    fts f;
    int cn = 0, jn = 0; /* Total number of fairness conditions. */

    /* bdd of INIT expr + ASSIGN init(v) := expr */
    bdd_ptr global_init = save_bdd(ONE);

    /* Loop which translates data about each system into an fts. */
    LOOP_OVER_FTS_LIST(f) {

      bdd_ptr system_init;

      fprintf(tlvstdout, "System #%d:\n", FTS_NUM(f));

      /* Check for errors (in ASSIGN section) */
      check_system(f);

      /* Build transition relation. */
      second_pass(f);

      /* Calculate and set variables : _vars[], _id[] */
      install_constants(f);

      install_kinds(f);

      /* Build the (global variable) "init" bdd using the init_expr
         (which contains all the INIT sections and the (init)
         assignments.) */
      system_init = build_init(f);
      /* warning: system_init is released. */
      and_it_in(&global_init, system_init);

      /* Build fairness arrays. */
      jn = build_justice_array(f);
      cn = build_compassion_arrays(f);

      /* Install table of equivalences between temporal formulas
         and their primaray variables. */
      install_temporal_definitions(f);
    }
    global_vars = save_bdd(calc_list_support(variables));
    install_global_constants(global_vars,global_init,global_trans_num,jn,cn);
  }
  print_usage(tlvstdout);
  print_bdd_usage(tlvstdout);
}

void empty_fts(void)
{
  init_hashes_if_needed();
  global_vars = save_bdd(ONE);
  global_id = save_bdd(ONE);
}
