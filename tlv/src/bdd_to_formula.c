/* Routines for converting a bdd back to a formula and printing it. */

#include <stdio.h>
#include <storage.h>
#include <mystring.h>
#include <node.h>
#include <hash.h>
#include <bdd.h> 
#include <assoc.h>
#include <util_err.h>
#include <y.tab.h>
#include "script.h"
#include "symbols.h"
#include "eval.h"

/* print_hash is used differntly in different places.
   It used in one way in bdd_to_formula_aux, and in another
   way (its main purpose) in the rest of the functions.

   The print_hash plays a central role in printing out the formula.
   One of the main ways the formula is printed succinctly is by identifying
   common subformula. This is done by having the subformula be
   a hash key in this hash. The value is the way the subformula will
   be printed out. Most formulas will be printed out as themselves, but
   some will be printed out as definitions (i.e. macros). The defintion
   of these macros is printed before the main formula is printed. */
static hash_ptr print_hash;



/* Graph routines, for depndancy between macros */




typedef struct {
  int id;
  struct graph_it *next;
  struct graph_it *prev;
} bi_link;

#define ROW 0
#define COL 1
typedef struct graph_it {
  bi_link link[2];
} graph_item;


typedef struct {
  node_ptr id;
  graph_item *link;
} row_col_holder;

typedef struct {
  int size;
  row_col_holder *index[2]; /* Points to rows, columns */
  hash_ptr index_hash;
} graph;

graph gr;


/* Returns size of graph. */
int init_graph(node_ptr defs) {
  int i;
  static first_time = 1;

  gr.size = length(defs);

  /* Allocate structures to hold information about rows and columns. */
  gr.index[ROW] = (row_col_holder *)malloc(gr.size * sizeof(row_col_holder));
  gr.index[COL] = (row_col_holder *)malloc(gr.size * sizeof(row_col_holder));

  if (first_time) {
    gr.index_hash = new_assoc();
    first_time = 0;
  }

  /* Fill structures with data. */
  for (i=0;i<gr.size; i++) {
    gr.index[COL][i].id = gr.index[ROW][i].id = cdr(car(defs));
    gr.index[COL][i].link = gr.index[ROW][i].link = 0;

    insert_assoc(gr.index_hash,cdr(car(defs)),(node_ptr)i);

    defs = cdr(defs);
  }

  return gr.size;
}

void clear_graph(void) {

  free(gr.index[0]);
  free(gr.index[1]);
  
  clear_hash(gr.index_hash);
}

int find_index(node_ptr id)
{ 
  return (int)find_assoc(gr.index_hash, id);
}

void add_edge(node_ptr from, node_ptr to)
{
  int from_i = find_index(from);
  int to_i = find_index(to);
  int index_type;

  graph_item *item = (graph_item *)malloc(sizeof(graph_item));

  item->link[ROW].id = from_i;
  item->link[COL].id = to_i;

  for (index_type= 0; index_type < 2; index_type++)
    {
      int other_type = 1 - index_type;
      int id = item->link[index_type].id;
      int other_id = item->link[other_type].id;

      graph_item *link = gr.index[index_type][id].link;
      graph_item *prev = 0;

      item->link[index_type].next = item->link[index_type].prev = 0;

      if (link) {
 
        /* Search for place to insert item in list. */
        while (link && link->link[other_type].id < other_id ) {
          prev = link;
          link = link->link[index_type].next;
        }

        /* Now we want to insert the item after prev. */

        /* If the id-s are equal then the edge is already in the
           graph, so be careful not to insert it. */
        if (!link || link->link[other_type].id > other_id ) {

          /* Link backwards. */
          if (prev) {
              /* Insert item after prev. */
              prev->link[index_type].next = item; 
              item->link[index_type].prev = prev;
              
          }
          else 
              /* Insert item as first item on the list */
              gr.index[index_type][id].link = item;      


          /* Link forwards. */
          if (link) {
            link->link[index_type].prev = item; 
            item->link[index_type].next = link;
          }

        }
        
      }
      else
        /* There are no items in the list, so just make the index point
           to the single item. */
        gr.index[index_type][id].link = item;
    }
}


void print_graph(void)
{
  int i;
  graph_item *link;

  /* Loop over rows. */
  for (i=0;i<gr.size; i++) {

    printf("\nrow (%i,%s):", i, gr.index[ROW][i].id->left.strtype);

    for (link = gr.index[ROW][i].link; link; link= link->link[ROW].next) {
      printf("(%i)", link->link[ROW].id );
    }
  }
}

mainn(int argc, char **argv)
{
  int i;
  node_ptr name, pair, defs = 0;
  char str[10];

  str[1] = 0;

  /* Create the list. */
  for (i =0;i<26 ; i++) {
    str[0] = i + 'a';
    name=find_node(DOT,NIL,string_to_atom(str));
    pair=find_node(LIST,NIL,name);
    defs=cons(pair,defs);
  }

  init_graph(defs);

  /* print menu in loop. */
  while(1) { 
    printf("1: add-edge, 2: remove-edges-to: 3: print\n");
    fgets(str,10,stdin);
  }

}


/* not needed... for now... */
void remove_edge_unused(node_ptr from, node_ptr to)
{
}

void remove_edges_to(node_ptr to)
{
   int to_i = find_index(to); 

   /* link: list of all items which go to "to" */
   graph_item *link = gr.index[COL][to_i].link;
   graph_item *prev = 0;
 

   /* Go over column list and free all links. */
   while (link) {

     int row_index = link->link[ROW].id;

     /* Disconnect link from row list. */

     if (link->link[ROW].prev && link->link[ROW].next ) 
     {
         /* Link is in the middle of the list. */
       link->link[ROW].prev->link[ROW].next = link->link[ROW].next;
       link->link[ROW].next->link[ROW].prev = link->link[ROW].prev;
     }

     else if (link->link[ROW].prev)
       /* Link is at the end of the list. */
       link->link[ROW].prev->link[ROW].next = 0;

     else if (link->link[ROW].next) {
       /* Link is at the beginning of the list. */
       link->link[ROW].next->link[ROW].prev = 0;
       gr.index[ROW][row_index].link = link->link[ROW].next;
     }
     else 
       /* This link is the only one on the row's list. */
       gr.index[ROW][row_index].link = 0;

     /* Advance along column list. */
     prev = link;
     link = link->link[COL].next;

     /* Free previous link. */
     free(prev);
   }
}


/* not needed... for now... */
int is_edge_unused(node_ptr from, node_ptr to)
{
}

int has_edge(node_ptr from)
{
  return gr.index[ROW][find_index(from)].link != 0;
}




/* Takes a list of formulas of the form (var = val -> Formula) and 
   builds a conjunction of those.   Applies some propositional
   simplification.  The list "l" is erased from memory. */
node_ptr conjunct_and_simplify(node_ptr l, node_ptr type)
{
  node_ptr true_node = find_node(TRUEEXP,NIL,NIL);
  node_ptr false_node = find_node(FALSEEXP,NIL,NIL);
  int n;
  node_ptr tmp=l, res=NIL;  /* res - result */

  /* Stage 1:
     First, collect all values with the same conclusion F.
     The result is the list "l" with possibly less conjuncts.
     Some of them remain the same, but some can be transformed to

       var in {val1,val2,...} -> Formula 
   */
  while(tmp) {
    node_ptr 
      expr=car(tmp),
      F = cdr(expr), /* The conclusion of the implication */
      var=car(car(expr)), /* The variable name */
      vals=cons(cdr(car(expr)),NIL), /* list of values for F - initially v */
      prev=tmp,
      tmp2=cdr(tmp); /* the remainder of the list */

    /* Now loop through the rest of the formulas and collect vals for the F */
    while(tmp2) {
      node_ptr 
	expr2=car(tmp2),
	F2 = cdr(expr2),
	val2=cdr(car(expr2));

      if(F==F2) {
	vals = cons(val2,vals); /* add the value to the list of vals */
	/* and remove it from the list of formulas */
	prev->right.nodetype=tmp2->right.nodetype;
	free_node(tmp2);
	tmp2=prev;
      }
      prev=tmp2;
      tmp2=cdr(tmp2);
    }
    /* Replace the current formula with a simplified one, if it simplifies */
    if(list_length(vals) > 1)
      tmp->left.nodetype=find_node(IMPLIES,find_node(SETIN,var,vals),F);
    /* if doesn't simplify, leave it unchanged */
    else free_list(vals);
    tmp=cdr(tmp);
  }

  
  /* Stage 2:
     Act according to the length of the list of conjuncts.
     The length cannot be zero.
     If n == 1 then the formula is simlified to F.
     Otherwise, try to perform boolean simplifications.
  */
  n=list_length(l);
  if(n==0) {
    catastrophe("conjunct_and_simplify: list_length(l) == 0");
  }
  else if(n==1) { /* formula is (x in type -> F): simplify to F */
    res = cdr(car(l));
    free_list(l);
    return(res);
  }
  /* If there are only two conjuncts (g1 -> FALSE) & (g2 -> F),
     then rewrite it to (g2 & F), or if F=true, then to (g2). */
  else if(n==2) {
    node_ptr c1=car(l), c2=car(cdr(l)),
             g1=car(c1), F1=cdr(c1),
             g2=car(c2), F2=cdr(c2),
             tmp3=NIL;

    if(F1==false_node)
      if(F2==true_node) tmp3=cons(g2,NIL);
      else tmp3=cons(find_node(AND,g2,F2),NIL);
    else if(F2==false_node) 
      if(F1==true_node) tmp3=cons(g1,NIL);
      else tmp3=cons(find_node(AND,g1,F1),NIL);
    /* No F is false, simplify only (g -> TRUE) */
    else if(F1==true_node) tmp3=cons(c2,NIL);
    else if(F2==true_node) tmp3=cons(c1,NIL);
    if(tmp3) {
      free_list(l);
      l=tmp3;
    }
  }
  /* If length >= 2 walk and simplify (g -> false) and (g -> true) */
  else if(n>2) {
    node_ptr *prev = &l;
    tmp=l;
    while(tmp) { /* Assume c = (g -> F) */
      node_ptr c=car(tmp), g=car(c), F=cdr(c),new=NIL;
      /* (g -> false) is replaces by (!g) */
      if(F==false_node) {
	new=g;
	if(new->type==EQUAL) 
            new = find_node(NOTEQUAL,car(new),cdr(new));
	else if(new->type==SETIN) 
            new = find_node(SETNOTIN, car(new),cdr(new));
	else new = find_node(NOT,new,NIL);
      }
      /* if it's (g -> true), then replace it by TRUE, which will later
	 be removed */
      else if(F==true_node) new=true_node;
      /* Now, if "new" has changed, substitute it for car(tmp), or
	 remove it if it's TRUE, and advance to the next conjunct. */
      if(new!=NIL)
	if(new==true_node) {
	  *prev=cdr(tmp);
	  free_node(tmp);
          if (*prev)
  	    tmp=cdr(*prev);
          else
            tmp=NIL;
	}
	else {
	  tmp->left.nodetype=new;
	  prev=&(tmp->right.nodetype);
	  tmp=cdr(tmp);
	}
      else {
	prev=&(tmp->right.nodetype);
	tmp=cdr(tmp);
      }
    }
  }

  /* Stage 3: for subformulas (x in/notin {...}) pick the shortest
     between the {...} and type-{...} */
  tmp = l;
  while(tmp) {
    node_ptr expr=car(tmp),g;
    if(expr->type==IMPLIES) g=car(expr);
    else g = expr;
    if(g->type==SETIN || g->type==SETNOTIN)
      if(list_length(cdr(g))*2 > list_length(type)) {
	node_ptr tmp2=list_minus(type,cdr(g));
	if(tmp2==NIL) catastrophe("conjunct_and_simplify: tmp2==NIL");
	free_list(cdr(g));
	if(cdr(tmp2)==NIL) {/* Change to equality */
	  if(g->type==SETIN) g->type=NOTEQUAL;
	  else g->type=EQUAL;
	  g->right.nodetype=car(tmp2);
	  free_list(tmp2);
	}
	else {
	  g->right.nodetype=tmp2;
	  if(g->type==SETIN) g->type=SETNOTIN;
	  else g->type=SETIN;
	}
      }
    tmp=cdr(tmp);
  }

  /* Now build the conjunction.  On the way, simplify (f->false) to (!f). */
  tmp=l;
  while(tmp) {
    if(res==NIL)res=car(tmp);
    else res = find_node(AND,res,car(tmp));
    tmp=cdr(tmp);
  }
  free_list(l);
  return(res);
}

/* This function transforms a bdd into a formula over the state variables.
   Here print_hash is used differntly than for the rest of 
   this file. The key is the bdd node, and the value is the formula.
   A bdd/formula is stored in the hash if we already generated
   a formula for this bdd. This is done so as to not regenrate formula
   for the same bdd. 
*/
node_ptr bdd_to_formula_aux(bdd_ptr d,
                            node_ptr vars, /* list of vars to consider */
                            int primed,
                            int phase)   /* 1 if deal with primed variable. */
{
  node_ptr true_node = find_node(TRUEEXP,NIL,NIL);
  node_ptr false_node = find_node(FALSEEXP,NIL,NIL);

  /* Check if this node already has a formula associated with it. */
  node_ptr tmp = find_assoc(print_hash,(node_ptr)d);
  
  node_ptr l = vars;
  node_ptr formula = true_node; /* will accumulate the result */

  /* Handle simple cases. */
  if(d==ZERO) return(false_node);
  /* if(d==ONE || vars==NIL) return(true_node); */
  if(d==ONE) return(true_node);

  /* Handle pathological cases. */ 
  if(ISLEAF(d)) catastrophe("bdd_to_formula_aux: ISLEAF(d)");
  if(vars == NIL) catastrophe("bdd_to_formula_aux: vars == NIL");

  /* if already computed, add to the list of shared defs and exit */
  if(tmp) return(tmp);
  /*{
    node_ptr pair=find_node(LIST,(node_ptr)d,tmp);
    if(!member(pair,*defs)) *defs=cons(pair,*defs);
    return(tmp);
  }*/
  else {
    node_ptr v = car(l); /* v is the current variable */

    /* The list of values for the var. type */
    node_ptr sym_val = get_symbol(v);
  
    node_ptr type;
    node_ptr flist = NIL; /* List of recursively computed formulas */
    int level;

    if(!sym_val) undefined(v);

    /* Find the level of the next var */
    if(cdr(l)) level = var_level(car(cdr(l)));
    else level = LEAFLEVEL;

    /* If the variable is not in the bdd, skip it. */
    if(GETLEVEL(d) >= level) 
       return bdd_to_formula_aux(d,cdr(l),primed,0);

    /* Otherwise go over all the values of that var */

    if(sym_val && symbol_type(sym_val) == PROGRAM_VAR_SYMBOL) {
      /* type_bdd = car(type); */
      type = get_program_var_type(sym_val);
    }
    else catastrophe("bdd_to_formula_aux: !type || type->type != VAR");


    /* The goal of this loop is to go over all values of the type
       of the current variable and generate conjuncts as follows:

        var = val1 -> formula1_over_variables_after_var_in_bdd_order     
        var = val2 -> formula2_over_variables_after_var_in_bdd_order     
        ...
     
        These conjuncts are put into the variable flist.

       Note that this totally ignores primed variables.
    */
    for(tmp=type; tmp; tmp = cdr(tmp)) {

      node_ptr val = car(tmp);  /* val is one value of the type. */
      bdd_ptr eq_bdd = eval(find_node(EQUAL,v,val),NIL);  /* Bdd of var = val */
      bdd_ptr subset;
      node_ptr temp;

      if (primed && phase)
        eq_bdd = r_shift(eq_bdd);

      if (!primed || phase) {
         /* Returns bdd which is what d is like when conjuncted with
            var = val, 
            however, the variable var does not appear in subset, only
            variables which come after var, in the bdd order. */
         subset = bdd_trim_to_level(and_bdd(d,eq_bdd),level);

         /* Recursively, obtain the formula corresponding to subset. */
         temp = bdd_to_formula_aux(subset,cdr(l),primed,0);
      }
      else {
         subset = forsome(support_bdd( bdd_of(sym_val)),and_bdd(d,eq_bdd));

         /* Recursively, obtain the formula corresponding to subset. */
         temp = bdd_to_formula_aux(subset,l,primed,1);
      }

      /* Construct the recursively computed conjunct */
      temp = find_node(IMPLIES,find_node(EQUAL, 
                                         ((primed && phase)?
                                             find_node(NEXT,v,NIL) : v),
                                         val),temp);

      /* Add formula to flist. */
      flist = cons(temp,flist);
    }

    /* Conjunct all the formulas and do some simplification
       relative to the current var type. */
    formula = conjunct_and_simplify(flist,type);
  }

  /* Associate the formula with the bdd d. */
  insert_assoc(print_hash,(node_ptr)d,formula);

  return(formula);
}

/* Returns true if the subformula "f" already exists
   in the list of pairs "defs" (f,name) */
int find_def(node_ptr f,node_ptr defs)
{
  while(defs) {
    if(car(car(defs))==f) return(1);
    defs=cdr(defs);
  }
  return(0);
}

/* Collects all significant repeated subexpressions into defs list.
   Assume that the formula is composed of AND, IMPLIES, (NOT)EQUAL,
   and SET(NOT)IN, and nothing else.  The rest are treated as atoms.

   All definition names have a name Xnnn where nnn is some number.
   Here, the parmater "n" contains the number of the next defintion. */

void collect_defs(node_ptr f, node_ptr *defs,
                  hash_ptr hash,
                  int *n)
{
  /* Check if subformula already exists in hash table */
  node_ptr tmp=find_assoc(hash,f);

  /* String of name of next definition (DEFINEs/ macros) */
  char str[32];

  if(tmp && !find_def(f,*defs)) { /* We've seen this formula, add it is not
                                     in defs, so add it to the defs */
    node_ptr name,pair;

    /* Generate a fresh name for a new definition. Into variable name. */
    do  {
      /* Generate string of name of new definition. */
      sprintf(str,"X%d",(*n)++);
      /* Put the name in the "main" context */
      name=find_node(DOT,NIL,string_to_atom(str));
    } 
    while (get_symbol(name)!=NIL); /* Loop until name does not exist
                                       already. */

    /* Save definition in hash table, just in case. However, 
       I don't think it is used anywhere. */
    /*    insert_symbol(name,find_node(PRINT,name,f));  */

    /* Add pair of (formula, defname) to defs list */
    pair=find_node(LIST,f,name);
    *defs=cons(pair,*defs);
  }
  else /*if ( !tmp )   NEW!! */ {
    /* Either we have not seen this subformula yet (i.e it is not
       recorded in "hash"),  or it is already in defs.
       I am not sure why the following code should be done if
       the formula is already in defs. However, if we have
       not seen the subformula yet, we recursively decsend into
       the formula to find shared subformulas in them. */
    switch(f->type) {
    case IMPLIES:
      collect_defs(cdr(f),defs,hash,n); break;
    case AND:
      collect_defs(car(f),defs,hash,n);
      collect_defs(cdr(f),defs,hash,n); break;
    default: return;
    }

    /* Insert the formula as its own printed representation.
       Only IMPLIES/AND formulas are inserted. */
    insert_assoc(hash,f,f);
  }
}

/* Traverses n (formula) recursively, substituting nodes hashed in print_hash
   for the variable names assigned to them in the hash.
   Assume that the formula is composed of AND, IMPLIES, (NOT)EQUAL,
   and SET(NOT)IN, and nothing else.  The rest are treated as atoms. 

   regist: boolen flag which is true if we should register the dependencies
   between macro definitions (X???) inside a hash table. 

   macro_name: Name of current macro.  This could be null if this routine
        is called for replacing shared nodes of the main formula. */
node_ptr replace_shared_nodes(node_ptr n,
                              hash_ptr hash,
                              int regist,
                              node_ptr macro_name)
{
  /* Check if formula exists in print_hash. */
  node_ptr tmp=find_assoc(hash,n);

  if(tmp) {
    /* Register that this macro depends on the macro named tmp. */
    if (regist)
       add_edge(macro_name,tmp);  

    /* Return replaced value */
    return tmp;
  }
  else {
    /* Try to replace recursively. */
    switch(n->type) {
    case IMPLIES:
      n->right.nodetype=replace_shared_nodes(cdr(n),hash, regist, macro_name);break;
    case AND:
      n->left.nodetype=replace_shared_nodes(car(n),hash, regist, macro_name);
      n->right.nodetype=replace_shared_nodes(cdr(n),hash, regist, macro_name);break;
    default: break;
    }
    return n;
  }
}

/* Does the same for the defs - they also can have shared terms */
void replace_shared_nodes_defs(node_ptr defs,
                               hash_ptr hash)
{
  while(defs) {
    /* Break definition into: f - formula, var - printed representation (i.e, X??). */
    node_ptr pair=car(defs), var=cdr(pair), f=car(pair);
    defs=cdr(defs);
    switch(f->type) {
    case IMPLIES:
      f->right.nodetype=replace_shared_nodes(cdr(f),hash, 1, var);break;
    case AND:
      f->left.nodetype=replace_shared_nodes(car(f),hash, 1, var);
      f->right.nodetype=replace_shared_nodes(cdr(f),hash, 1, var);break;
    default: break;
    }
  }
}


void sort_dependency(int def_len, node_ptr *defs) 
{
  node_ptr tmp, tmp2, prev;
  node_ptr sorted = 0;
  node_ptr from, new_def = 0;

  int count_processed = def_len;

  /* Loop until all macros have been processed. */
  while (count_processed) 
    {
      prev = 0;
      for (tmp = *defs; tmp;  tmp = tmp2) {

        node_ptr var = cdr(car(tmp));

        tmp2 = cdr(tmp); /* Next item to process. */

        if (!has_edge(var)) {

          /* Add edge to start of new_def. */
          tmp->right.nodetype = new_def;
          new_def = tmp;

          /* Disconnect node from defs. */
          if (prev) 
            prev->right.nodetype = tmp2;
          else
            *defs = tmp2;

          /* Remove all edge pointing to var */
          remove_edges_to(var);

          count_processed--;
        }
        else
          prev = tmp;
      }
    }

  *defs = reverse(new_def);

}

/* This is the main routine (whereas dump_bdd_form is just a wrapper)
   which accepts a bdd and returns a finite state formula
   which represents it. It also exports "defs", a list
   of definitions which are used inside the formula. */
node_ptr bdd_to_formula(bdd_ptr d, node_ptr *defs, int primed)
{
  extern node_ptr variables;

  node_ptr order;
  node_ptr formula, tmp;
  static int n=0;


  /***** Initialiazations *****/


  /* Initialize print_hash. */ 
  if (!print_hash) {
    print_hash = new_assoc();
  }

  clear_hash(print_hash);

  /* Make sure that the mapping between variable names and bdd variable 
     numbers is correct. This is just a safety precaution, since it
     should always be set OK. Note that we need this since without it
     there is no way to extract from the bdd which variable names
     correspond to it. */
  set_variable_names();


  /* Obtain formula from the bdd d. The basic structure 
     of the formula is
      var = val1 -> formula1
      var = val2 -> formula2
      ..

     but with some additional simplifications.
  */
  formula = bdd_to_formula_aux(d,variables, primed, 0);

  /* Find shared expressions in "formula" 
     and store them into the "defs" linked list. defs is a linked
     list of pairs: (name, subformula) where the name starts with 
     X and has a number appended to it. */
  clear_hash(print_hash);
  collect_defs(formula,defs,print_hash,&n);
  clear_hash(print_hash);

  /* Insert defs into print_hash. The key is the formula
     and the value is the printed representation. */
  for(tmp=*defs; tmp; tmp=cdr(tmp))
    insert_assoc(print_hash,car(car(tmp)),cdr(car(tmp)));


  {
    /* Initialize depedency graph. */
    /* Returns how many macros/variables do we have. */
    int def_len = init_graph(*defs);

    /* Replace shared expressions by printed representation 
       in the formula part (the key) of the defs lists. 
       This is useful in printing more succint macro definitions. */
    replace_shared_nodes_defs(*defs,print_hash);

   
    /* Find good order for printing macros, so that each macro
       will use only macros which have been defined previously. 
       defs is returned sorted. */
    sort_dependency(def_len, defs);

    /* Clear depedency graph. */
    clear_graph();
  }

  /* Replace shared expressions by printed representation 
     in formula. */
  formula=replace_shared_nodes(formula,print_hash, 0 , 0);

  return(formula);
}


/* EXPORTED. */

/* Dumps bdd into a file as a formula.
   The dump format is simply a sequence of tlv assignment 
   statments, of the form 

    Let varname := ...

   If this is stored in a file then the variable can be loaded
   again by simply loading the file.

   primed is either 0 or 1. If 0 only print unprimed variables.
   varname is the name of the variable into which the assignment
   will be made.  */
void dump_bdd_formula(FILE *ff, register bdd_ptr d, int primed,
                      char *varname)
{
  node_ptr defs=NIL, tmp;
  
  /* Translage bdd "d" into a formula represnted as a node_ptr. 
     In addition, return any definitions into the list "defs" 
     (an output paramter). */
  node_ptr formula=bdd_to_formula(d,&defs,primed);

  /* Print all the definitions. */
  tmp=defs;
  while(tmp) { 
    /* Each item in "defs" contains a pair of "definition name" and "formula" */
    node_ptr pair=car(tmp),name,f;

    if(pair->type != LIST) catastrophe("dump_bdd_formula: pair->type != LIST");

    /* Extract pair. */
    name=cdr(pair); f = car(pair);

    /* Print definition pair. */
    fprintf(ff,"Let '");
    fprint_node(ff,name);fprintf(ff," := "); fprint_node(ff,f);
    fprintf(ff,";\n");

    /* Go to next definition item. */
    tmp=cdr(tmp);
  }
  fprintf(ff,"\n");

  /* Finally, Print the formula. */
  fprintf(ff,"Let %s := ", varname);
  fprint_node(ff,formula);
  fprintf(ff,";\n");

  free_list(defs);
}

