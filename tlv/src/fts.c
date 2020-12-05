#include <node.h>
#include <bdd.h>
#include <y.tab.h>
#include "fts.h"


fts fts_list = 0;   /* Information about systems and processes is collected here. */


/* Sorted list which contains all "kind" names exactly once. */
node_ptr list_of_all_kinds = NIL;



/* Obtain record for new fts. */
fts new_fts(node_ptr sys_name)
{
  fts f = (fts) malloc(sizeof(struct fts_data));

  f->name = sys_name;

  f->variables = f->kinds = f->init = f->just = f->compassion = NIL;
  f->components = 0;
  f->ltl_list = 0;
  f->next = 0;

  /* Manage list of systems. */
  if (fts_list)
    {
        /* Link new system to old one */
        f->next = fts_list->next;
        fts_list->next = f;
    }
  else
    fts_list = f;

  return f;
}

/* Obtain record for new component. */
component_ptr new_component(void)
{
  component_ptr c = (component_ptr) malloc(sizeof(component_rec));

  c->owned = c->trans = c->assign = c->context = NIL;
  c->prop_t = c->prop_d = 0;
  c->prop_t_F = c->prop_d_F = NIL;
  c->composition_type = 0;
  c->c1 = c->c2 = 0;

  return c;
}

/* Create and return new component, filled with
   composition type, two child components, and context */
component_ptr new_component_fill(int ctype,
                                 component_ptr c1, component_ptr c2,
                                 node_ptr context)
{
  component_ptr c = new_component();

  /* Fill record */
  c->composition_type = ctype;
  c->c1 = c1;  
  c->c2 = c2;
  c->context = context;

  return c;
}

/**********************************************************************/


/* Return a component tree which is a syncronous composition of
   components c1,c2 . */
component_ptr synch_compose(component_ptr c1, component_ptr c2)
{
  if (c1 == 0)  /* c1 is the empty component. */
    return c2;
  else if (c2 == 0)
    return c1;
  else {
    component_ptr c = new_component();
    c->c1 = c1;
    c->c2 = c2;

    c->composition_type = SYNCHCOMP;
    return c;
  }
}

/* When using the COMPOSED section, the components are built up
   recursively. However, when the "process" keyword is used, then
   the process is composed asynchronously with everything else in
   the system. This function adds a "process" component by 
   composing the component asynchronously with the root of the
   component tree of the fts. */
void add_component_as_top_process_of_fts(fts f, component_ptr c)
{
  if (c == 0)  /* If the component is empty then do nothing. */
    return;
  else if (f->components) {
    /* Compose asynchronously with f->components. */

    component_ptr new_c = new_component();

    new_c->composition_type = ASYNCHCOMP;

    new_c->c1 = f->components;
    new_c->c2 = c;

    f->components = new_c;
  }
  else
    f->components = c;
}

/**********************************************************************/

/* Returns 1 if the component is empty. */
int empty_component(component_ptr c)
{
  return (c->composition_type == 0 && c->trans == NIL && c->assign == NIL);
}

/* Lexicographicall sorted. */
node_ptr add_to_sorted_atom_list_with_no_duplicates(node_ptr list,
                                                    node_ptr item)
{
  int cmpresult;

  if (list == NIL ||
      (cmpresult = strcmp(atom_to_string(car(list)),
                          atom_to_string(item))) < 0)
    return cons(item,list);
  else if ( cmpresult == 0)
    return list;
  else {
    list->right.nodetype =
      add_to_sorted_atom_list_with_no_duplicates(cdr(list),item);
    return list;
  }
}

/* Add the variable of the system f, to the kind set of the system. */
void add_kind(fts f, node_ptr variable, node_ptr kind)
{
  /* Store kind and variable on list. */
  f->kinds = cons(cons(kind,variable),f->kinds);

  /* Side effect: Compute list of all kinds. */
  list_of_all_kinds =
    add_to_sorted_atom_list_with_no_duplicates(list_of_all_kinds,kind);

  /*  prinstf("add_kind :");
  print_list(list_of_all_kinds); */
}

/* Add the variable of the system f, to the sets of kinds specified in the
   kind_list. */
void add_kinds(fts f, node_ptr variable, node_ptr kind_list)
{
  node_ptr l = kind_list;

  for (;l; l = cdr(l))
    add_kind(f,variable,car(l));
}

/*
  Functions on lists of fts.
*/

fts append_fts(fts x, fts y)
{
  if(x==0)return(y);
  x->next = append_fts(x->next, y);
  return(x);
}

fts reverse_fts(fts f) 
{
  if ( f )
    {
       fts temp = reverse_fts(f->next);
       f->next = 0;
       return append_fts(temp,f);
    }    
  else
      return 0;
}


/* Assign a number to each transition system, and insert the number
   of transition systems into _sn. */
void number_fts(void)
{
  int curr_fts = 0;
  fts f2;

  fts_list = reverse_fts(fts_list);


  /* Number fts's */
  for (f2 = fts_list ; f2 ; f2 = f2-> next) 
     f2->fts_no = ++curr_fts;

  /* Insert _sn */
  insert_dynamic_var(var_key("_sn"),
                     save_bdd( leaf_bdd(find_NUMBER_node(curr_fts)) )  );
}


/**********************************************************************/
