#include <node.h>
#include <bdd.h>
#include <symbols.h>
#include <util_err.h>

#include <y.tab.h>

#define MAXSTVARS 30000

extern int nstvars;  /* The number of bdd variables. Defined in bdd.c */

extern int verbose;

/* Get a new variable for bdd's. This is done by increasing nstvars
   and anding the new variable with the "vars" bdd */
static int get_bdd_var(void)
{
  if(nstvars == MAXSTVARS)toomanyvars();
  if(verbose > 1)fprintf(tlvstderr,"  BDD variable %d\n",nstvars+1);

  /*  release_bdd(vars);
  vars = save_bdd(and_bdd(atomic_bdd(nstvars+1),vars)); */
  return(++nstvars);
}
  

/* This routine creates a scalar variable bdd and returns it's bdd.
   A scalar variable is just a variable with a finite type.
   The bdd returned has leafs which are items of the type.
   For example, for parameters l = (A,B,C,D), n =30, the result
   bdd will be something like:

          30
         / \
        32 32
       /\   /\
      A  C  B D


  parameters:
   l - type of the variable
   n - The bdd level number of the variable.

   If the scalar variable can obtain only one value then a constant
   is returned.

   A scalar var is represented by several bdd variables, one for
   each bit needed to represent the type.
   Note that this function is recursive. */
bdd_ptr scalar_var_aux(node_ptr l, int n)
{
  if(l == NIL)catastrophe("scalar_var_aux: l = NIL");

  if(cdr(l) == NIL){
    /* We have a scalar variable with only one value, so we want
       to return a leaf bdd, with a constant value. */

    /* Check if the constant already exists in the constant
       hash, then return it. */
    node_ptr v = find_atom(car(l));
    bdd_ptr temp = get_constant(v);
    if(temp)return(temp);

    /* If we reached here, then the constant does not
       exist in the hash table.  
       Generate new lead bdd which contains constant, save
       in constant hash, and return it. */
    temp = save_bdd(leaf_bdd(v));
    if(v && v->type == ATOM) insert_constant(v,temp);
    return(temp);
  }

  /* The size of l is greater than 2, so we have to allocate
     a new bdd variable (n). */

  /* Add a new variable if not already exists */
  if((++n) > nstvars)
    get_bdd_var();  /* This has side effect of increasing nstvars.*/

  /* Recursively, split the list in half, and handle each one
     separately. */
  {
    bdd_ptr p0 = scalar_var_aux(odd_elements(l),n);
    bdd_ptr p1 = scalar_var_aux(even_elements(l),n);
    return(find_bdd(THE_CURRENT_VAR(n),p0,p1));
  }
}


bdd_ptr scalar_var(node_ptr l)
{
  return scalar_var_aux(l,nstvars);
}

/* Input: the name of a variable. Returns
   corresponding bdd, as saved in the symbol table. */
bdd_ptr get_bdd_of_var(node_ptr l)
{
  node_ptr s = get_program_var_symbol(l);

  return bdd_of(s);
}


/* Input: a bdd. Returns variable name which
   corresponds to level of root of bdd. */
node_ptr get_var_of_bdd_root_level(bdd_ptr b)
{
  extern node_ptr *variable_names;

  int blevel = GETLEVEL(b);
  int i;

  for (i=blevel; i>=0 ; i--) 
    if (variable_names[i] != NIL)
      return variable_names[i];
  
  return NIL;
}

