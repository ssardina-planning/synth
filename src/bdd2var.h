/*  Routines for converting variables to bdds (allocating bdd variables)
    and vice versa. */


/* This routine creates a scalar variable bdd and returns it's bdd

   l - type of the variable

   If the scalar variable can obtain only one value then a constant
   is returned.

   A scalar var is represented by several bdd variables, one for
   each bit needed to represent the type */
bdd_ptr scalar_var(node_ptr l);


/* Input: the name of a variable. Eeturns
   corresponding bdd, as saved in the symbol table. */
bdd_ptr get_bdd_of_var(node_ptr l);

/* Input: a bdd. Returns variable name which
   corresponds to level of root of bdd. */
node_ptr get_var_of_bdd_root_level(bdd_ptr b);


/*get_first_level(level)
  get_last_level(level)*/
