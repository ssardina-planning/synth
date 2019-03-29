/* Various satisfiability routines for bdd's. 
   This file is included from bdd.c */


/***************************************************************************\
*function: sat_bdd							    *
*									    *
*returns a bdd which is <= bdd d, but has at most one node at each level    *
\***************************************************************************/
/* This function is used in finding counterexamples
   It is intended to produce one element of a set which is
   represented by the BDD d. */

bdd_ptr sat_bdd_aux(bdd_ptr d,int l)
{
  bdd_ptr temp1;
  int mylevel,l1 = THE_CURRENT_VAR(l);
  if(d == ZERO)return(d);
  if(l > nstvars)return(ONE);
  mylevel=GETLEVEL(d);

  if(l1 == mylevel){
    if(d->left != ZERO)return(find_bdd(mylevel,
				       sat_bdd_aux(d->left,l+1),
				       ZERO));
    return(find_bdd(mylevel,
		    ZERO,
		    sat_bdd_aux(d->right,l+1)));
  }

  if(l1 < mylevel)
    return(find_bdd(l1,sat_bdd_aux(d,l+1),ZERO));

  if(d->left != ZERO)return(sat_bdd_aux(d->left,l));

  return(sat_bdd_aux(d->right,l));
}

bdd_ptr sat_bdd(bdd_ptr d)
{
  /*
   * Calling sat_bdd_aux with nstbase+1 eliminates the process
   * selection variables from the resulting bdd.  As a result, the
   * error trace cannot tell which process is executing.
   * 
   * It was restored by steed.
   */
#if 1
  return(sat_bdd_aux(d,NSTBASE+1));
#else
  return(sat_bdd_aux(d,1));
#endif
}



/* This function is used in finding counterexamples
   It is intended to produce one element of a set which is
   represented by the BDD d. In contrast to sat_bdd, it does
   not "fill out" a value in all possible levels. Instead,
   it only fills those levels which appear in the set represented by
   var_set */

bdd_ptr sat_bdd_from_set(bdd_ptr d,bdd_ptr var_set)
{
  int mylevel,l1; 

  if(d == ZERO)return(d);
  if(ISLEAF(var_set))return(ONE);

  l1 = GETLEVEL(var_set);
  mylevel=GETLEVEL(d);

  if(l1 == mylevel){
    if(d->left != ZERO)return find_bdd(mylevel,
				       sat_bdd_from_set(d->left,var_set->right),
				       ZERO);
    return find_bdd(mylevel,
		    ZERO,
		    sat_bdd_from_set(d->right,var_set->right));
  }

  if(l1 < mylevel)
    return find_bdd(l1,sat_bdd_from_set(d,var_set->right),ZERO);

  if(d->left != ZERO) return sat_bdd_from_set(d->left,var_set);

  return sat_bdd_from_set(d->right,var_set);
}


/***********************************************************************
  sat_bdd_from_state_space

  This routine replaces both sat_bdd and sat_bdd_from_set. The problem
  with those routines was that it allocated bdd nodes which encode 
  values in a strange way. This happens only for variables whose range
  is not a power of two. For example, a variable which can have range
  of 1..3 . Such a variable is encoded by two bdd varibles, however,
  one particular value should be encoded by only one of the variables.
  The two faulty sat routines would encode this value using two 
  bdd variables as well. This creates strange situations, for example,
  where two different bdd's appear the same when printed, but are 
  in fact different, and the place they differ is in that bdd variable
  which makes no difference to the encoding of the value of a variable.

  The way this routine works is by using a bdd, which encodes the 
  allowed state space. The routine only generates a satisfying assignment
  within this state space.


THIS DOESN't work as originally intended because ss cannot be computed!!!
  However, we can use the variable's bdd from the symbol table instead of
  ss, but this can only be used to satisfy a single variable.
**********************************************************************/

bdd_ptr sat_bdd_from_state_space(bdd_ptr d, bdd_ptr ss)
{
  bdd_ptr temp1;
  int mylevel,sslevel; 

  if (d == ZERO) return d;   /* We cannot satisfy a contradiction. */

  if (ISLEAF(ss)) return ONE ; 

  mylevel = GETLEVEL(d);
  sslevel = GETLEVEL(ss);

  if(sslevel == mylevel){
    if(d->left != ZERO)
      return find_bdd(mylevel,
		      sat_bdd_from_state_space(d->left,ss->left),
		      ZERO);
    else
      return find_bdd(mylevel,
	  	      ZERO,
		      sat_bdd_from_state_space(d->right,ss->right));
  }
  else if (sslevel < mylevel)
      return find_bdd(sslevel,
                      sat_bdd_from_state_space(d,ss->left),
                      ZERO);
  else 
      return sat_bdd_from_state_space(d->left != ZERO ? d->left : d->right, 
                                      ss);
}



/***************************************************************************\
*function: rand_original_sat_bdd							    *
*									    *
*returns a bdd which is <= bdd d, but has at most one node at each level    *
\***************************************************************************/
/* This function is used in finding counterexamples
   It is intended to produce one element of a set which is
   represented by the BDD d. The BDD d should be UNPRIMED!!!

    It is like sat_bdd, but returns a RANDOM element. */
int the_largest_var_num=0;
bdd_ptr the_type_left, the_type_right;

bdd_ptr rand_original_sat_bdd_aux(bdd_ptr d,int l,bdd_ptr the_type)
{
  int sl,sr;
  int min_of_mylevel_l1;
  bdd_ptr temp1;
  int mylevel,l1 = THE_CURRENT_VAR(l);
  if(d == ZERO)return(d);
  if(l > nstvars)return(ONE);
  mylevel=GETLEVEL(d);

  min_of_mylevel_l1 = mylevel < l1 ? mylevel : l1;

  /* Try to find the type bdd of the variable corresponding to 
     the current level. */
  if (the_type == 0 || 
      (ISLEAF(the_type) && VAR_NUM(min_of_mylevel_l1) > the_largest_var_num ) )
  {
    int i = min_of_mylevel_l1;

    while(i >=0 && variable_names[i] == NIL)  i--;

    if (i<0)      
      /* We didn't find a corresponding variable. If this happened
         for a *real* bdd variable then this is an error. */
      if ( mylevel <= l1 )
        catastrophe("No corresponding variable found to bdd in rand_original_sat_bdd_aux\n");
      else
        /* Search for the first variable and rerun this procedure from there */
        {
          i=0;
          while(i < nstvars*2 && variable_names[i] == NIL)  i++;

          if (i > nstvars*2)
            catastrophe("No variable names found in rand_original_sat_bdd_aux\n");
          
          return rand_original_sat_bdd_aux(d,VAR_NUM(i),
                                           the_type);
        }

    else
      {
        the_type = get_bdd_of_var(variable_names[i]);
        the_largest_var_num = lowest_var_bdd(the_type);
      }
  }

  the_type_left  = ISLEAF(the_type) ? the_type : the_type->left;
  the_type_right = ISLEAF(the_type) ? the_type : the_type->right;

  if(l1 == mylevel){
    /* IF both sides are available choose at random. */

    if (d->left != ZERO && d->right != ZERO )
      {
        if ( rand_choose_left_branch_by_state_space(d) )
            return find_bdd(mylevel,
                       rand_original_sat_bdd_aux(d->left,l+1,the_type_left),
                       ZERO);
        else
            return find_bdd(mylevel,
                        ZERO,
                        rand_original_sat_bdd_aux(d->right,l+1,the_type_right));
      }
    else if(d->left != ZERO)
        return find_bdd(mylevel,
                    rand_original_sat_bdd_aux(d->left,l+1,the_type_left),
                    ZERO);
    else
        return find_bdd(mylevel,
		    ZERO,
		    rand_original_sat_bdd_aux(d->right,l+1,the_type_right));
  }

  /* This is the tricky part where we have to "fill" the bdd
     with new values in a random fashion (whereas in sat_bdd we only
     go left which is always safe, sometimes going right is not legal. 
     This depends on the type of the variable corresponding to level "l". */
  if(l1 < mylevel)
    {
      int ran , res ;

      /* If no corresponding variable was found then dont add
         this to the bdd. */
      if (ISLEAF(the_type))
        return rand_original_sat_bdd_aux(d,l+1,the_type);

      /* A corresponding variable was found. */

      /* Branch proportionally to size of bdd's on both branches. */
      if (rand_choose_left_branch_by_size(the_type))
        return 
          find_bdd(l1,rand_original_sat_bdd_aux(d,l+1,the_type_left),
                      ZERO);
      else
        return 
          find_bdd(l1,ZERO,
                      rand_original_sat_bdd_aux(d,l+1,the_type_right));
    }

  /* IF both sides are available choose at random. */

  if (d->left != ZERO && d->right != ZERO )
    {
      /* Branch proportionally to size of bdd's on both branches. */
      if (rand_choose_left_branch_by_state_space(d) )
          return rand_original_sat_bdd_aux(d->left,l,the_type);
      else
          return rand_original_sat_bdd_aux(d->right,l,the_type);
    }
  else if (d->left != ZERO)
      return rand_original_sat_bdd_aux(d->left,l,the_type);
  else
      return rand_original_sat_bdd_aux(d->right,l,the_type);
}


bdd_ptr rand_original_sat_bdd(bdd_ptr d)
{
  /*
   * Calling sat_bdd_aux with nstbase+1 eliminates the process
   * selection variables from the resulting bdd.  As a result, the
   * error trace cannot tell which process is executing.
   * 
   * It was restored by steed.
   */

set_variable_names();

#if 1
  return(rand_original_sat_bdd_aux(d,NSTBASE+1,0));
#else
  return(rand_original_sat_bdd_aux(d,1,0));
#endif
}


/* Choose at random a side (left or right) according to the
   size of the bdd on each side. */
int rand_choose_left_branch_by_size(bdd_ptr d)
{
  /* Branch proportionally to size of bdd's on both branches. */
  int sl = size_bdd(d->left);
  int sr = size_bdd(d->right);

  int ran = rand() % RAND_MAX;
  int res = RAND_MAX * (sl / (float)(sl + sr));

  return ran < res;
}

/* Choose at random a side (left or right) .
   The random choice should be made
   such that it is more likely to choose the side with more space
   state, proportionally to the amount of state space. */
int rand_choose_left_branch_by_state_space(bdd_ptr d)
{
  double sl = count_bdd(d->left);
  double sr = count_bdd(d->right);

  int ran = rand() % RAND_MAX;
  double res = RAND_MAX * (sl / (sl + sr));

  return ran < res;
}


/* The aim of this routine is :
    Find a satisfying path in the bdd d.
    This path SHOULD NOT include all levels.
    It should only include the levels needed to satisfy the bdd.
    The normal "sat_bdd" routines goes over all levels,
    if there is a level which does not appear in d then
    an arbitray choice is taken. We don't want that in some cases,
    especially if we want to print the bdd, because if there are 
    many variables in the system and we are printing a counter example
    then the values of variables which are added by the "normal" sat
    procedure don't add more information, yet clutter the printout.
 
    The parameter l here is the actual level number
    and not the variable number */
bdd_ptr sparse_sat_bdd_aux(bdd_ptr d, int l)
{
  int mylevel;
  if(d == ZERO)return(d);
  if(l > nstvars*2 +1)return(ONE);
  mylevel=GETLEVEL(d);
  if(l == mylevel){
    if(d->left != ZERO)return(find_bdd(mylevel,
				       sparse_sat_bdd_aux(d->left,l+1),
				       ZERO));
    return(find_bdd(mylevel,
		    ZERO,
		    sparse_sat_bdd_aux(d->right,l+1)));
  }
  if(l < mylevel)
    return(sparse_sat_bdd_aux(d,mylevel));

  /* Here l1 > mylevel. This means that we don't want variables
     below l1 to appear in the satisfying bdd so choose one side
     of d to continue */
  if(d->left != ZERO)
    return(sparse_sat_bdd_aux(d->left,l));
  else
    return(sparse_sat_bdd_aux(d->right,l));
}

bdd_ptr sparse_sat_bdd(bdd_ptr n)
{
  return (sparse_sat_bdd_aux(n,1));
}


bdd_ptr multisataux(bdd_ptr n,int rejecting)
{
  if (TESTMARK(n))
    {
    return leaf_bdd(find_NUMBER_node(rejecting));
    }

  SETMARK(n);

  if(ISLEAF(n))
    {
      return n;
    }
  else    
      return find_bdd(GETLEVEL(n),multisataux(n->left,rejecting),
                                  multisataux(n->right,rejecting)
                     );
}

bdd_ptr multisat(bdd_ptr n,int rejecting)
{
  bdd_ptr b = multisataux(n, rejecting);
  repairmark(n);
  return b;
}






/* Like new_sat_bdd, but the path is random. */
bdd_ptr rand_sat_bdd_aux(bdd_ptr d, int l)
{
  int mylevel;
  int sl,sr;
  if(d == ZERO)return(d);
  if(l > nstvars*2 +1)return(ONE);
  mylevel=GETLEVEL(d);

  if(l == mylevel){
    if (d->left != ZERO && d->right != ZERO )
      {
        /* Branch proportionally to size of state space on both branches. */
        if (rand_choose_left_branch_by_state_space(d))
            return(find_bdd(mylevel,
                            rand_sat_bdd_aux(d->left,l+1),
                            ZERO));
        else
            return(find_bdd(mylevel,
                            ZERO,
                            rand_sat_bdd_aux(d->right,l+1)));
      }

    if(d->left != ZERO)return(find_bdd(mylevel,
				       rand_sat_bdd_aux(d->left,l+1),
				       ZERO));
    return(find_bdd(mylevel,
		    ZERO,
		    rand_sat_bdd_aux(d->right,l+1)));
  }
  if(l < mylevel)
    return(rand_sat_bdd_aux(d,mylevel));

  /* Here l1 > mylevel. This means that we don't want variables
     below l1 to appear in the satisfying bdd so choose one side
     of d to continue */
  if (d->left != ZERO && d->right != ZERO )
    {
      /* Branch proportionally to size of state space on both branches. */
      if (rand_choose_left_branch_by_state_space(d) )
        return(rand_sat_bdd_aux(d->left,l));
      else
        return(rand_sat_bdd_aux(d->right,l));
    }

  if(d->left != ZERO)
    return(rand_sat_bdd_aux(d->left,l));
  else
    return(rand_sat_bdd_aux(d->right,l));
}


/* Like new_sat_bdd, but the path is random. */
bdd_ptr rand_sat_bdd(bdd_ptr d)
{
  return (rand_sat_bdd_aux(d,1));
}
