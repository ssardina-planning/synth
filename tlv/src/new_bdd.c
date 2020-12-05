/* This file contains new bdd functions. It is included by bdd.c */

static  char buf[200];

/***************************************************************************\
*function: fast_and_bdd							    *
*									    *
*and two bdds, but once a satisfying assignment to the result has been found*
*then stop.     							    *
* It is like doing sat_bdd(and_bdd(a,b))                                    *
\***************************************************************************/
bdd_ptr fast_and_bdd(bdd_ptr a,bdd_ptr b)
{
  int alevel,blevel;
  bdd_ptr temp1;
  /* anything AND false is false */
  if(a==ZERO || b==ZERO)return(ZERO);
  /* anything AND true is itself */
  if(a==ONE) return(b);
  if(b==ONE) return(a);

  if(ISLEAF(a))type_error(leaf_value(a));
  if(ISLEAF(b))type_error(leaf_value(b));
  if(a==b)return(a);

  if(((int)a)>((int)b))swapwords(&a,&b);

  /* Check to see if we've solved this problem before */
  if(temp1=find_apply(FAST_AND_OP,a,b))return(temp1);

  /* if not, get the level fields of a and b */
  alevel=GETLEVEL(a);
  blevel=GETLEVEL(b);
  /* now break the AND problems into two subproblems */
  /* if levels are the same, do AND(a->left,b->left), AND(a->right,b->right) */
  if(alevel==blevel)
   {
    temp1 = fast_and_bdd(a->left,b->left) ;
    if ( temp1 != ZERO )
       temp1=find_bdd(alevel,temp1,ZERO);
    else
     {
       temp1 = fast_and_bdd(a->right,b->right) ;
       if ( temp1 != ZERO )
          temp1=find_bdd(alevel,ZERO,temp1);
     }
   }

  /* else if level of a is lower, split on value of a's variable */
  else if(alevel<blevel)
   {
    temp1= fast_and_bdd(a->left,b);
    if ( temp1 != ZERO )
       temp1=find_bdd(alevel,temp1,ZERO);
    else
     {
       temp1= fast_and_bdd(a->right,b);
       if (temp1 != ZERO )
          temp1=find_bdd(alevel,ZERO,temp1);
     }
   }

  /* else (level of b is lower), split on value of b's variable */
  else 
   {
    temp1=fast_and_bdd(a,b->left);
    if ( temp1 != ZERO )
       temp1=find_bdd(blevel,temp1,ZERO);
    else
     {
       temp1=fast_and_bdd(a,b->right);
       if (temp1 != ZERO)
         temp1=find_bdd(blevel,ZERO,temp1);
     }
   }

  /* now put result in apply cache */
  insert_apply(FAST_AND_OP,a,b,temp1);

  return(temp1);
}


/* The first parameter is a satisfying path, the second
   is a bdd of all the values a specific variable can get */
bdd_ptr old_my_if_then_bdd(bdd_ptr a,bdd_ptr b)
{
  int alevel,blevel;
  bdd_ptr temp1;
  if(a==ZERO)return(leaf_bdd(ELSE_LEAF));
  if(a==ONE)
   {
    if ( ISLEAF(b) )  
      return(b);
    else
      return(leaf_bdd(ELSE_LEAF));
    }
  if(ISLEAF(a))type_error(leaf_value(a));

  if(temp1=find_apply((int)old_my_if_then_bdd,a,b))return(temp1);

  alevel=GETLEVEL(a);
  blevel=GETLEVEL(b);
  if(alevel==blevel)
    temp1=find_bdd(alevel,old_my_if_then_bdd(a->left,b->left),
		   old_my_if_then_bdd(a->right,b->right));
  else if(alevel<blevel)
   {
    temp1=old_my_if_then_bdd(a->left,b);
    if (temp1 == leaf_bdd(ELSE_LEAF))
      temp1 = old_my_if_then_bdd(a->right,b);
    }
  else temp1=leaf_bdd(ELSE_LEAF);

  insert_apply((int)old_my_if_then_bdd,a,b,temp1);

  return(temp1);
}



/* The first parameter is a satisfying path, the second
   is a bdd of all the values a specific variable can get */

bdd_ptr my_if_then_bdd_aux(bdd_ptr a, bdd_ptr b, int commited)
{
  int alevel,blevel;
  bdd_ptr temp1;
  if(a==ZERO)return(leaf_bdd(ELSE_LEAF));
  if(a==ONE)
   {
    if ( commited )  
      return(b);
    else
      return(leaf_bdd(ELSE_LEAF)); 
    }
  if(ISLEAF(a))type_error(leaf_value(a));


  alevel=GETLEVEL(a);
  blevel=GETLEVEL(b);
  if(alevel==blevel)
   {
    commited = 1;
    temp1=find_bdd(alevel,my_if_then_bdd_aux(a->left,b->left,commited),
		   my_if_then_bdd_aux(a->right,b->right,commited));
    }
  else if(alevel<blevel)
   {
    temp1=my_if_then_bdd_aux(a->left,b,commited);
    if (temp1 == leaf_bdd(ELSE_LEAF))
      temp1 = my_if_then_bdd_aux(a->right,b,commited);
    }
  else 
    if (ISLEAF(b))
      if (commited)
        temp1 = b;
      else
        temp1 = leaf_bdd(ELSE_LEAF);
    else
      temp1=find_bdd(blevel,my_if_then_bdd_aux(a,b->left,commited),
                            my_if_then_bdd_aux(a,b->right,commited));

  return(temp1);
}


/* The first parameter is a satisfying path, the second
   is a bdd of all the values a specific variable can get */
bdd_ptr my_if_then_bdd(bdd_ptr a, bdd_ptr b)
{
  return(my_if_then_bdd_aux(a,b,0));
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
bdd_ptr my_sat_bdd(bdd_ptr d, int l)
{
  int mylevel;
  if(d == ZERO)return(d);
  if(l > nstvars*2 +1)return(ONE);
  mylevel=GETLEVEL(d);
  if(l == mylevel){
    if(d->left != ZERO)return(find_bdd(mylevel,
				       my_sat_bdd(d->left,l+1),
				       ZERO));
    return(find_bdd(mylevel,
		    ZERO,
		    my_sat_bdd(d->right,l+1)));
  }
  if(l < mylevel)
    return(my_sat_bdd(d,mylevel));

  /* Here l1 > mylevel. This means that we don't want variables
     below l1 to appear in the satisfying bdd so choose one side
     of d to continue */
  if(d->left != ZERO)
    return(my_sat_bdd(d->left,l));
  else
    return(my_sat_bdd(d->right,l));
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



bdd_ptr new_sat_bdd(bdd_ptr n)
{
  return (my_sat_bdd(n,1));
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



/* This routine accepts a bdd, and then returns a bdd
   which can be used to quatify with.  The returned
   bdd will quatify all variables which appeared in
   the input bdd. 

   THIS IS THE SAME AS "support_bdd"!!! so I erased this.

bdd_ptr quant(a)
bdd_ptr a;
{
  bdd_ptr b;

  if ( ISLEAF(a) ) return ONE;

  b = and_bdd(quant(a->left),quant(a->right));
  return and_bdd(find_bdd(GETLEVEL(a),ZERO,ONE),b);
}

*/

bdd_ptr replace_leaves_generic(bdd_ptr a,
                               node_ptr (*f)(node_ptr n))
{
  if ( ISLEAF(a) )
    return leaf_bdd(f((node_ptr)a->left));
  else
    return find_bdd(GETLEVEL(a),
                    replace_leaves_generic(a->left,f),
                    replace_leaves_generic(a->right,f));
}


bdd_ptr replace_leaves(bdd_ptr a,
                       node_ptr from, node_ptr to)
{
  if ( ISLEAF(a) )
    {
      while (from) {
        if (((node_ptr)a->left) == car(from))
          return leaf_bdd(car(to));

        from = cdr(from);
        to = cdr(to);
      }
      return a;
    }
  else
    return find_bdd(GETLEVEL(a),
                    replace_leaves(a->left,from,to),
                    replace_leaves(a->right,from,to));
}




/* Print the bdd */
void print_bdd(bdd_ptr a, int col)
{
  /* if (a==ZERO) return;*/

 if (ISLEAF(a))
  {
   int i;

   for (i=0;i<col;i++)
     fprintf(tlvstdout," ");

   if (a==ONE)
     fprintf(tlvstdout,"ONE\n");
   else if (a==ZERO)            /* Maybe I should delete this and  */
     fprintf(tlvstdout,"ZERO\n");  /* undelete exiting on a==ZERO ?   */
   else
     fprintf(tlvstdout,"LEAF\n");
  }
 else
  {
    print_bdd(a->right,col+2);

    {
       int level = GETLEVEL(a);
       int i;

       for (i=0;i<col;i++)
         fprintf(tlvstdout," ");
       fprintf(tlvstdout,"%d\n",level);
    }
    
    print_bdd(a->left,col+2);
  }
}


/* **********************************************************************  */

/* Given a bdd, print into buf the name of corresponding bit of
   the corresponding variable. */
void print_boolean_var_name_to_buf(bdd_ptr a, node_ptr *name_table)
{
    char localbuf[100];
    int i;
    int level = GETLEVEL(a);
    int curr_level = THE_CURRENT_VAR(VAR_NUM(level));

    /* Search the upper boundary of this variable, and put into i */
    for (i=curr_level; i>0 && name_table[i] == NIL; i-=2); 

    localbuf[0] = buf[0] = 0;
    sprint_node(localbuf,100,name_table[i]); /* Print name */

    /* Print into buf. Print variable name, bit number in variable,
       and whether variable is primed or not.  */
    sprintf(buf,"%s_%d%s",
             localbuf,
             name_table[i+2] == NIL && VAR_NUM(i)<nstvars ?
                  VAR_NUM(curr_level) - VAR_NUM(i) :
                  0,
             IS_NEXT_VAR(level) ? "'" : "" /* Print "'" if primed varialbe */
          );  
}


/* Gets as parameter the name of a bdd node which is shared, and
   return the corresponding auxiliary variable name. */
node_ptr new_var_of(bdd_ptr b)
{
  return find_assoc(shared_vars_hash,(node_ptr) b);
}


/* Traverse the bdd, and when a shared bdd is found (it is found
   by reaching it the second time in a traversal) then the new var
   is created. */

node_ptr create_new_vars_list_aux(bdd_ptr b, int *new_var_no)
{
  if (ISLEAF(b))
    return NIL;

  if (TESTMARK(b)) {
    node_ptr l;

    /* We have encountered this bdd before so it must be shared.
       Check if a variable for this bdd has already been created.
       If not then create it. */
    if ( (l = new_var_of(b)) == NIL ) {
      char localbuf[100] = "", *st;
      node_ptr s;

      sprintf(localbuf,"xxx__%d",*new_var_no);
      st = (char *) malloc(strlen(localbuf));

      strcpy(st,localbuf);
      (*new_var_no)++;

      s = string_to_atom(st);
      insert_assoc(shared_vars_hash,(node_ptr) b, s);
      return cons( cons(s ,(node_ptr)b), NIL);
    }
    else 
      return NIL;
  }
  else {
      SETMARK(b);
      return append( create_new_vars_list_aux(b->left, new_var_no),
                     create_new_vars_list_aux(b->right, new_var_no));
  }
}

node_ptr create_new_vars_list(bdd_ptr b)
{
   static int i = 0;
   node_ptr l = create_new_vars_list_aux(b,&i);

   repairmark(b);
   return l;
}



char *name_of_root(bdd_ptr b, node_ptr *name_table)
{
  print_boolean_var_name_to_buf(b, name_table);
  return buf;
}

/* If expand == 1 then if b has a corresponding new shared variable
   then do not use it, but instead print the entire formula. */
void print_bdd_by_shannon_using_new_shared(FILE *stream, bdd_ptr b, node_ptr *name_table, 
                                           char expand) 
{
  node_ptr new_var;

  if (ISLEAF(b)) 
    return;

  if ( !expand && (new_var = new_var_of(b)) != NIL )
    print_node(stream, new_var);
  else {

    if ( b->left != ZERO && b->right != ZERO)
      fprintf(stream,"( ");

    if ( b->left != ZERO ) {
        fprintf(stream," ! %s ", name_of_root(b,name_table) );

        if ( b-> left != ONE ) {
          fprintf(stream,"& (");
          print_bdd_by_shannon_using_new_shared(stream,b->left, name_table,0) ;
          fprintf(stream," )");
        }

        if (b->right != ZERO)
          fprintf(stream,") | (");
    }

    if ( b->right != ZERO ) {
        fprintf(stream," %s ", name_of_root(b,name_table) );

        if ( b->right != ONE ) {
          fprintf(stream,"& (");
          print_bdd_by_shannon_using_new_shared(stream,b->right, name_table,0) ;
          fprintf(stream," )");
        }
    }

    if ( b->left != ZERO && b->right != ZERO)
      fprintf(stream," ) ");
  }

}

/* This routine prints a bdd as a boolean formula. 
   Shared parts of the expression are assigned to new variable names */
void print_bdd_by_shannon(bdd_ptr b) 
{

  /* Go over the bdd and find nodes which are shared. For each shared
     node which is not a leaf, create a new boolean variable which encodes
     that shared bdd. */
  node_ptr new_vars_list = create_new_vars_list(b);

  node_ptr l;

  /* For each new shared variable print a conjunct which assigns
     the value of the shared subexpression to the shared value . */
  for (l = new_vars_list; l ; l = cdr(l) ) {
    node_ptr var_name = car(car(l));
    bdd_ptr bd = car(l)->right.bddtype;

    fprintf(tlvstdout,"( ");
    print_node(tlvstdout, var_name);
    fprintf(tlvstdout," = (");
    print_bdd_by_shannon_using_new_shared(tlvstdout,bd,variable_names,1);
    fprintf(tlvstdout," )  ) \n& \n");
  }
  
  /* Print expression. */
  print_bdd_by_shannon_using_new_shared(tlvstdout,b,variable_names,0);
}


/*************************************************************/
/* Print bdd as cnf */

/* Traverse the bdd, and create a  new variable for each node.
   The variable is stored both in the shared_vars_hash, and
   in a linked list of new variable names. */

node_ptr create_new_var_for_each_node_aux(bdd_ptr b, int *new_var_no)
{
  node_ptr l;

  if (ISLEAF(b) || TESTMARK(b))
    return NIL;

  SETMARK(b);


  /* If we have NOT encountered this bdd before then create a
     new variable for it. */
  if ( (l = new_var_of(b)) == NIL ) {
    char localbuf[100] = "", *st;
    node_ptr s,p;

    sprintf(localbuf,"xxx__%d",*new_var_no);
    st = (char *) malloc(strlen(localbuf));

    strcpy(st,localbuf);
    (*new_var_no)++;

    s = string_to_atom(st);
    insert_assoc(shared_vars_hash,(node_ptr) b, s);
    p = cons( cons(s ,(node_ptr)b), NIL);

    return append( p,
                append( create_new_var_for_each_node_aux(b->left , new_var_no),
                        create_new_var_for_each_node_aux(b->right, new_var_no)));
  }
  else 
    return NIL;

}

node_ptr create_new_var_for_each_node(bdd_ptr b)
{
   static int i = 0;
   node_ptr l = create_new_var_for_each_node_aux(b,&i);

   repairmark(b);
   return l;
}

#define name_of_bdd(b) ( b == ONE ? "TRUE" : ( b == ZERO ? "FALSE" : \
                                atom_to_string(new_var_of(b) ) ) ) 

void print_bdd2cnf(bdd_ptr b)
{

  /* Go over the bdd and find nodes which are shared. For each shared
     node which is not a leaf, create a new boolean variable which encodes
     that shared bdd. */
  node_ptr new_vars_list = create_new_var_for_each_node(b);

  node_ptr temp,l;

  /* Print singleton conjunct consisting of the root node of the BDD for the
     formula we want to convert to CNF. */

  fprintf(tlvstdout,"%s \n", name_of_bdd(b));

  /* For each new  variable print a conjunct which connects
     the values of the node to the nodes of the sons . */
  for (l = new_vars_list; l ; l = cdr(l) ) {
    node_ptr var_name = car(car(l));
    char n[100],n_0[100], n_1[100], x[100] ;
    bdd_ptr bd = car(l)->right.bddtype;

    fprintf(tlvstdout," &\n");

    n[0] = n_0[0] = n_1[0] = 0;

    sprint_node(n,100,var_name);
    strcpy(x,name_of_root(bd,variable_names));

    if (bd->left == ONE)
      strcpy( n_0, "TRUE" );
    else if (bd->left == ZERO)
      strcpy( n_0, "FALSE" );
    else
      sprint_node(n_0,100, new_var_of(bd->left));

    if (bd->right == ONE)
      strcpy( n_1, "TRUE" );
    else if (bd->right == ZERO)
      strcpy( n_1, "FALSE" );
    else
      sprint_node(n_1,100, new_var_of(bd->right));

    /* Print conjunts. */
    fprintf(tlvstdout,
            "(!%s | %s | %s) & (!%s | !%s | %s) & (%s | %s | !%s) & (%s | !%s | !%s)\n",
            n, x, n_0,   n, x , n_1,   n, x, n_0,    n, x , n_1);

  }  

}

/* Create disjunct of the u bits in the string u_string. */
void fill_u_string(int u_bits, int u_val, int u_suffix, char *u_string)
{
  int bit_no, bit_val;

  char u_name[200];
 
  u_string[0] = '\0';

  /* Loop which goes over all bits of u. */
  for (bit_no = 0; bit_no < u_bits; bit_no++) {

      if (bit_no != 0)
        strcat(u_string," | ");

      /* Find if bit bit_no in u_val is on or off. */

      bit_val = 1 << bit_no & u_val;

      if (bit_val)
          strcat(u_string,"!");

      sprintf(u_name,"UU%d_%d",u_suffix,bit_no);
      strcat(u_string,u_name);
  }
}


node_ptr create_new_or_get_old_var_for_each_node_aux(bdd_ptr b, int *new_var_no)
{
  node_ptr l;

  if (ISLEAF(b) || TESTMARK(b))
    return NIL;

  SETMARK(b);


  /* If we have NOT encountered this bdd before then create a
     new variable for it. */
  if ( (l = new_var_of(b)) == NIL ) {
    char localbuf[100] = "", *st;
    node_ptr s,p;

    sprintf(localbuf,"xxx__%d",*new_var_no);
    st = (char *) malloc(strlen(localbuf));

    strcpy(st,localbuf);
    (*new_var_no)++;

    s = string_to_atom(st);
    insert_assoc(shared_vars_hash,(node_ptr) b, s);
    p = cons( cons(s ,(node_ptr)b), NIL);

    return append( p,
            append( create_new_or_get_old_var_for_each_node_aux(b->left , new_var_no),
                    create_new_or_get_old_var_for_each_node_aux(b->right, new_var_no)));
  }
  else {
    node_ptr p = cons( cons(l ,(node_ptr)b), NIL);

    return append( p,
            append( create_new_or_get_old_var_for_each_node_aux(b->left , new_var_no),
                    create_new_or_get_old_var_for_each_node_aux(b->right, new_var_no)));
  }
    

}


node_ptr new_or_old_var_for_each_node(bdd_ptr b)
{
   static int i = 0;
   node_ptr l = create_new_or_get_old_var_for_each_node_aux(b,&i);

   repairmark(b);
   return l;
}


void print_bdd2cnf2(node_ptr bdd_list)
{
  node_ptr l;

  /* The range and number of bits required to represent u. */
  int u_len = length(bdd_list);
  double log_2 = log(2.0);
  double log_u_len = log((double)u_len);
  double u_bits_double = ceil(log_u_len/log_2);

  /* The number of bits needed to encode u_len, the length of the bdd list. */
  int u_bits = u_bits_double;

  /* The maximum value u can attain. */
  int u_val_max = pow(u_bits,2);

  int u = 0;

  static int u_suffix = 0;
 
  /* String which will contain part of disjunct. */
  char u_string[1000];

  u_suffix++;

  for (l = bdd_list; l ; l = cdr(l)) {

      bdd_ptr b = l->left.bddtype;

      /* Go over the bdd and find nodes which are shared. For each shared
         node which is not a leaf, create a new boolean variable which encodes
         that shared bdd. */
      node_ptr new_vars_list = new_or_old_var_for_each_node(b);

      node_ptr temp,l;

      fill_u_string(u_bits,u,u_suffix,u_string);  u++;

      /* Print conjunct which forces variable which corresponds to top node
         of bdd, to be true when  u != Constant */
      fprintf(tlvstdout,"(%s | %s) & ",u_string, name_of_bdd(b));


      /* For each new  variable print a conjunct which connects
         the values of the node to the nodes of the sons . */
      for (l = new_vars_list; l ; l = cdr(l) ) {
        node_ptr var_name = car(car(l));
        char n[100],n_0[100], n_1[100], x[100] ;
        bdd_ptr bd = car(l)->right.bddtype;

        n[0] = n_0[0] = n_1[0] = 0;

        sprint_node(n,100,var_name);
        strcpy(x,name_of_root(bd,variable_names));
        strcpy(n_0, name_of_bdd(bd->left));
        strcpy(n_1, name_of_bdd(bd->right) );

        /* Print conjunts. */
        fprintf(tlvstdout,"(!%s | %s | %s | %s) & (!%s | !%s | %s | %s) & "
                          "(%s | %s | !%s | %s) & (%s | !%s | !%s | %s)\n",
                 n, x, n_0, u_string,  
                 n, x, n_1, u_string,
                 n, x, n_0, u_string,
                 n, x, n_1, u_string);

        fprintf(tlvstdout," &\n");
      }
  }  

  /* Add conjuncts which elimanate values of u which should not appear. */
  for ( ; u < u_val_max ; u++ ) {
      fill_u_string(u_bits,u,u_suffix,u_string);     

      fprintf(tlvstdout,"(%s)\n &\n",u_string);
  }

  fprintf(tlvstdout,"TRUE\n");

}


void reset_sharing(void)
{
  clear_hash(shared_vars_hash);
}

/*************************************************************/

/* This function prints the graph of the bdd to a file. */
void new_graph_bdd_aux(FILE *stream,
                   bdd_ptr a,
                   node_ptr *name_table,
                   int is_an_mtbdd)
{

  if (TESTMARK(a)) return;
  SETMARK(a);  

  if (ISLEAF(a))
   {
    node_ptr n = (node_ptr)a->left;
     /* Make leaf in different shape, and set label */
    fprintf(stream,"s%d [shape=box,width=0,height=0,label=\"",
                    (int)a);
    print_node(stream,n);    /* Print node */
    fprintf(stream,"\"];\n");
   }
  else
  {
    /* Set label of node */

    fprintf(stream,"s%d [shape=box,width=0,height=0,label=\"",(int)a);

    if (!name_table)
      fprintf(stream,"%d\"];\n",GETLEVEL(a));
    else
      { 
        print_boolean_var_name_to_buf(a,name_table);
        fprintf(stream,"%s\"];\n",buf); /* Finish writing the label */
      }

    /* Connect to sons */
    if (is_an_mtbdd || a->left != ZERO)
      {
        fprintf(stream,"s%d -> s%d [style=dotted];\n",   /* [label=\"0\"] */
                       (int)a,(int)a->left);
        new_graph_bdd_aux(stream,a->left,name_table,is_an_mtbdd);
      }

    if (is_an_mtbdd || a->right != ZERO)
      {
        fprintf(stream,"s%d -> s%d;\n",   /* [label=\"1\"] */
                         (int)a,(int)a->right);
        new_graph_bdd_aux(stream,a->right,name_table,is_an_mtbdd);
      }
  }
}

/* Used only be tlv to draw a complete graph (not part of another graph). */
void new_graph_bdd(char* fname,bdd_ptr a)
{
  FILE *stream;

  stream = fopen(fname,"w");

  fprintf(stream,"digraph A {\n");
  new_graph_bdd_aux(stream,a,variable_names,is_mtbdd(a));
  fprintf(stream,"}\n");
  repairmark(a);

  fclose(stream);
}


/* The "reject" parameter is a number of a leaf which 
   should not be printed. If reject = NO_REJECT then we
   print all leaves. */
void graph_bdd_aux(FILE *stream,
                   bdd_ptr a,
                   char* prefix,
                   char* connect_to,
                   char **name_table,
                   int reject)
{

  if (TESTMARK(a)) return;
  SETMARK(a);  

  if (ISLEAF(a))
   {
    node_ptr n = (node_ptr)a->left;
     /* Make leaf in different shape, and set label */
    fprintf(stream,"%s%d [shape=box,width=0,height=0,label=\"Q",
                    prefix,(int)a);
    print_node(stream,n);    /* Print node */
    fprintf(stream,"\"");

    /*    if (n->type == NUMBER && F[n->left.inttype] == one_number)
      fprintf(stream,"style=filled];\n");
    else */
      fprintf(stream,"];\n");

    /* Connect leaf */
    if (connect_to)
      fprintf(stream,"%s%d -> %s;\n",prefix,(int)a,connect_to);
   }

  else
    {
      /* Set label of node */

      fprintf(stream,"%s%d [shape=box,width=0,height=0,label=\"",prefix,(int)a);

      if (!name_table)
        fprintf(stream,"%d\"];\n",GETLEVEL(a));
      else
        { 
          int i,j;
          int var_num = VAR_NUM(GETLEVEL(a));

          /* Search the boundaries of this variable */
          for (i=var_num; i>0 && name_table[i-1] == name_table[var_num]; i--); 
          for (j=var_num; name_table[j+1] == name_table[var_num]; j++); 

          fprintf(stream,"%s",name_table[var_num]);  /* Print name */
          if (i!=j)
            fprintf(stream,"_%d",var_num-i);
 
          if (IS_NEXT_VAR(GETLEVEL(a)))
            fprintf(stream,"'");  /* Print "'" if primed varialbe */

          fprintf(stream,"\"];\n"); /* Finish writing the label */
        }

      /* Connect to sons */

      if (reject == NO_REJECT ||
          !ISLEAF(a->left) ||
          ((node_ptr)a->left->left)->type != NUMBER ||
          ((node_ptr)a->left->left)->left.inttype != reject)
        {
          /* [label=\"0\"] */
          fprintf(stream,"%s%d -> %s%d [style=dotted];\n",  
                          prefix,(int)a,prefix,(int)a->left);

          graph_bdd_aux(stream,a->left,prefix,connect_to,name_table,reject);
        }


      if (reject == NO_REJECT ||
          !ISLEAF(a->right) ||
          ((node_ptr)a->right->left)->type != NUMBER ||
          ((node_ptr)a->right->left)->left.inttype != reject)
        {
          fprintf(stream,"%s%d -> %s%d;\n",   /* [label=\"1\"] */
                            prefix,(int)a,prefix,(int)a->right);
          graph_bdd_aux(stream,a->right,prefix,connect_to,name_table,reject);
        }
    }

}



/* Does not do any printing other than the nodes themself */
void graph_nodes_bdd(FILE *stream,
                     bdd_ptr a,
                     char* prefix,
                     char* connect_to,
                     char **name_table,
                     int reject)
{
  graph_bdd_aux(stream,a,prefix,connect_to,name_table,reject);
  repairmark(a);
}

/* Print a subgraph to a file */
void subgraph_bdd(FILE *stream,
                  bdd_ptr a,
                  char* prefix,
                  char* connect_to,
                  char* label)
{
  fprintf(stream,"subgraph cluster_%s%d {\n",prefix,(int)a);
  fprintf(stream,"              label = \"%s\";\n",label);
  graph_nodes_bdd(stream,a,prefix,connect_to,NULL,NO_REJECT);  /* Print the nodes */
  fprintf(stream,"                      }\n");
}

/* Print bdd a to file fname.  */
void graph_bdd(char* fname,bdd_ptr a)
{
  FILE *stream;

  stream = fopen(fname,"w");

  fprintf(stream,"digraph A {\n");
  subgraph_bdd(stream,a,"",NULL,"What?");
  fprintf(stream,"}\n");

  fclose(stream);
}


/* Print a subgraph to a file */
void sym_subgraph_bdd(FILE *stream,
                      bdd_ptr a,
                      char* prefix,
                      char* connect_to,
                      char* label,
                      char **name_table)
{
  fprintf(stream,"subgraph cluster_%s%d {\n",prefix,(int)a);
  fprintf(stream,"              label = \"%s\";\n",label);
  graph_nodes_bdd(stream,a,prefix,connect_to,name_table,NO_REJECT);  /* Print the nodes */
  fprintf(stream,"                      }\n");
}



/***************************************************************************\
*function: r_shift_bounded							    *
*									    *
* shift a bdd from current vars to next vars				    *
\***************************************************************************/
bdd_ptr r_shift_bounded(bdd_ptr a, int bound)
{
  int alevel;
  bdd_ptr temp1;
  if(ISLEAF(a))return(a);

  /* DONT LOOK in apply cache since the shifted bdds
     are very small */
  /*  if(temp1=find_apply(r_shift_bounded,a,0))return(temp1);*/

  alevel = GETLEVEL(a);
  if (alevel>bound)
    return a;    
  else if(IS_CURRENT_VAR(alevel)){
    temp1 = find_bdd(CURRENT_TO_NEXT(alevel),
		     r_shift_bounded(a->left,bound),
                     r_shift_bounded(a->right,bound));
    /*    insert_apply(r_shift_bounded,a,0,temp1);*/
    return(temp1);
  }
  else
    catastrophe("r_shift_bounded: !IS_CURRENT_VAR(alevel)");
}



bdd_ptr equal_bdd(bdd_ptr a, bdd_ptr b)
{
  return(apply_bdd(equal_node,a,b));
}

bdd_ptr plus_bdd(bdd_ptr a, bdd_ptr b)
{
  return(apply_bdd(plus_node,a,b));
}

bdd_ptr minus_bdd(bdd_ptr a, bdd_ptr b)
{
  return(apply_bdd(minus_node,a,b));
}

/* Define * numeric operation on bdd's */
bdd_ptr times_bdd(bdd_ptr a, bdd_ptr b)
{
  return(apply_bdd(times_node,a,b));
}

/* Define / numeric operation on bdd's */
bdd_ptr divide_bdd(bdd_ptr a, bdd_ptr b)
{
  return(apply_bdd(divide_node,a,b));
}

/* Define mod numeric operation on bdd's */
bdd_ptr mod_bdd(bdd_ptr a, bdd_ptr b)
{
  return(apply_bdd(mod_node,a,b));
}

bdd_ptr union_bdd(bdd_ptr a, bdd_ptr b)
{
  return(apply_bdd(union_node,a,b));
}

bdd_ptr setin_bdd(bdd_ptr a, bdd_ptr b)
{
  return(apply_bdd(setin_node,a,b));
}

bdd_ptr lt_bdd(bdd_ptr a, bdd_ptr b)
{
  return(apply_bdd(lt_node,a,b));
}

bdd_ptr gt_bdd(bdd_ptr a, bdd_ptr b)
{
  return(apply_bdd(gt_node,a,b));
}


node_ptr new_BDD_node(bdd_ptr b)
{
  return new_node(BDD,(node_ptr) b, NIL);
}
node_ptr find_BDD_node(bdd_ptr b)
{
  return find_node(BDD,(node_ptr) b, NIL);
}


char *output_order_file = 0; /* Output file name */

void set_output_order_file(char *fname)
{
   output_order_file = fname;
}




/* Print the order of the variables if requested on the command line */
void output_order()
{
  FILE *f;
  node_ptr l = variables;

  if(!reorder && !output_order_file)
    return;

  if ( !output_order_file )
    set_output_order_file("temp.ord");


  f = fopen(output_order_file,"w");  /* Open output file */
  if(!f)rpterr("cannot open %s for output",output_order_file);


  if (!f) return;

  /* Loop which prints all variables in order into file */
  while(l){
    print_node(f,car(l));
    fprintf(f,"\n");
    l = cdr(l);
  }
  if(fclose(f) == EOF)
    rpterr("cannot close %s",output_order_file);
  if(verbose>1)
    fprintf(stderr,"smv: variable order output to file %s\n",output_order_file);

  if(!reorder)
    exit(0);
}
