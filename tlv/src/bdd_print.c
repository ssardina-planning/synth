/* Print bdds in various ways. It is included by bdd.c */

static  char buf[200];


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
/*    Output in DOTTY format.                                */
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

/**********************************************************************/

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
