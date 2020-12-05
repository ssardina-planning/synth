/* This file contains routines which are mostly called from
   script.c . tlv.c implements tlv-specific commands, whereas script.c
   implements a generalized scripting language. */ 


#include <stdio.h>
#include <storage.h>
#include <string.h>
#include <mystring.h>
#include <node.h>
#include <hash.h>
#include <bdd.h>
#include <bdd2var.h>
#include <assoc.h>
#include <util_err.h>
#include <y.tab.h>
#include <script.h>
#include <symbols.h>
#include "eval.h"
#include "smv.h"
#include "fts.h"

/* Is true if tlv is run from a gui. */
int has_gui = 0;

extern node_ptr variables;

/* Hash tables for tlv-specific commands and functions. */
static hash_ptr built_in_command_hash = NULL;
static hash_ptr built_in_func_hash = NULL;
static hash_ptr built_in_formula_func_hash = NULL;

bdd_ptr sat_bdd_by_var_list(bdd_ptr d, node_ptr l)
{
  node_ptr sym_val;

  if (l == NIL)
    return ONE;
  else {
    if ( ( sym_val = get_symbol(car(l))) == NIL ) {
       start_err();
       fprintf(stderr, "sat_bdd__by_var_list: variable not declared: ");
       print_node(stderr,car(l));
       finish_err();
    }
    else
       /* Recursive call . */
       return and_bdd(sat_bdd_from_state_space( d, bdd_of( sym_val ) ),
                      sat_bdd_by_var_list(d,cdr(l))
                     );
  }
}


/* Print node n to stream at a specific column */
int myprint_node_atcol(FILE *stream,
                       node_ptr n,
                       int prevcol, /* Column where previous print stopped. */
                       int col)
{
  char buf[41];
  int c,p,i;
  buf[0] = 0;

  /* Go to new column */
  for (i=prevcol;i<col;i++)
    fprintf(stream," ");

  /* Print the node into the buffer "buf" */
  c = sprint_node(buf,40,n);

  p = strlen(buf);
  if(!c) p += 3;

  /* Print the buffer on the screen */
  fprintf(stream,"%s",buf);

  /* If there was not enough space in "buf" print "..." */
  if(!c)fprintf(stream,"...");
  return(col + p);
}


/* Print a single satisfying assignment of bdd s, in a human
   readable format. */
void print_sat(bdd_ptr s)
{
  int cur_col =1;
  int prev_col;
  int tab_size = 20;

  node_ptr l = variables;

  /* Find satisfying assignment of bdd */
  s = save_bdd(sparse_sat_bdd(s));

  /* Loop over all variables, and print their value according to s. */
  while (l) {
    /* Let v be the bdd which corresponds to the current variable.
       The leaves of the bdd are the possible values which that variable
       can be assigned to. The path from the root of the bdd to the leaf,
       is the bdd-encoding of the value at the leaf. */
    node_ptr n = car(l);
    node_ptr q = get_program_var_symbol(n);
    bdd_ptr v = save_bdd(bdd_of(q));
    /* bdd_ptr v = eval(n, NIL); */

    node_ptr w, w_next;
    l = cdr(l);

    /* w is the value which is encoded by s. */
    w = (node_ptr) value_bdd(my_if_then_bdd(s, v));

    release_bdd(v);

    /* Repeat the process for v primed. */
    v = r_shift(v);
    w_next = (node_ptr) value_bdd(my_if_then_bdd(s, v));

    /* If w or w_next have a real value, then print. */
    if (w != (node_ptr)(-1) || w_next != (node_ptr) (-1)) {
      prev_col = cur_col;
      if (cur_col >= 62) {
        prev_col = cur_col = 1;
        fprintf(tlvstdout, "\n");
      }
      else if (cur_col > 1)
        cur_col = ((cur_col-2) / tab_size + 1) * tab_size + 1;

      /* Print the name of the variable. */
      cur_col = myprint_node_atcol(tlvstdout, n, prev_col, cur_col);

      fprintf(tlvstdout, " = "); cur_col += 3;

      /* Print the unprimed value before a comma, and the primed variable
         after the comma. */

      if (w != (node_ptr)(-1))
        cur_col = myprint_node_atcol(tlvstdout, w, cur_col, cur_col);

      fprintf(stdout, ","); cur_col++;

      if (w_next != (node_ptr)(-1))
          cur_col = myprint_node_atcol(tlvstdout, w_next, cur_col, cur_col);
    }
  }
  release_bdd(s);
  fprintf(tlvstdout, "\n");
}


/* Evaluate an expression, and interpret it as a boolean.
   Only ZERO is interpreted as FALSE, everything else is true. */
static int eval_node_to_boolean(node_ptr n, node_ptr context)
{
  bdd_ptr temp = eval(n,context);

  /* Only ZERO is interpreted as FALSE. */
  int result = (temp != ZERO);

  release_bdd(temp);

  return result;
}

/* Evaluate node to a bdd. If it is a leaf bdd, then prints
   the value of the leaf. Otherwise, print a satifying assignment
   of the bdd. */
static void eval_node_and_print(node_ptr n)
{
  bdd_ptr r = eval(n,NIL);

  if (ISLEAF(r)) {
    node_ptr leaf_node = (node_ptr) value_bdd(r);

    print_node(tlvstdout, leaf_node);
    /*    if (leaf_node->type == NUMBER)
      fprintf(tlvstdout,"%d",leaf_node->left.inttype);
    else
      fprintf(tlvstdout,"I don't know %d",leaf_node->type); */
  }
  else
    print_sat(r);

  release_bdd(r);
}

/* Implementation of assignment in tlv-basic. Note that
   there are two types of assignment:  Let x :=
   and Let 'x := */
static void tlv_assign_command(node_ptr var, node_ptr val)
{
  extern int verbose;
  extern int save_bdd_list_length;
  node_ptr x;
  node_ptr var_node;

  if (var->type == DEFINE) {
    /* The assignment is of type Let 'x := */

    /* Evaluate value as a parse tree expression. */
    node_ptr res = eval_symbol(val);

    /* Find canonical node for variable. */
    var_node = eval_struct(car(var), NIL);

    /* Insert variable in symbol table. */

    x = get_symbol(var_node);
    if (x) {
      /* Delete variable. */

      /* The value hash is a cache which stores the values
         of parse tree variables, or symbols in DEFINE.
         We must clear this cache To handle the following case

         Let 'a := 1;
         Let 'b := a;

         Print b;  -- values of a and b are evaluated and cached.

         Let 'a := 2;

         Print b;

         If we do not clear the value cache, then the last printing of
         b will output 1 ( since the value will be fetched from the cache )
         although it should have printed 2. */
      clear_value_hash();
      remove_symbol(var_node);
    }
    /* Create variable */
    insert_parse_tree(var_node, res);
  }
  else {
    bdd_ptr res;

    if (verbose > 2)
      fprintf(tlvstderr,"assign: save_list %d\n", save_bdd_list_length);

    /* Evaluate value. */
    res = eval(val, NIL);

    if (verbose > 2)
      fprintf(tlvstderr,"assign: save_list %d\n", save_bdd_list_length);

    /*if (!silent)
      if ( res == ONE )
      fprintf(stderr,"TRUE\n");
      else {
        if (res == ZERO)
        fprintf(stderr,"FALSE\n");
        else
          fprintf(stderr,"Sometimes\n");
      }*/

    /* Get canoncial node for variable name . */
    var_node = eval_struct(var, NIL);

    x = get_symbol(var_node);

    switch (symbol_type(x)) {
    case UNDEFINED_SYMBOL:
      /* Create dynamic variable */
      insert_dynamic_var(var_node, res);
      break;
    case DYNAMIC_VAR_SYMBOL:
      /* Update dynamic variable. */
      release_bdd(bdd_of(x));
      mygarbage();
      update_bdd(x,res);
      break;
    default:
      fprintf(tlvstderr,
              "The assigned variable already exists (e.g. as a program "
              "variable)\n");
      break;
    }
    if (verbose > 2)
      fprintf(tlvstderr, "save_list %d\n", save_bdd_list_length);
  }
}

/* Obsolete function. Probably should be delted. */
void size_command(node_ptr var)
{
  node_ptr var_node,x;

  var_node = eval_struct(var,NIL);
  x = get_symbol(var_node);
  fprintf(tlvstdout, "BDD:\n");

  if (has_bdd(x))
    print_bdd(bdd_of(x), 0);
 }


/* Implement dumping bdd's to files to be read by dotty. */
static void tlv_dump_command(node_ptr a,     /* Bdd to dump. */
                             node_ptr fname, /* File name. */
                             node_ptr bdd)   /* Index */
{
  /* Evaluate to bdd. */
  bdd_ptr dump_me = eval(a,NIL);

  FILE *file_out;
  char new_fname[80];

  /* Generate file name. */
  if (fname==NIL)
     sprintf(new_fname,"out.dot");
  else if (bdd==NIL)
     sprintf(new_fname,"%s.dot",fname->left.strtype->text);
  else
    {
     int i = eval_num(bdd,NIL);
     sprintf(new_fname,"%s%d.dot",fname->left.strtype->text,i);
    }

  /* Dump bdd. */
  new_graph_bdd(new_fname,dump_me);

  release_bdd(dump_me);
}


/* Old version of print_sat. Obsolete. */
void old_print_sat(bdd_ptr s)
{
  int first =1;

  node_ptr l = variables;
  while(l){
    node_ptr n = car(l);
    bdd_ptr v = eval(n,NIL);
    node_ptr w;
    l = cdr(l);

    w = (node_ptr)(value_bdd(my_if_then_bdd(s,v)));
    if (w != (node_ptr)(-1)) {

      if (first)
        first =0;
      else
        fprintf(tlvstdout," &\n");
        
      indent_node(tlvstdout,"",n," = ");
      print_node(tlvstdout,w);
    }

    v = r_shift(v);
    w = (node_ptr)(value_bdd(my_if_then_bdd(s,v)));
    if (w != (node_ptr)(-1)) {

      if (first)
        first =0;
      else
        fprintf(tlvstdout," &\n");
 
      indent_node(tlvstdout,"",n,"' = ");
      print_node(tlvstdout,w);
    }
  }

  fprintf(tlvstdout,"\n");
}


/* Return "zero" value according to whether we want to return
   a bdd or a formula. */
void *typed_return_ZERO(int typ)
{
  if (typ)
    return (void *) NULL;
  else
    return (void *) save_bdd(ZERO);
}

void *return_ZERO(void) 
{
    return (void *) save_bdd(ZERO);
}


void free_value(void *val){
  release_bdd((bdd_ptr)val);
}

/* Declare a new program variable. */
void declare_var(node_ptr n)
{
  extern bdd_ptr vars;

  node_ptr name = eval_struct(car(n),NIL); /* name is variable name (term)
                                                     which could be ARRAY or DOT */

  node_ptr type = cdr(n);        /* type points to "type" node */
  node_ptr val;

  /* Check if name already exists */
  if(get_symbol(name))
      fprintf(tlvstderr,"Redefinition error!!!\n"); 
  else
  {
      extern node_ptr variables;
      extern bdd_ptr global_vars;
      extern bdd_ptr global_id;


      node_ptr tmp;
      bdd_ptr bdd_of_val;
      bdd_ptr temp_bdd;

      /* Handle a single variable with a known name and type .
         n is the context. This inserts the variable into symbol_hash */
      inst_one_variable(name,type,NIL);


      /* This is bad programming, but we now have to fix the order which
         this variable was put when it was prepended into "variables".
         We have to move this from the beginning, to the end of it. */

      tmp = variables;
      variables = cdr(variables);  /* Cut variable from beginning. */

      tmp = find_node(tmp->type, tmp->left.nodetype, NIL);
      variables = append(variables, tmp);       /* Append to end. */

      /* Create bdd for var */
      val = get_symbol(name);
      bdd_of_val = save_bdd(scalar_var(get_program_var_type(val)));
      update_bdd(val, bdd_of_val);


      /* Update global_id and global_vars */
      temp_bdd = save_bdd(and_bdd(global_vars, support_bdd(bdd_of_val)));
      release_bdd(global_vars);
      global_vars = temp_bdd;

      temp_bdd = save_bdd(and_bdd(global_id, 
                                  equal_bdd(bdd_of_val,r_shift(bdd_of_val))
                          ) );
      release_bdd(global_id);
      global_id = temp_bdd;


      /*   vars = calc_list_support(variables);*/

      /* Needed in order to perform reordering. */
      set_var_names();
  }
}

void *tlv_eval(node_ptr parm, node_ptr n, node_ptr context, int typ)
{
  if (typ)
    return (void *) eval_symbol(n);
  else
    return (void *) eval(n, context);
}

/* Returns string (which should be freed) */
char *node_to_file_name(node_ptr n)
{
  char buf[1000];
  char *fname;
  int size;
  node_ptr eval_n = eval_symbol(n);

  /* Convert node into a string. */
  buf[0] = 0;  /* Clear the string */
  sprint_node(buf,1000,eval_n);

  /* Allocate memory and copy string. */
  fname = (char *)malloc((strlen(buf)+1) * sizeof(char));
  strcpy(fname,buf);

  return fname;
}

/***********************************************************************/


node_ptr substitute_car(node_ptr dvar, node_ptr from, node_ptr to)
{
  if (dvar == NIL)
    return NIL;
  else if (dvar == from)
    return to;
  else
    return find_node(dvar->type, substitute_car(dvar->left.nodetype,from,to),
                                 dvar->right.nodetype);
} 

/***********************************************************************/

enum {SIZE_COMMAND, STATS_COMMAND, NSTATE_COMMAND,
      FORMULA_COMMAND, VFORMULA_COMMAND, BFORMULA_COMMAND,
      CNFFORMULA_COMMAND,  CNFFORMULA2_COMMAND, BDD2RESET,
      LOG_COMMAND, APPEND_COMMAND, LOAD_COMMAND, LOAD_RELATIVE_COMMAND,
      PROCS_COMMAND,FUNCS_COMMAND,
      GUI_COMMAND,
      REORDER_COMMAND, REORDER_BITS_COMMAND, REORDER_SIZE_COMMAND,
      WORDER_COMMAND, RORDER_COMMAND,
      FORCE_GARBAGE_COMMAND,
      SAVE_LIST_COMMAND,
      RECORD_COPY_COMMAND,
      RECORD_PRINT_COMMAND,
      DELVAR_COMMAND};

/* tlv specific commands. Called from script.c .
   Return 0 if no such command exists.
   curr_stmt - holds name of command to execute. */
int application_command(node_ptr curr_stmt, node_ptr args)
{
  int command_id;

  /* Find command number which corresponds to name in curr_stmt. */
  node_ptr built_in = find_assoc(built_in_command_hash,curr_stmt);

  if (built_in != NIL)
    command_id = built_in->left.inttype;
  else
    return 0;

  /* case according to command . */
  switch (command_id) {

  case SIZE_COMMAND: print_all_dynamic_vars(); 
                     return 1;

  case NSTATE_COMMAND: 
    {
      /* Print the number of states in a bdd. */

      /* Get symbol of dynamic variable. */
      node_ptr key = eval_struct(car(args),NIL); 
      node_ptr key_val = get_symbol(key); 

      if ( ! key_val )
        rpterr("nstate: Dynamic variable does not exist!");

      if (has_bdd(key_val))
        fprintf(tlvstdout, "%1.0f", count_bdd(bdd_of(key_val)) ); 
      else
        rpterr("nstate: Identifier does not have assocaiated bdd!");

      return 1;
    }
                     
  case FORMULA_COMMAND :  /* form */
    {
      bdd_ptr result = eval(args,NIL);

      dump_bdd_formula(tlvstdout,result,1, "formula" );
      release_bdd(result);
      return 1;
    }

  case VFORMULA_COMMAND :  /* vform */
    {
      /* In contrast to form, in vform the argument must
         be a dynamic variable. The output will be
         assigned to the name of this dynamic variable. */
      node_ptr key = eval_struct(car(args),NIL); 
      node_ptr key_val = get_symbol(key); 
      bdd_ptr result;
      char varname[200];

      /* Put name of variable inside varname. */
      varname[0]=0;
      sprint_node( varname, 200, key );


      if ( ! key_val )
        rpterr("vform: Dynamic variable %s does not exist!", varname);

      if (has_bdd(key_val))
        result = bdd_of(key_val);
      else
        rpterr("vform: Identifier %s does not have assocaiated bdd!", varname);

      dump_bdd_formula(tlvstdout,result,1, varname );
      return 1;
    }

  case BFORMULA_COMMAND : /* bdd2prop */
    {
      bdd_ptr result = eval(args,NIL);

      print_bdd_by_shannon(result);
      release_bdd(result);
      return 1;
    }

  case CNFFORMULA_COMMAND :  /* bdd2cnf */
    {
      bdd_ptr result = eval(args,NIL);

      print_bdd2cnf(result);
      release_bdd(result);
      return 1;
    }

  case CNFFORMULA2_COMMAND : /* bdd2cnfneg */
    {
      node_ptr bdd_list= NIL, l;
      bdd_ptr b,c;

      /* Calculate list of bdds which will be passed to print_bdd2cnf2 */

      if ( length(args) == 1)
        {
          /* The argument is a name of the array. Item 0 contains the
             amount of array elements to be evaluated to bdds. */
 
          node_ptr key, val, array_item, array_name;
          bdd_ptr val_bdd;
          int i,n;    

          /* Calculate number of items in array. */

          /* Find key of array item. */
          array_name = eval_struct(car(args),NIL);
          key = find_node(ARRAY,array_name,find_NUMBER_node(0));

          /* Obtain symbol value. */
          if ( ( val = get_symbol(key) ) == NIL )
             rpterr("bdd2cnfneg: item 0 of array does not exist\n");

          /* Obtain bdd. */
          if ( (val_bdd = bdd_of(val) ) == 0) 
             rpterr("bdd2cnfneg: item 0 of array does not have bdd\n");

          /* Extract number from leaf node of the bdd. */
          n = leaf_value(val_bdd)->left.inttype;

          for (i=1 ; i <= n; i++) {
           
            /* Find key of array item. */
            key = find_node(ARRAY,array_name,find_NUMBER_node(i));

            /* Obtain symbol value. */
            if ( ( val = get_symbol(key) ) == NIL ) 
               rpterr("bdd2cnfneg: item %d of array does not exist\n",i);

            /* Obtain bdd. */
            if ( (b = bdd_of(val) ) == 0) 
               rpterr("bdd2cnfneg: item %d of array does not have bdd\n",i);

            /* Calculate negation of bdd. */
            c = save_bdd(not_bdd(b));

            /* Save to bdd list. */
            bdd_list = cons((node_ptr)c, bdd_list);
          }
        }
      else
        {
        /* The argument list is a list of expressions which should be
           evaluated and translated individually to bdds. */
          for (l= args; l; l = cdr(l)) {
            b = eval(car(l),NIL);
            c = save_bdd(not_bdd(b));
            release_bdd(b);
            bdd_list = cons((node_ptr)c, bdd_list);
          }
        }

      print_bdd2cnf2(bdd_list);

      /* Release list of bdds. */
      for (l= bdd_list; l; l = cdr(l))
        release_bdd(l->left.bddtype);

      return 1;
    }

  case BDD2RESET :
      reset_sharing();
      return 1;

  case LOG_COMMAND:
  case APPEND_COMMAND:

      if (args == NIL)
        { 
          /* Restore output to stdout. */

          if ( tlvstdout != stdout )
            {
               fclose(tlvstdout);
               tlvstdout = stdout;
            }
        }
      else
        {
          char *fname = node_to_file_name(car(args));
          /*          node_ptr file_name = car(args); */
          FILE *out;

   /*     if (file_name == NIL || file_name->type != QUOTE )
             fprintf(tlvstderr,"\nCannot open file: Enter a string as the first argument.\n");
          else if (! (out = fopen(file_name->left.strtype->text, 
                             command_id == LOG_COMMAND ? "w" : "a") 
                ) )
             fprintf(tlvstderr,"\nCannot open file %s ...\n",
                     file_name->left.strtype->text);*/

          if (! (out = fopen(fname,
                             command_id == LOG_COMMAND ? "w" : "a")  ) )
             fprintf(tlvstderr,"\nCannot open file %s ...\n",  fname);

          else
            { /* SUCCESS: we can open the file... */

              /* If tlvstdout refers to a file then close it first. */
              if ( tlvstdout != stdout )  fclose(tlvstdout);

              tlvstdout = out;
            }

          free(fname);
        }

      return 1;

  case LOAD_COMMAND: {
    /*      extern void load_file(char* file_name); */

    /* Translate argument to string. */
    char *fname = node_to_file_name(car(args));
    load_script_file(fname, 0);
    /* Don't free fname, since it is assigned to the variable
       input_file, in order to print error messages.
       free(fname); */
  }
    return 1;

  case LOAD_RELATIVE_COMMAND: {
    char *fname = node_to_file_name(car(args));
    load_script_file(fname, 1);
    return 1;
  }

  case STATS_COMMAND:
    /* print_usage is no longer meaningful, since it measures time relative to
      lasttime, i.e. the last time settime was called */
    /* print_usage(tlvstdout); */
    print_bdd_usage(tlvstdout);
    return 1;

  case PROCS_COMMAND:
      print_procs();
      return 1;

  case FUNCS_COMMAND:
      print_funcs();
      return 1;

  case GUI_COMMAND :
      if (has_gui)
      {
         node_ptr quote_node = car(args);
         char *st = quote_node->left.strtype->text;

         fprintf(tlvstdout,"GUI %s\n",st);
      }
      return 1;

  case REORDER_COMMAND : 
      {
         extern int reorder;  
         extern int reorder_size;

         if (args == NIL) {
            int old_reorder = reorder;  
            int old_reorder_size = reorder_size;
 
            reorder = 1;
            reorder_size = 0;
            force_garbage();            
 
            reorder = old_reorder;
            reorder_size = old_reorder_size;
         }
         else {
             int val = eval_num(args,NIL);

             if (val == 0)
                 reorder = 0;
             else if (val == 1)
                 reorder = 1;
             else
                 rpterr("reorder: value should be 0 or 1\n");
         }
         return 1;
      }

  case REORDER_BITS_COMMAND : 
      {
         extern int reorder_bits;       
         int val = eval_num(args,NIL);
 
         reorder_bits = val;
         return 1;
      }

  case REORDER_SIZE_COMMAND : 
      {
         extern int reorder_size;
         int val = eval_num(args,NIL);
 
         reorder_size = val;
         return 1;
      }

  case WORDER_COMMAND : /* sorder */
    
    if (args != NIL ) 
    {  
          node_ptr file_name = car(args);
          FILE *out;
 
          if (file_name == NIL || file_name->type != QUOTE )
             fprintf(tlvstderr,
                "\nCannot open file: Enter a string as the first argument.\n");
          else {
              write_var_list_to_file(variables,
                                     file_name->left.strtype->text);
              fprintf(tlvstderr,"Writing order file %s .\n",
                      file_name->left.strtype->text);
              return 1;
          }

    }
    break;

  case RORDER_COMMAND :   /* lorder */
    /* Load new order. */
    if (args != NIL ) 
    {  
        extern void push_stream();
        extern void pop_stream();

        node_ptr file_name = car(args);

        if (file_name == NIL || file_name->type != QUOTE )
             fprintf(tlvstderr,
                "\nCannot open file: Enter a string as the first argument.\n");
        else {  
            node_ptr l;
            node_ptr vars;

            /* The push_stream and pop_stream are needed here since
               read_variable_list_from_file uses lex, and this can mess
               up with parsing tlv-Basic. */
            push_stream();
            vars = read_variable_list_from_file(file_name->left.strtype->text);
            pop_stream();            

            /* Check that all variables are defined. */

            for (l= vars; l; l = cdr(l)) {
              node_ptr n = car(l);

              /* Check if the variable is in the symbol_hash. */
              node_ptr q = get_symbol(n);
              if(!q || symbol_type(q) != PROGRAM_VAR_SYMBOL){
                start_err();
                indent_node(tlvstderr,"unknown variable in order file :",n,"");
                finish_err();
                return 0;
              }
            }         

            /* Set order according to vars. */
            fprintf(tlvstderr,"Setting order...\n");
            set_order(vars);
            

            return 1;
        }
    }

    break;

  case FORCE_GARBAGE_COMMAND : 
    force_garbage();
    return 1;
    break;

  case SAVE_LIST_COMMAND : 
    print_save_list_sizes(tlvstderr);
    return 1;
    break;

  case RECORD_COPY_COMMAND : 
    /* Two arguments, "assign" second argument to first. */ 
    if (length(args) == 2) {
      node_ptr to = eval_struct(cadr(args),NIL);
      node_ptr from = eval_struct(car(args),NIL);
      node_ptr dvar;
      node_ptr dvar_scan;

      /* Go over list of dynamic varibles. */
      LOOP_OVER_DYNAMIC_VARS(dvar) {

        /* Loop over the term to see if they have a context
           of from.*/
        for (dvar_scan=dvar; dvar_scan; dvar_scan = car(dvar_scan)) {

          if ( dvar_scan == from) {
            node_ptr new_var = substitute_car(dvar, from, to);
            /*            fprintf(tlvstderr,"Copying to variable ");
            print_node(tlvstderr,new_var);
            fprintf(tlvstderr,"\n"); */
            duplicate_dynamic_var_from(new_var,dvar);
            break;
          }
        }
      }
      return 1;
    }

    break;

  case RECORD_PRINT_COMMAND : 

    /* Print names of all varialbes in record. */
    if (length(args) == 1) {
      node_ptr record = eval_struct(car(args),NIL);
      node_ptr dvar;
      node_ptr dvar_scan;
      int first = 1;

      /* Go over list of dynamic varibles. */
      LOOP_OVER_DYNAMIC_VARS(dvar) {

        /* Loop over the term to see if they have a context
           of from.*/
        for (dvar_scan=dvar; dvar_scan; dvar_scan = car(dvar_scan)) {

          if ( dvar_scan == record ) {
            if (! first)
               fprintf(tlvstderr,", ");
            else
               first = 0;
            
            print_node(tlvstderr,dvar);
            break;
          }
        }

      }
      fprintf(tlvstderr,"\n");
    }
  
    return 1;
    break;

  case DELVAR_COMMAND : 

    /* Delete all varialbes record. */
    if (length(args) == 1) {
      node_ptr var = eval_struct(car(args),NIL);
      node_ptr var_info = get_symbol(var);

      if (var_info) {
        if (symbol_type(var_info) == DYNAMIC_VAR_SYMBOL)
          delete_dynamic_var(var);
        else if(symbol_type(var_info) == PARSE_TREE_SYMBOL)
          remove_symbol(var);
        else {
 	  rpterr("Error: Cannot delete variable %n\n", var);
          return 0;
	}
      }
      else {
	rpterr("Error: variable %n does not exist\n", var);
        return 0;
      }

    }
    return 1;
    break;
  }
  return 0;
}


enum {SUCC_FUNC, PRED_FUNC,
      PRIME_FUNC, UNPRIME_FUNC,
      ASSIGN_FUNC,
      SET_UNION_FUNC, SET_INTERSECTION_FUNC, SET_MINUS_FUNC,
      SET_MEMBER_FUNC,
      SUPPORT_FUNC,
      STRLEN_FUNC, OPS_FUNC,
      RSAT_FUNC, FSAT_FUNC,
      FRSAT_FUNC,
      VALUE_FUNC, ID_FUNC,
      READ_NUM_FUNC,
      IS_TRUE_FUNC, IS_FALSE_FUNC, IS_EQUAL_FUNC,
      IS_FORMULA_FUNC,
      SYS_NUM_FUNC,
      SATISFIABILITY_FUNC};

/* tlv specific functions. Called from script.c .
   Return NULL if no such function exists.
   name - holds name of function. */
void *application_function(node_ptr name,node_ptr args)
{
  int func_id;

  /* Extract function ID from name. */
  node_ptr built_in = find_assoc(built_in_func_hash,name);
       
  if (built_in != NIL)
    func_id = built_in->left.inttype;
  else
    return NULL;

  /* Switch according to function ID. */

  switch (func_id) {

  case SUCC_FUNC:  /* succ */
      if (length(args) != 2) {
          rpterr("Error: succ expects two parameters");
          return return_ZERO();
      }
      else
        {
          bdd_ptr P = eval(car(cdr(args)),NIL);
          bdd_ptr arg2 = eval(car(args),NIL);

          bdd_ptr result = save_bdd(r_collapse(P,arg2));

          release_bdd(P);  release_bdd(arg2);
          return (void *)result;
        }

  case PRED_FUNC:  /* pred */
      if (length(args) != 2) {
          rpterr("Error: pred expects two parameters");
          return return_ZERO();
      }
      else
        {
          bdd_ptr P = eval(car(cdr(args)),NIL);
          bdd_ptr arg2 = eval(car(args),NIL);

          bdd_ptr result = save_bdd(collapse(P,arg2));

          release_bdd(P);  release_bdd(arg2);
          return (void *)result;
        }

  case PRIME_FUNC:  
      if (length(args) != 1) {
          rpterr("Error: prime expects one parameter"); 
          return return_ZERO();
      }
      else
        {
          bdd_ptr arg1 = eval(car(args),NIL);
          bdd_ptr result = save_bdd(r_shift(arg1));

          release_bdd(arg1);
          return (void *)result;
        }

  case UNPRIME_FUNC:
      if (length(args) != 1)  {
          rpterr("Error: prime expects one parameter"); 
          return return_ZERO();
      }
      else
        {
          bdd_ptr arg1 = eval(car(args),NIL);
          bdd_ptr result = save_bdd(f_shift(arg1));

          release_bdd(arg1);
          return (void *)result;
        }

  case ASSIGN_FUNC:
      if (length(args) != 3) { 
          rpterr("Error: assign expects three parameters"); 
          return return_ZERO();
      }
      else
        {
          bdd_ptr result;
          node_ptr dvar = eval_struct(car(cdr(cdr(args))),NIL);
          node_ptr pvar = eval_struct(car(cdr(args)),NIL);

          if ( symbol_type(get_symbol(pvar)) != PROGRAM_VAR_SYMBOL )
            {
              indent_node(tlvstderr,"Variable ",pvar,
                                 " is not a program variable\n");
              return return_ZERO();
            }

          if ( symbol_type(get_symbol(dvar)) != DYNAMIC_VAR_SYMBOL ) 
            {
              indent_node(tlvstderr,"Variable ",dvar,
                                 " is not a dynamic variable\n");
              return return_ZERO();
            }


          {
              bdd_ptr s = eval(dvar,NIL);  /* Bdd of state. */
              bdd_ptr v = eval(pvar,NIL);  /* Bdd of assigned variable. */
              bdd_ptr r = eval(car(args),NIL);   /* Bdd of value expression. */

              /* Bdd of the result of the exrpession */
              bdd_ptr w = leaf_bdd((node_ptr)
                        (value_bdd(if_then_bdd(s,r))));

              /* Bdd of assignment of value to variable */
              bdd_ptr q = setin_bdd(v,w);

              if(q == ZERO){
                indent_node(tlvstderr,
                            "cannot assign ",leaf_value(w)," to variable ");
                print_node(tlvstderr,pvar);
                fprintf(tlvstderr,"\n");
                return return_ZERO();
              }

              /* Change current state to reflect assignment. 
               The "forsome" throws all the bdd nodes with levels that 
               are in v, from the interactive state. */
              result = save_bdd( and_bdd(forsome(support_bdd(v),s),
                                         q));

              release_bdd(v);  release_bdd(s);
              release_bdd(r); 

              return (void *)result;
          }
        }

  /* Functions on bdd's which are viewed as sets of variables.
     A set of variables is represented as a path of bdd variables
     where only the right side can have more variables. Such bdd's
     look like a long stick. */

  case SET_UNION_FUNC:
      if (length(args) != 2) {  
          rpterr("Error: set_union expects two parameters"); 
          return return_ZERO();
      }
      else
        {
          bdd_ptr arg1 = eval(car(cdr(args)),NIL);
          bdd_ptr arg2 = eval(car(args),NIL);

          bdd_ptr result = save_bdd(and_bdd(arg1,arg2));

          release_bdd(arg1);  release_bdd(arg2);
          return (void *)result;
        }

  case SET_INTERSECTION_FUNC:
      if (length(args) != 2) {
          rpterr("Error: set_intersect expects two parameters"); 
          return return_ZERO();
      }
      else
        {
          bdd_ptr arg1 = eval(car(cdr(args)),NIL);
          bdd_ptr arg2 = eval(car(args),NIL);
          bdd_ptr a_min_b = forsome(arg2,arg1);
          bdd_ptr b_min_a = forsome(arg1,arg2);
          bdd_ptr a_or_b  = and_bdd(arg1,arg2); /* This is NOT a mistake. */
          bdd_ptr a_xor_b = or_bdd(a_min_b,b_min_a);
 
          bdd_ptr result = save_bdd(forsome(a_xor_b,a_or_b));

          release_bdd(arg1);  release_bdd(arg2);
          return (void *)result;
        }

  case SET_MINUS_FUNC:
      if (length(args) != 2)  {
          rpterr("Error: set_minus expects two parameter"); 
          return return_ZERO();
      }
      else
        {
          bdd_ptr arg1 = eval(car(cdr(args)),NIL);
          bdd_ptr arg2 = eval(car(args),NIL);

          bdd_ptr result = save_bdd(forsome(arg2,arg1));

          release_bdd(arg1);  release_bdd(arg2);
          return (void *)result;
        }

  case SET_MEMBER_FUNC:
      if (length(args) != 1)  {
          rpterr("Error: set_member expects one parameter"); 
          return return_ZERO();
      }
      else
        {
          bdd_ptr arg1 = eval(car(args),NIL);

          if (ISLEAF(arg1)) {
              /* arg1 is probably an empty set. */
              bdd_ptr result = save_bdd(ONE);
              release_bdd(arg1); 
              return (void *)result;              
          }
          else {
              node_ptr var = get_var_of_bdd_root_level(arg1);

              release_bdd(arg1); 

              if (var == NIL) {
                  rpterr("Error: set_member, variable not found"); 
                  return return_ZERO();
              }
              else {
                  bdd_ptr result = save_bdd(support_bdd(get_bdd_of_var(var)));
                  return (void *)result;              
              }
          }
        }

  case SUPPORT_FUNC:
        /* Create a set of supporting variables from a list of bdd's */
        {
          node_ptr curr_arg = args;
          bdd_ptr new_result,result;
          
          result = save_bdd(ONE);
         
          while (curr_arg) {

            bdd_ptr arg1 = eval(car(curr_arg),NIL);

            bdd_ptr new_result = save_bdd(and_bdd(support_bdd(arg1),result));
            release_bdd(result);
            result = new_result;

            release_bdd(arg1);
       
            curr_arg = cdr(curr_arg);
          }

          return (void *)result;
        }

  case STRLEN_FUNC:
      /* Returns the length of the expression as a string. */

      if (length(args) != 1)  {
          rpterr("Error: strlen expects one parameter"); 
          return return_ZERO();
      }
      else
        {
          char buf[1024];

          node_ptr i_node; 
          node_ptr arg1 = eval_symbol(car(args));
  
          sprint_node(buf,1024,arg1); 
 
          i_node = find_NUMBER_node(strlen(buf));

          return (void *)save_bdd(leaf_bdd(i_node) ) ;
        }

  case OPS_FUNC:
      if (length(args) != 1)  {
          rpterr("Error: ops expects one parameter"); 
          return return_ZERO();
      }
      else
        {
          node_ptr arg1 = eval_symbol(car(args));
 
          node_ptr i_node = find_NUMBER_node(number_of_operands(arg1));

          return (void *)save_bdd(leaf_bdd(i_node) ) ;
        }


  /* Various kinds of satisfying bdd's . */

  case RSAT_FUNC:
      if (length(args) != 1) {
          rpterr("Error: rsat expects one parameter"); 
          return return_ZERO();
      }
      else
        {
          bdd_ptr arg1 = eval(car(args),NIL);
          bdd_ptr result = save_bdd(rand_sat_bdd(arg1));

          release_bdd(arg1);
          return (void *)result;
        }

  case FSAT_FUNC:
      switch (length(args)){
        case 1:
          {
          bdd_ptr arg1 = eval(car(args),NIL);
          bdd_ptr result = save_bdd(sat_bdd_by_var_list(arg1,variables));

          release_bdd(arg1);
          return (void *)result;
          }
        case 2:
          {
          bdd_ptr arg1 = eval(car(cdr(args)),NIL);
          bdd_ptr arg2 = eval(car(args),NIL);
          bdd_ptr result = save_bdd(sat_bdd_from_set(arg1,arg2));

          release_bdd(arg1);
          release_bdd(arg2);
          return (void *)result;
          }
        default: {
          rpterr("Error: fsat expects one or two parameters"); 
          return return_ZERO();
        }
      } 

  case FRSAT_FUNC:
      if (length(args) != 1) {
          rpterr("Error: frsat expects one parameter");   
          return return_ZERO();
      }
      else
        {
          extern bdd_ptr global_id;
          bdd_ptr arg1 = eval(car(args),NIL);

          /* Get random satisfying bdd. */
          bdd_ptr rand_bdd = rand_original_sat_bdd(arg1);

          /* Limit the bdd such that the representation is valid. */
          bdd_ptr result = save_bdd(limit_to(rand_bdd, global_id));

          release_bdd(arg1);
          return (void *)result;
        }

  case VALUE_FUNC:
      switch (length(args)){
      case 1:
        {
          /* This just returns the value of some non zero leaf */

          bdd_ptr arg1 = eval(car(args),NIL);
          node_ptr v = leaf_value_bdd(arg1);

          release_bdd(arg1);
          return save_bdd(leaf_bdd(v));
        }
      case 2:
        {
          /* This obtains the value of a particular system variable
             from a bdd inside a dynamic variable. */

          node_ptr result;
          node_ptr dvar = eval_struct(car(cdr(args)),NIL);
          node_ptr pvar = eval_struct(car(args),NIL);

          if ( symbol_type(get_symbol(pvar)) != PROGRAM_VAR_SYMBOL )
            {
              indent_node(tlvstderr,"Variable ",pvar,
                                 " is not a program variable\n");
              return return_ZERO();
            }

          if ( symbol_type(get_symbol(dvar)) != DYNAMIC_VAR_SYMBOL ) 
            {
              indent_node(tlvstderr,"Variable ",dvar,
                                 " is not a dynamic variable\n");
              return return_ZERO();
            }


          {
              bdd_ptr s = eval(dvar,NIL);  /* Bdd of state. */
              bdd_ptr v = eval(pvar,NIL);  /* Bdd of assigned variable. */

              result = leaf_value_bdd(my_if_then_bdd(s,v));
                           
              release_bdd(v);  release_bdd(s);

              if (result != (node_ptr)(-1))
                return (void *)save_bdd(leaf_bdd(result));
              else
                return (void *)save_bdd(leaf_bdd(string_to_atom("novalue")));
          }
        }
      default: {
          rpterr("Error: value expects one or two parameters"); 
          return return_ZERO();
        }
      }

  case ID_FUNC:
    /* Returns bdd which preserves variables in the bdd of the argument. */

      if (length(args) != 1)  {
          rpterr("Error: id expects one parameter"); 
          return return_ZERO();
      }
      else
      {
          extern bdd_ptr global_vars;
          extern bdd_ptr global_id;

          bdd_ptr arg1 = eval(car(args),NIL);
          bdd_ptr set_to_quantify = forsome(arg1, global_vars);
          bdd_ptr result = save_bdd (forsome( set_to_quantify, global_id));

          release_bdd(arg1);
          return (void *)result;
      }

  case READ_NUM_FUNC:
    /* Read number interactively from user. 
       Returns bdd. */
      {
          char buf[100];
          int i;
          node_ptr i_node; 

          /* Read string from user. */
          fgets(buf, 100, stdin);

          i = atoi(buf);  /* Convert to integer. */

          /* Return as bdd. */
          i_node = find_NUMBER_node(i);
          return (void *)save_bdd(leaf_bdd(i_node) ) ;
      }
  case IS_TRUE_FUNC:
    if (length(args) != 1)  {
      rpterr("Error: is_true expects one parameter"); 
      return return_ZERO();
    }
    else {
      bdd_ptr arg1 = eval(car(args),NIL);
      int result = (arg1 == ONE);
      node_ptr result_node = find_NUMBER_node(result);

      release_bdd(arg1);
      return (void *)save_bdd(leaf_bdd(result_node));
    }
  case IS_FALSE_FUNC:
    if (length(args) != 1)  {
      rpterr("Error: is_false expects one parameter"); 
      return return_ZERO();
    }
    else {
      bdd_ptr arg1 = eval(car(args),NIL);
      int result = (arg1 == ZERO);
      node_ptr result_node = find_NUMBER_node(result);

      release_bdd(arg1);
      return (void *)save_bdd(leaf_bdd(result_node));
    }

  case IS_EQUAL_FUNC:
    if (length(args) != 2)  {
      rpterr("Error: is_equal expects 2 parameters"); 
      return return_ZERO();
    }
    else {
      bdd_ptr arg1 = eval(car(args),NIL);
      bdd_ptr arg2 = eval(car(cdr(args)), NIL);

      int result = (arg1 == arg2);
      node_ptr result_node = find_NUMBER_node(result);

      release_bdd(arg1);
      release_bdd(arg2);
      return (void *) save_bdd(leaf_bdd(result_node));
    }
    
  case IS_FORMULA_FUNC:
    if (length(args) != 1)  {
      rpterr("Error: is_formula expects one parameter"); 
      return return_ZERO();
    }
    else {
      /* Return true if the argument is the name of a parse-tree variable. */

      node_ptr var_name = eval_struct(car(args),NIL);

      int result = symbol_type(get_symbol(var_name)) == PARSE_TREE_SYMBOL ;
      node_ptr result_node = find_NUMBER_node(result);

      return (void *)save_bdd(leaf_bdd(result_node));
    }
      
  case SYS_NUM_FUNC:
    {
      char buf1[200];
      char buf2[200];

      node_ptr arg1 = eval_symbol(car(args));
      fts f;
      int result = 0;
      node_ptr result_node;

      buf1[0] = 0;
      sprint_node(buf1,200, arg1);

      LOOP_OVER_FTS_LIST(f) {
        buf2[0] = 0;
        sprint_node(buf2,200, FTS_NAME(f));

        if (strcmp(buf1,buf2) == 0 ) {
          result = FTS_NUM(f);
          break;
        }          
      }

      result_node = find_NUMBER_node(result);
      return (void *)save_bdd(leaf_bdd(result_node));
    }

  case SATISFIABILITY_FUNC:
    { /* Integration of SAT solver. */

      node_ptr var_name = eval_struct(car(cdr(args)),NIL);
      node_ptr var_info = get_symbol(var_name);
      node_ptr counter_example_name = eval_struct(car(args),NIL);

      if (symbol_type(var_info) != PARSE_TREE_SYMBOL) {
          rpterr("Error: SAT expects first parameter to be a formula (parse tree)"); 
          return return_ZERO();
      }
      else 
      {
          /* Obtain the formula from the information about the formula variable. */
          node_ptr formula = parse_tree_of(var_info);
      
          int result = 1; /* = sat_solve(formula, counter_example_name);

                           Invoke SAT solver, get result, and
                           convert counter example back to a formula. */
      
          node_ptr result_node = find_NUMBER_node(result);
          return (void *)save_bdd(leaf_bdd(result_node));
      }
    }

  }


  return NULL;
}


/*  These were once function for manipulating parse trees/formulas.

      else if (!strcmp(fun,"car"))
        {
          node_ptr res = eval_symbol(car(ops));
          return car(res);
        }
      else if (!strcmp(fun,"cdr"))
        {
          node_ptr res = eval_symbol(car(ops));
          return cdr(res);
          } 
      else if (!strcmp(fun,"union2"))
        {
          node_ptr s1 = eval_symbol(car(cdr(ops)));
          node_ptr s2 = eval_symbol(car(ops));

          return union_node(s1,s2);
        }
      else if (!strcmp(fun,"minus"))
        {
          node_ptr s1 = eval_symbol(car(cdr(ops)));
          node_ptr s2 = eval_symbol(car(ops));

          return set_minus_node(s1,s2);
        }
      else if (!strcmp(fun,"member"))
        {
          node_ptr s1 = eval_symbol(car(cdr(ops)));
          node_ptr s2 = eval_symbol(car(ops));

          return setin_node(s1,s2);
        }
      else if (!strcmp(fun,"sing"))
        {
          node_ptr s = eval_symbol(car(ops));

          return cons(s,NIL);
        }
      else if (!strcmp(fun,"nil"))
        {
          return NIL;
          } */


enum {
  ROOT_FUNC, OP_FUNC,
  ADDNEG_FUNC, AND_FUNC, OR_FUNC, IMPLIES_FUNC, IFF_FUNC, EQUAL_FUNC,
  NOTEQUAL_FUNC, LT_FUNC, GT_FUNC, LE_FUNC, GE_FUNC,
  POSITIVE_FUNC,
  READ_STRING_FUNC,
  LTL_E_FUNC, LTL_A_FUNC, LTL_N_FUNC, LTL_U_FUNC, LTL_W_FUNC, LTL_S_FUNC,
  LTL_B_FUNC, LTL_H_FUNC, LTL_O_FUNC, LTL_P_FUNC, LTL_WP_FUNC,
  ARRAY_LOOKUP_FUNC, DOT_FUNC, QUOTE_FUNC
};

void *formula_application_function(node_ptr name, node_ptr args)
{
  int func_id;

  /* Extract function ID from name. */
  node_ptr built_in = find_assoc(built_in_formula_func_hash, name);

  if (built_in != NIL)
    func_id = built_in->left.inttype;
  else
    return NULL;

  /* Switch according to function ID. */

  switch (func_id) {
  case ROOT_FUNC: {
    /* Return string of root operator of parse tree.  */
    node_ptr res = eval_symbol(car(args));
    return (void *) string_to_atom(op_string(res));
  }
  case OP_FUNC: {
    /* op(i,n) - return i-th operand of n.  */
    int op_no = eval_num(car(cdr(args)),NIL);
    node_ptr parm = eval_symbol(car(args));
    int max_op = number_of_operands(parm);
    node_ptr result;

    if (op_no > max_op || op_no < 1)
      result = string_to_atom("");
    else
      switch (max_op) {
      case 1:
        result = (op_no == 1 ? car(parm) : string_to_atom(""));
        break;
      case 2:
        result = (op_no == 1 ? car(parm): op_no == 2 ? cdr(parm) :
                  string_to_atom(""));
        break;
      case 3:
        switch (op_no) {
        case 1: result = car(car(parm)); break;
        case 2: result = cdr(car(parm)); break;
        case 3: result = cdr(parm); break;
        default: result = string_to_atom(""); break;
        }
        break;
      }
    return (void *)result;
  }
  case ADDNEG_FUNC: {
    /* Add a negation as the root of a parse tree.  */
    node_ptr s = eval_symbol(car(args));
    return (void *) find_node(NOT,s,NIL);
  }
  case AND_FUNC: {
    node_ptr s1 = eval_symbol(car(cdr(args)));
    node_ptr s2 = eval_symbol(car(args));
    return (void *) new_node(AND,s1,s2);
  }
  case OR_FUNC: {
    node_ptr s1 = eval_symbol(car(cdr(args)));
    node_ptr s2 = eval_symbol(car(args));
    return (void *) new_node(OR,s1,s2);
  }
  case IMPLIES_FUNC: {
    node_ptr s1 = eval_symbol(car(cdr(args)));
    node_ptr s2 = eval_symbol(car(args));
    return (void *) new_node(IMPLIES,s1,s2);
  }
  case IFF_FUNC: {
    node_ptr s1 = eval_symbol(car(cdr(args)));
    node_ptr s2 = eval_symbol(car(args));
    return (void *) new_node(IFF,s1,s2);
  }
  case EQUAL_FUNC: {
    node_ptr s1 = eval_symbol(car(cdr(args)));
    node_ptr s2 = eval_symbol(car(args));
    return (void *) new_node(EQUAL,s1,s2);
  }
  case NOTEQUAL_FUNC: {
    node_ptr s1 = eval_symbol(car(cdr(args)));
    node_ptr s2 = eval_symbol(car(args));
    return (void *) new_node(NOTEQUAL,s1,s2);
  }
  case LT_FUNC: {
    node_ptr s1 = eval_symbol(car(cdr(args)));
    node_ptr s2 = eval_symbol(car(args));
    return (void *) new_node(LT,s1,s2);
  }
  case GT_FUNC: {
    node_ptr s1 = eval_symbol(car(cdr(args)));
    node_ptr s2 = eval_symbol(car(args));
    return (void *) new_node(GT,s1,s2);
  }
  case LE_FUNC: {
    node_ptr s1 = eval_symbol(car(cdr(args)));
    node_ptr s2 = eval_symbol(car(args));
    return (void *) new_node(LE,s1,s2);
  }
  case GE_FUNC: {
    node_ptr s1 = eval_symbol(car(cdr(args)));
    node_ptr s2 = eval_symbol(car(args));
    return (void *) new_node(GE,s1,s2);
  }
  case LTL_E_FUNC: {
    node_ptr s = eval_symbol(car(args));
    return (void *) find_node(EVENTUALLY, s, NIL);
  }
  case LTL_A_FUNC: {
    node_ptr s = eval_symbol(car(args));
    return (void *) find_node(ALWAYS, s, NIL);
  }
  case LTL_N_FUNC: {
    node_ptr s = eval_symbol(car(args));
    return (void *) find_node(NEXT_LTL, s, NIL);
  }
  case LTL_U_FUNC: {
    node_ptr s1 = eval_symbol(car(cdr(args)));
    node_ptr s2 = eval_symbol(car(args));
    return (void *) find_node(LTLUNTIL, s1, s2);
  }
  case LTL_W_FUNC: {
    node_ptr s1 = eval_symbol(car(cdr(args)));
    node_ptr s2 = eval_symbol(car(args));
    return (void *) find_node(WAITINGFOR, s1, s2);
  }
  case LTL_S_FUNC: {
    node_ptr s1 = eval_symbol(car(cdr(args)));
    node_ptr s2 = eval_symbol(car(args));
    return (void *) find_node(SINCE, s1, s2);
  }
  case LTL_B_FUNC: {
    node_ptr s1 = eval_symbol(car(cdr(args)));
    node_ptr s2 = eval_symbol(car(args));
    return (void *) find_node(BACKTO, s1, s2);
  }
  case LTL_H_FUNC: {
    node_ptr s = eval_symbol(car(args));
    return (void *) find_node(HASALWAYSBEEN, s, NIL);
  }
  case LTL_O_FUNC: {
    node_ptr s = eval_symbol(car(args));
    return (void *) find_node(ONCE, s, NIL);
  }
  case LTL_P_FUNC: {
    node_ptr s = eval_symbol(car(args));
    return (void *) find_node(PREVIOUSLY, s, NIL);
  }
  case LTL_WP_FUNC: {
    node_ptr s = eval_symbol(car(args));
    return (void *) find_node(WEAKPREVIOUS, s, NIL);
  }

  case ARRAY_LOOKUP_FUNC: {
    node_ptr arr = eval_symbol(car(cdr(args)));
    node_ptr index = eval_symbol(car(args));
    return (void *) find_node(ARRAY, arr, index);
  }
  case DOT_FUNC: {
    node_ptr trm = eval_symbol(car(cdr(args)));
    node_ptr atm = eval_symbol(car(args));
    return (void *) find_node(DOT, trm, atm);
  }
  case QUOTE_FUNC: {
    node_ptr expr = eval_symbol(car(args));
    return expr;
  }
/*
  case PARSE_FILE_FUNC: {
    char *filename = node_to_file_name(car(args));
    node_ptr result;
    parse_file(filename, &result);
    if (result == NULL)
      printf("Parsed file. Result is NULL!\n");
    else
      printf("Parsed file. Returning parse tree..\n");
    return (void *) result;
  }
*/
/*
  else if (!strcmp(fun,"or"))
    return new_node(OR,s1,s2);
  else if (!strcmp(fun,"iff"))
    return new_node(IFF,s1,s2);
  else if (!strcmp(fun,"implies"))
    return new_node(IMPLIES,s1,s2);
*/

  case POSITIVE_FUNC: {
    /* Return positive form of ltl formula. */
    node_ptr res = eval_symbol(car(args));
    return (void *) positive_form(res);
  }
  case READ_STRING_FUNC: {
    /* Read a string from the user. */
    char buf[1000];
    int len;
    buf[0] = 0; /* Clear buffer */

    fgets(buf, 1000, stdin);  /* Read it! */

    /* If there is a newline at the end, remove it */
    len = strlen(buf);
    if (buf[len-1] == '\n') buf[len-1] = 0;
    return (void *) string_to_atom(buf);
  }
  }
  return (void *) NULL;
}




/* Initialize this file. */
void init_tlv(void)
{

  /* Associate names of functions and commands to their ID's. */

  if (!built_in_func_hash) {

    /* Functions which return bdds. */

    built_in_func_hash = new_assoc();

    insert_assoc(built_in_func_hash,string_to_atom("succ"),
                                  find_NUMBER_node(SUCC_FUNC));
    insert_assoc(built_in_func_hash,string_to_atom("pred"),
                                  find_NUMBER_node(PRED_FUNC));

    insert_assoc(built_in_func_hash,string_to_atom("prime"),
                                  find_NUMBER_node(PRIME_FUNC));
    insert_assoc(built_in_func_hash,string_to_atom("unprime"),
                                  find_NUMBER_node(UNPRIME_FUNC));

    insert_assoc(built_in_func_hash,string_to_atom("assign"),
                                  find_NUMBER_node(ASSIGN_FUNC));

    insert_assoc(built_in_func_hash,string_to_atom("set_union"),
                                  find_NUMBER_node(SET_UNION_FUNC));
    insert_assoc(built_in_func_hash,string_to_atom("set_intersect"),
                                  find_NUMBER_node(SET_INTERSECTION_FUNC));
    insert_assoc(built_in_func_hash,string_to_atom("set_minus"),
                                  find_NUMBER_node(SET_MINUS_FUNC));
    insert_assoc(built_in_func_hash,string_to_atom("set_member"),
                                  find_NUMBER_node(SET_MEMBER_FUNC));

    insert_assoc(built_in_func_hash,string_to_atom("support"),
                                  find_NUMBER_node(SUPPORT_FUNC));
    insert_assoc(built_in_func_hash,string_to_atom("vset"),
                                  find_NUMBER_node(SUPPORT_FUNC));

    insert_assoc(built_in_func_hash,string_to_atom("strlen"),
                                  find_NUMBER_node(STRLEN_FUNC));
    insert_assoc(built_in_func_hash,string_to_atom("ops"),
                                  find_NUMBER_node(OPS_FUNC));

    insert_assoc(built_in_func_hash,string_to_atom("rsat"),
                                  find_NUMBER_node(RSAT_FUNC));
    insert_assoc(built_in_func_hash,string_to_atom("fsat"),
                                  find_NUMBER_node(FSAT_FUNC));
    insert_assoc(built_in_func_hash,string_to_atom("frsat"),
                                  find_NUMBER_node(FRSAT_FUNC));

    insert_assoc(built_in_func_hash,string_to_atom("value"),
                                  find_NUMBER_node(VALUE_FUNC));

    insert_assoc(built_in_func_hash,string_to_atom("id_of"),
                                  find_NUMBER_node(ID_FUNC));

    insert_assoc(built_in_func_hash,string_to_atom("read_num"),
                                  find_NUMBER_node(READ_NUM_FUNC));

    insert_assoc(built_in_func_hash,string_to_atom("is_true"),
                                  find_NUMBER_node(IS_TRUE_FUNC));
    insert_assoc(built_in_func_hash,string_to_atom("is_false"),
                                  find_NUMBER_node(IS_FALSE_FUNC));
    insert_assoc(built_in_func_hash,string_to_atom("is_equal"),
                                  find_NUMBER_node(IS_EQUAL_FUNC));

    insert_assoc(built_in_func_hash,string_to_atom("is_formula"),
                                  find_NUMBER_node(IS_FORMULA_FUNC));

    insert_assoc(built_in_func_hash,string_to_atom("sys_num"),
                                  find_NUMBER_node(SYS_NUM_FUNC));

    insert_assoc(built_in_func_hash,string_to_atom("SAT"),
                                  find_NUMBER_node(SATISFIABILITY_FUNC));


    /* Functions of formulas. */

    built_in_formula_func_hash = new_assoc();

    insert_assoc(built_in_formula_func_hash, string_to_atom("root"),
                 find_NUMBER_node(ROOT_FUNC));
    insert_assoc(built_in_formula_func_hash, string_to_atom("op"),
                 find_NUMBER_node(OP_FUNC));

    insert_assoc(built_in_formula_func_hash, string_to_atom("addneg"),
                 find_NUMBER_node(ADDNEG_FUNC));
    insert_assoc(built_in_formula_func_hash, string_to_atom("and"),
                 find_NUMBER_node(AND_FUNC));
    insert_assoc(built_in_formula_func_hash, string_to_atom("or"),
                 find_NUMBER_node(OR_FUNC));
    insert_assoc(built_in_formula_func_hash, string_to_atom("implies"),
                 find_NUMBER_node(IMPLIES_FUNC));
    insert_assoc(built_in_formula_func_hash, string_to_atom("iff"),
                 find_NUMBER_node(IFF_FUNC));
    insert_assoc(built_in_formula_func_hash, string_to_atom("equal"),
                 find_NUMBER_node(EQUAL_FUNC));
    insert_assoc(built_in_formula_func_hash, string_to_atom("notequal"),
                 find_NUMBER_node(NOTEQUAL_FUNC));
    insert_assoc(built_in_formula_func_hash, string_to_atom("lt"),
                 find_NUMBER_node(LT_FUNC));
    insert_assoc(built_in_formula_func_hash, string_to_atom("gt"),
                 find_NUMBER_node(GT_FUNC));
    insert_assoc(built_in_formula_func_hash, string_to_atom("le"),
                 find_NUMBER_node(LE_FUNC));
    insert_assoc(built_in_formula_func_hash, string_to_atom("ge"),
                 find_NUMBER_node(GE_FUNC));

    insert_assoc(built_in_formula_func_hash, string_to_atom("array-lookup"),
                 find_NUMBER_node(ARRAY_LOOKUP_FUNC));
    insert_assoc(built_in_formula_func_hash, string_to_atom("member-of"),
                 find_NUMBER_node(DOT_FUNC));
    insert_assoc(built_in_formula_func_hash, string_to_atom("quote"),
                 find_NUMBER_node(QUOTE_FUNC));

    /* insert_assoc(built_in_formula_func_hash, string_to_atom("parse-file"), */
    /*              find_NUMBER_node(PARSE_FILE_FUNC)); */

    insert_assoc(built_in_formula_func_hash, string_to_atom("eventually"),
                 find_NUMBER_node(LTL_E_FUNC));
    insert_assoc(built_in_formula_func_hash, string_to_atom("always"),
                 find_NUMBER_node(LTL_A_FUNC));
    insert_assoc(built_in_formula_func_hash, string_to_atom("ltl_next"),
                 find_NUMBER_node(LTL_N_FUNC));
    insert_assoc(built_in_formula_func_hash, string_to_atom("ltl_until"),
                 find_NUMBER_node(LTL_U_FUNC));
    insert_assoc(built_in_formula_func_hash, string_to_atom("waitfor"),
                 find_NUMBER_node(LTL_W_FUNC));
    insert_assoc(built_in_formula_func_hash, string_to_atom("since"),
                 find_NUMBER_node(LTL_S_FUNC));
    insert_assoc(built_in_formula_func_hash, string_to_atom("backto"),
                 find_NUMBER_node(LTL_B_FUNC));
    insert_assoc(built_in_formula_func_hash, string_to_atom("hasalways"),
                 find_NUMBER_node(LTL_H_FUNC));
    insert_assoc(built_in_formula_func_hash, string_to_atom("once"),
                 find_NUMBER_node(LTL_O_FUNC));
    insert_assoc(built_in_formula_func_hash, string_to_atom("previous"),
                 find_NUMBER_node(LTL_P_FUNC));
    insert_assoc(built_in_formula_func_hash, string_to_atom("wprevious"),
                 find_NUMBER_node(LTL_WP_FUNC));

    insert_assoc(built_in_formula_func_hash, string_to_atom("positive"),
                 find_NUMBER_node(POSITIVE_FUNC));
    insert_assoc(built_in_formula_func_hash, string_to_atom("read_string"),
                 find_NUMBER_node(READ_STRING_FUNC));

    /* Commands. */

    built_in_command_hash = new_assoc();

    insert_assoc(built_in_command_hash,string_to_atom("sz"),
                                  find_NUMBER_node(SIZE_COMMAND));
    insert_assoc(built_in_command_hash,string_to_atom("numstate"),
                                  find_NUMBER_node(NSTATE_COMMAND));

    insert_assoc(built_in_command_hash,string_to_atom("form"),
                                  find_NUMBER_node(FORMULA_COMMAND));
    insert_assoc(built_in_command_hash,string_to_atom("vform"),
                                  find_NUMBER_node(VFORMULA_COMMAND));
    insert_assoc(built_in_command_hash,string_to_atom("bdd2prop"),
                                  find_NUMBER_node(BFORMULA_COMMAND));
    insert_assoc(built_in_command_hash,string_to_atom("bdd2cnf"),
                                  find_NUMBER_node(CNFFORMULA_COMMAND));
    insert_assoc(built_in_command_hash,string_to_atom("bdd2cnfneg"),
                                  find_NUMBER_node(CNFFORMULA2_COMMAND));

    insert_assoc(built_in_command_hash,string_to_atom("bdd2reset"),
                                  find_NUMBER_node(BDD2RESET));

    insert_assoc(built_in_command_hash,string_to_atom("log"),
                                  find_NUMBER_node(LOG_COMMAND));
    insert_assoc(built_in_command_hash,string_to_atom("append"),
                                  find_NUMBER_node(APPEND_COMMAND));
    insert_assoc(built_in_command_hash,string_to_atom("Load"),
                                  find_NUMBER_node(LOAD_COMMAND));
    insert_assoc(built_in_command_hash,string_to_atom("Load_Relative"),
                                  find_NUMBER_node(LOAD_RELATIVE_COMMAND));

    insert_assoc(built_in_command_hash,string_to_atom("Stats"),
                                  find_NUMBER_node(STATS_COMMAND));


    insert_assoc(built_in_command_hash,string_to_atom("procs"),
                                  find_NUMBER_node(PROCS_COMMAND));
    insert_assoc(built_in_command_hash,string_to_atom("funcs"),
                                  find_NUMBER_node(FUNCS_COMMAND));

    insert_assoc(built_in_command_hash,string_to_atom("gui"),
                                  find_NUMBER_node(GUI_COMMAND));

    insert_assoc(built_in_command_hash,string_to_atom("reorder"),
                                  find_NUMBER_node(REORDER_COMMAND));
    insert_assoc(built_in_command_hash,string_to_atom("reorder_bits"),
                                  find_NUMBER_node(REORDER_BITS_COMMAND));
    insert_assoc(built_in_command_hash,string_to_atom("reorder_size"),
                                  find_NUMBER_node(REORDER_SIZE_COMMAND));

    /* Save and load order */
    insert_assoc(built_in_command_hash,string_to_atom("sorder"),
                                  find_NUMBER_node(WORDER_COMMAND));
    insert_assoc(built_in_command_hash,string_to_atom("lorder"),
                                  find_NUMBER_node(RORDER_COMMAND));

    insert_assoc(built_in_command_hash,string_to_atom("garbage"),
                                  find_NUMBER_node(FORCE_GARBAGE_COMMAND));

    insert_assoc(built_in_command_hash,string_to_atom("savelist"),
                                  find_NUMBER_node(SAVE_LIST_COMMAND));

    insert_assoc(built_in_command_hash,string_to_atom("rcopy"),
                                  find_NUMBER_node(RECORD_COPY_COMMAND));
    insert_assoc(built_in_command_hash,string_to_atom("rprint"),
                                  find_NUMBER_node(RECORD_PRINT_COMMAND));

    insert_assoc(built_in_command_hash,string_to_atom("delvar"),
                                  find_NUMBER_node(DELVAR_COMMAND));
  }

  /* Assign function pointers in script.c to point to functions
     which have been implemented in this file. */

  script_eval_node_to_boolean = eval_node_to_boolean;
  script_eval_node = tlv_eval;
  script_eval_num = eval_num;
  script_eval_node_to_symbol_key = eval_struct;

  script_null_value = typed_return_ZERO;
  script_free_value = free_value;

  script_eval_node_and_print = eval_node_and_print;
  script_assign_command = tlv_assign_command;
  script_dump_command = tlv_dump_command;
  script_declare_var = declare_var;

  script_application_command = application_command;
  script_application_function[0] = application_function;
  script_application_function[1] = formula_application_function;
}
