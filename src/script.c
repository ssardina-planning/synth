/* There are several parts to this file

     Part I : Implementation of specific generic tlv commands:
               To - to_command , Func - func_command , Print - print_command,
               Let - assign_command,  Quit - exit_command.

     Part II : Script execution - run_stmts, run_1_stmt

     Part III : Running procedures and function: map_params,
                run_command, run_func

     Part IV : load_script, go_interactive, init_script

   Changes:
   11/17/2003: Ittai -
     Added dynamic default parameters to procedures/functions. "dynamic" means
     that a parameter's default value is an expression that is evaluated
     whenever the procedure/function is called (rather than when the procedure/
     function is defined).

   The function gnu_getcwd defined here is taken from the gnu libc documentation
 */

#include <string.h>
#include <unistd.h>
#include <errno.h>
#include <node.h>
#include <y.tab.h>
#include <node_smv.h>
#include <storage.h>
#include <hash.h>
#include <assoc.h>
#include <stdlib.h>
#include <stdio.h>
#include <util_err.h>
#include <string.h>
#include <mystring.h>
#include <script.h>
#include <symbols.h>
#include <eval.h>
#include "platform.h"

int silent;

/* Hash tables which contain definitions of user defined
   procedures and functions. */
static hash_ptr progs_hash;
static hash_ptr funcs_hash[2];

static char *current_load_path = NULL;

#define BUFSIZE 1000
char buf[BUFSIZE];

/* Pointers to functions. tlv.c assigns into these pointers. */

void *(*script_eval_node)(node_ptr parm, node_ptr n,node_ptr context, int typ);
int (*script_eval_node_to_boolean)(node_ptr n, node_ptr context);
int (*script_eval_num)(node_ptr num,node_ptr context);
node_ptr (*script_eval_node_to_symbol_key)
           (node_ptr n, node_ptr context);


void *(*script_null_value)(int typ);
void (*script_free_value)(void *val);

void (*script_insert_dynamic_var)(node_ptr parm_key,void *val);

void (*script_eval_node_and_print)(node_ptr n);
void (*script_assign_command)(node_ptr lhs,
                               node_ptr rhs);
void (*script_dump_command)(node_ptr n,
                             node_ptr fname,
                             node_ptr b);
void (*script_declare_var)(node_ptr n);


int (*script_application_command)(node_ptr stmt,node_ptr args);
void *(*script_application_function[5])(node_ptr name,node_ptr args);


/* Lists of all defined procedures and functions. */
static node_ptr list_of_procs;
static node_ptr list_of_funcs;

/* Print list of nodes. */
void print_node_list(node_ptr l)
{
  for(;l;l=cdr(l)) {
      print_node(tlvstdout,car(l));
      fprintf(tlvstdout,"\n");
  }
}

/* Print all defined procedures. */
void print_procs(void)
{
  fprintf(tlvstdout,"Procedures:\n");

  print_node_list(list_of_procs);
}

/* Print all defined functions. */
void print_funcs(void)
{
  fprintf(tlvstdout,"Functions:\n");

  print_node_list(list_of_funcs);
}


/***********************************************************************/

/* Interactive command to define new programs */
void to_command(node_ptr n, node_ptr param, node_ptr stmts)
{
  /* Find canonical name of procedure. */
  node_ptr name = find_atom(n);
  node_ptr val;

  /* If the routine already exists then erase it */
  if (val = find_assoc(progs_hash, name))
    remove_assoc(progs_hash, name, val);
  else
    list_of_procs = cons(name, list_of_procs);

  /* Insert the routine into the program hash */
  insert_assoc(progs_hash, name, find_node(LIST, param, stmts));

  if (!silent)
    fprintf(tlvstderr, "The program %s has been recorded\n",
            name->left.strtype->text);
}


/* Interactive command to define new functions */
void func_command(node_ptr n, node_ptr param, node_ptr stmts, int typ)
{
  /* Find cannonical name of function. */
  node_ptr name = find_atom(n);
  node_ptr val;

  /* If the routine already exists then erase it */
  if(val=find_assoc(funcs_hash[typ],name))
    remove_assoc(funcs_hash[typ],name,val);
  else
    list_of_funcs = cons(name,list_of_funcs);

  /* Insert the routine into the program hash */
  insert_assoc(funcs_hash[typ],name,find_node(LIST,param,stmts));

  if (!silent)
    fprintf(tlvstderr,"The function %s has been recorded\n",
                   name->left.strtype->text);
 }

/* s is a string. Substitue the two letter string "\n" with
   a space followed by a real \n . This allows the user
   to use "\n" within the Print command, in order to terminate
   line. */
char *subs_newline(char *s)
{
  char *pos;

  for (pos = s; pos = strstr(pos, "\\"); pos++)
    {
      int find = 1;

      switch (pos[1]) {
        case 'n': pos[0]='\n'; break; //newline
        case 't': pos[0]='\t'; break; //tab
        case 'r': pos[0]='\r'; break; //carriage return
        case 'f': pos[0]='\f'; break; //form feed 
        case 'v': pos[0]='\v'; break; //vertical tab
        case 'b': pos[0]='\b'; break; //backspace
        case 'a': pos[0]='\a'; break; //bell
        default: find=0; break;

        //case '"': pos[0]='"'; break; //double quote
        //this one is making some problems since you are 
        //probably locking for this char first
      }

      if (find) {
        // forcing the cursor back to place, that is one character before
        strcpy(pos+1, pos+2);
      }
    }
  return s;
}

/* Implementation of Print command.
   The items are printed in reverse. */
void print_command(node_ptr n)
{
  if (n) {
    node_ptr curr_expr = car(n);

    /* Recursively print next item on the list. */
    print_command(cdr(n));

    if (curr_expr->type == QUOTE)
      /* The current expression is a string, so print it. */
      fprintf(tlvstdout, subs_newline(curr_expr->left.strtype->text));

    else if (curr_expr->type == DEFINE) {
      /* The parameter is preceeded by ' . This means
         that the parameter should not be evaluated as a bdd, but
         as a symbol/parse-tree */

      /* Evaluate parameter as a symbol. */
      node_ptr val = eval_symbol(car(curr_expr));

      /* Print result. */
      strcpy(buf, "");
      sprint_node(buf, BUFSIZE, val);
      fprintf(tlvstdout, buf);
    }
    else
      /* Use tlv.c specific routine to interpret parameter and 
         print it. */
      if (script_eval_node_and_print)
        (*script_eval_node_and_print)(curr_expr);
      else
        fprintf(tlvstdout,"**cant print data**");
  }
}


/* Implement assign and dump comamnds by calling tlv.c code. */
void assign_command(node_ptr lhs,node_ptr rhs)
{
  (*script_assign_command)(lhs,rhs);
}
void dump_command(node_ptr n, node_ptr fname, node_ptr b)
{
  (*script_dump_command)(n,fname,b);
}

/* Exit command. Exit from program. */
void exit_command(node_ptr num)
{
  if (num == NIL) exit(0);

  exit((*script_eval_num)(num,NIL));
}


/***********************************************************************
     Part II : Script execution - run_stmts, run_1_stmt
 ***********************************************************************/

/* Run a sequence (given as a list) of statements. */
/* The returned result already has reference counters to it. */
void *run_stmts(node_ptr stmts, int typ)
{
  node_ptr curr_node = stmts;
  node_ptr curr_stmt;

  node_ptr stmt_stack = NIL;

  void *result;

  /* This loop runs a statment list which may contain nested
     statement lists. The inner loop simply goes through
     a list of statements and executes them. However, when
     there are nested lists such as when there is an IF statement,
     then execution moves on to a new list (the list either for
     the THEN, or the ELSE), but when that list is done we
     have to go back to resume execution of the original list.
     This is done by having a stack of the locations where
     we need to resume execution. This stack is observed
     in the outer loop. */
  while (curr_node) {
    /* This loop runs a statement list. */
    while (curr_node) {
      /* Get the current statement from the list. */
      curr_stmt = curr_node->left.nodetype;

      /* Execute statement */
      switch (curr_stmt->type) {
      case PRINT: print_command(car(curr_stmt)); break;
      case SETTIME: settime_command();  break;
      case CHKTIME: chktime_command();  break;
      case WHILE:
        /* Evaluate the condition as a boolean. */
        if ((*script_eval_node_to_boolean)(curr_stmt->left.nodetype,NIL)) {

          /* Remember our current position in a stack */
          push_node(&stmt_stack,curr_node);

          /* Start excuting a new statement list */
          curr_node = curr_stmt->right.nodetype;

          /* Skip over code at end loop which advances to the next statement */
          continue;
        }
        break;

      case IF: {
        /* Evaluate the condition as a boolean. */
        int result =
          (*script_eval_node_to_boolean)(condition_of_if(curr_stmt), NIL);

        if (result || (!result && else_of_if(curr_stmt) != NIL)) {
          /* Remember the next statement to be executed after
             this IF structure */
          if (curr_node->right.nodetype)
            push_node(&stmt_stack,curr_node->right.nodetype);

          /* Start executing a new statement list */
          curr_node = result ? then_of_if(curr_stmt) : else_of_if(curr_stmt);

          /* Skip over the code which advances to the next statement */
          continue;
        }

        break;
      }
      case TLVCASE: {
        /* Case command. */
        node_ptr scan;
        node_ptr str_list;

        /* Evaluate the term in the parenthesis as a parse tree. */
        node_ptr result = eval_symbol(car(curr_stmt));

        strcpy(buf,"");
        sprint_node(buf,BUFSIZE,result);

        /* Scan the list of strings and find one that matches. */
        for (scan=cdr(curr_stmt); scan; scan=cdr(scan))
          if (scan->type == DEFAULT)
            break;
          else
            for (str_list = car(car(scan));str_list; 
                 str_list = cdr(str_list))
              if (!strcmp(buf, atom_to_string(car(str_list))))
                goto get_out;
        get_out:
        /* Execute the statement sequence (if string found). */
        if (scan) {
          /* Remember the next statement to be executed after
             this CASE structure */
          if (curr_node->right.nodetype)
            push_node(&stmt_stack,curr_node->right.nodetype);

          /* Start executing a new statement list */
          curr_node = cdr(car(scan));

          /* We do this "continue" to skip over the code
             at the end of this loop which advances to
             the next statement */
          continue;
        }

        /* If no matching string was found, then just continue
           execution after the CASE statement. */
        break;
      }

      case RUN:
        run_command(curr_stmt->left.nodetype,curr_stmt->right.nodetype);
        break;

      case BREAK: case CONTINUE:
        /* Search for last loop in stack. Pop stack until we reach it.  */
        do {
          curr_node = pop_node(&stmt_stack);
        } while (curr_node != NIL && ! is_loop_stmt(car(curr_node)) );
        /* curr_node->left.nodetype->type != WHILE ); */

        if (curr_stmt->type == BREAK)
          break;
        else
          continue; /* skip over advancing curr_node to next statement.
                       This will bring us back to the beginning of the loop. */
      case TLV_RETURN:
        /* Empty stack */
        while (curr_node = pop_node(&stmt_stack));

        /* Evaluate result. */
        if (curr_stmt->left.nodetype)
          result = (*script_eval_node)(NIL,curr_stmt->left.nodetype,NIL, typ);
        else
          result = (*script_null_value)(typ);

        return (result);

      case EXIT:
        exit_command(car(curr_stmt));
        break;

        /* The reason we keep the next three cases in here and not
           in "application_command" is that if we want to create a
           program which will be able to understand different languages
           and data structures according to the input, then grammar.y
           will have to call different functions for assignment (for
           example) if there is no "generic" script_assign_command.
           Instead we  have
           a generic "assign_command" implemented by "script_assign_command".
           the assign_command supplied by script.h provides a generic
           assign command which can be used from grammar.y */

      case LOCAL: {
        node_ptr name_key =
          (*script_eval_node_to_symbol_key)(curr_stmt->left.nodetype, NIL);

        if (!exists_local(name_key))
          /* If such a variable already exists, then store
             its value so we can restore it later. */
          delete_symbol_and_store_on_frame(name_key);
        /* else */
        /*   fprintf(tlvstdout, "LOCAL: Skipping re-declaration of local\n"); */

        if (curr_stmt->right.nodetype == NIL)
          break;
      }
        /* fall through on purpose.*/

      case LET:
        (*script_assign_command)(curr_stmt->left.nodetype,
                                 curr_stmt->right.nodetype);
        break;

      case DUMP:
        (*script_dump_command)(curr_stmt->left.nodetype,
                               curr_stmt->right.nodetype->left.nodetype,
                               curr_stmt->right.nodetype->right.nodetype);
        break;

      case COLON:
        /* Declare a new program variable. */
        (*script_declare_var)(curr_stmt);
        break;

      default:
        /* fprintf(tlvstderr, "run_stmts: Strange statement -- %d\n", */
        /*         curr_stmt->type); */
        break;
      }

      /* Go to the next statement in the list. */
      if (curr_node != NIL)
        curr_node = curr_node->right.nodetype;
    }

    /* Return from nested list. */
    curr_node = pop_node(&stmt_stack);
  }
  return (*script_null_value)(typ);
}

/* Run one statement (this is used for running While and IF from
   command line) */
void run_1_stmt(node_ptr stmt)
{
  /* Wrap statement in a list. */
  node_ptr stmts = new_node(LIST, stmt, NIL);

  void *val = run_stmts(stmts, 0);

  (*script_free_value)(val);

  /* Free node used to wrap statement in list. */
  free_node(stmts);
}

/***********************************************************************
     Part III : Running procedures and function: map_params,
                run_command, run_func
 ***********************************************************************/

/* eval_arg: Evaluates an argument corresponding to a given parameter */
node_ptr eval_arg(node_ptr param, node_ptr arg)
{
  node_ptr result;
  if (param->type == INOUT) {
    /* This handles passing parameters by name. This occurs when the
       formal paramter is preceded by &  . */

    /* I don't know which of these two lines is better. The additional
       eval_struct may provide easier calls with the same parameter name,
       since the argument passed to the next parameter would not be the parm
       name, but its value. */

    result = eval_struct(arg, NIL);
    /* result = new_node(LIST,arg,NIL); */
  }
  else if (param->type == DEFINE)
    /* Symbolic evaluation, when formal paramter is preceeded by ' */
    result = eval_symbol(arg);
  else {
    node_ptr parm_key = eval_struct(param, NIL); /* Find node for parameter */

    /* Evaluate argument. */
    result = (node_ptr) (*script_eval_node)(parm_key,arg,NIL,0);
  }
  return result;
}

/* Associate actual parameters with formal parameters. */
/* Loop over both parameter lists .                    */
/* Also pushes new frame, but only if succeded in performing the map,
   (which is indicated by a return value of 1. */
static int map_params(char *name, node_ptr arg_list, node_ptr parm_list)
{
  node_ptr curr_arg = arg_list;
  node_ptr curr_parm;

  /* Length of parameter lists. */
  int len_p = length(parm_list);
  int len_a = length(arg_list);

  int params_to_default = len_p - len_a;

  /* List of evaluated arguments. */
  node_ptr eval_arg_list = NIL;

  /* Check that the number of formal parameters is greater than the number
    of actual arguments. If there are leftover parameters then hopefully they
    have default values. Otherwise we'll report an error later on. */
  if (len_p < len_a) {
    fprintf(tlvstderr, "The number of parameters is incorrect\n");
    fprintf(tlvstderr,
            "The routine %s expects %d parameters but received %d\n", name,
            len_p, len_a);
    return 0;
  }
  else if (len_p > len_a) {
    /* There are more formal parameters than arguments.
       We need to check that there are at least len_p - len_a
       default parameters. */
    int i = params_to_default;

    for (curr_parm = parm_list;  curr_parm != NIL && i > 0; 
         curr_parm = cdr(curr_parm)) {

      node_ptr parm = car(curr_parm);
      i--;

      if (!is_default_param(parm)) {
        fprintf(tlvstderr, "The number of parameters is incorrect\n");
        fprintf(tlvstderr,
                "The routine %s expects at least %d parameters but received"
                " %d\n",
                name, len_a + 1, len_a);
        return 0;
      }
    }
  }

  /*** Evaluate arguments ***/

  /* Loop which evaluates arguments and adds them to the list
     "eval_arg_list" */
  for (curr_parm = parm_list ; curr_parm != NIL; curr_parm = cdr(curr_parm) ) {
    node_ptr parm = curr_parm->left.nodetype;
    node_ptr arg;

    if (params_to_default == 0) {
      arg = curr_arg->left.nodetype;
      /* Go to next argument */
      curr_arg = curr_arg->right.nodetype;
    }
    else {
      params_to_default--;
      if (is_default_param(parm))
        arg = default_param_value(parm);
      else
        catastrophe("Error: in map_params");
    }
    /* Unwrap a default param */
    if (is_default_param(parm))
      parm = default_param_formal(parm);

    eval_arg_list = append(eval_arg_list,
                           new_node(LIST, eval_arg(parm, arg), NIL));
  }

  /* We can push the frame only after evaluating the arguments since
     evaluating the arguments may require the previous frame. */
  push_frame();

  /*** Map evaluated arguments list. ***/

  /* Loop which maps actual parameters to formal paramters */
  curr_arg = eval_arg_list;
  for (curr_parm = parm_list; curr_parm != NIL; curr_parm = cdr(curr_parm)) {
    node_ptr parm = curr_parm->left.nodetype;
    node_ptr arg = curr_arg->left.nodetype;

    node_ptr parm_key;

    if (parm->type == EQDEF)
      parm = parm->left.nodetype;
    if (parm->type == INOUT) {
      parm_key = eval_struct(car(parm), NIL); /* Find node for parameter */
      insert_by_name_param(parm_key, arg);    /* Associate parameter by name. */
    }
    else if (parm->type == DEFINE) {
      parm_key = eval_struct(car(parm), NIL);  /* Find node for parameter */
      /* Remember previous definition. */
      delete_symbol_and_store_on_frame(parm_key);
      insert_parse_tree(parm_key, arg);       /* Create parse tree variable */
    }
    else {
      parm_key = eval_struct(parm, NIL);  /* Find node for parameter */

      /* Remember previous definition of symbol. */
      delete_symbol_and_store_on_frame(parm_key);

      /* Insert dyname var. */
      if (script_insert_dynamic_var)
        (*script_insert_dynamic_var)(parm_key, (void *) arg);
      else
        insert_dynamic_var(parm_key, (bdd_ptr) arg);
    }
    curr_arg = curr_arg->right.nodetype; /* Go to next argumenmt */
  }

  free_list(eval_arg_list);

  return 1;
}

/* Interactive command to run programs. name is the name of subprogram
   to run, and args are the arguments. */
void run_command(node_ptr name, node_ptr args)
{
  node_ptr prg;

  /* This is a list which contains the previous values of variables
     which were overrun by local variables.
     They are restrored after this routines ends it's execution.
     node_ptr global_list= NIL ;  */

  /* Find program in prog hash */
  node_ptr name_node = find_node(name->type,name->left.nodetype,
                                            name->right.nodetype);
  if (name_node == NIL ||
      (prg= find_assoc(progs_hash,name_node)) == NIL) {
    /* No user defined command found.
       Try to execute a predefined application command from tlv.c . */
    if (script_application_command &&
        (*script_application_command)(name_node, args))
      return;
    else {
      fprintf(tlvstderr, "The program %s is not defined\n",
              name->left.strtype->text);
      return;
    }
  }

  /* Map arguments to formal parameters, and execute routine.
     push frame is done inside map_params. */
  if (map_params(name->left.strtype->text,
                 args,prg->left.nodetype)) {
    void *val = run_stmts(prg->right.nodetype, 0); /* Run program */
    (*script_free_value)(val);
    pop_frame();
  }
}

/* Interactive command to run programs */
void *run_func(node_ptr name, node_ptr args, int typ)
{
  void *result;
  node_ptr name_node = find_atom(name);
  node_ptr prg;

  /* Try to find a user defined function. */
  if ((prg = find_assoc(funcs_hash[typ],name_node)) == NIL) {
    /* No user defined function found.
       Try to execute a predefined application function. */
    if (script_application_function[typ])
      if ((result = (*script_application_function[typ])(name_node,args)) !=
          NULL)
        return result;

    /* Only print error for a function returning a bdd. */
    if (typ == 0)
      fprintf(tlvstderr, "The function %s is not defined\n",
              name->left.strtype->text);
    return (*script_null_value)(typ);
  }

  /* Execute user defined function. */

  /* push frame is done inside map_params. */
  if (map_params(name->left.strtype->text,
                 args,prg->left.nodetype)) {
    /* Run the program */
    result = run_stmts(prg->right.nodetype, typ);
    pop_frame();

    return result;
  }
  else
    return (*script_null_value)(typ);
}

/***********************************************************************/

/// Taken from gnu libc's info documentation
char *gnu_getcwd()
{
  size_t size = 100;
  while (1) {
    char *buffer = (char *) malloc(sizeof(char) * size);
    if (getcwd(buffer, size) == buffer)
      return buffer;
    free(buffer);
    if (errno != ERANGE)
      return NULL;
    size *= 2;
  }
}

/// Return the filename portion of a path. The result is a substring, not a copy
static const char *filename_only(const char *path)
{
  char *res = strrchr(path, PATH_SEP);
  return res ? res : path;
}

/**
   Sets the current load path to the absolute path portion of path (which is
   assumed to end in a filename
   If fname is a relative path, current load path is left unchanged

   This overrides the current load path, which is assumed to have been saved
   somewhere.
*/
static void set_current_load_path(const char *fname)
{
  const char *filename = filename_only(fname);
  if (filename > fname) {
    int path_len = strlen(fname) - strlen(filename);
    current_load_path = (char *) malloc(sizeof(char) * (path_len + 1));
    strncpy(current_load_path, fname, path_len);
    current_load_path[path_len] = '\0';
  }
}

static int is_relative_path(const char *path)
{
  return path[0] != PATH_SEP;
}

/// Allocates a new string containing the absolute version of path
static char *make_absolute_path(const char *path, const char *relative_to)
{
  char *res;
  int base_len = strlen(relative_to);
  int sep_missing = (relative_to[base_len - 1] == PATH_SEP) ? 0 : 1;

  res = malloc(sizeof(char) *
               (base_len + sep_missing + strlen(path) + 1));
  strcpy(res, relative_to);
  if (sep_missing)
    res[base_len] = PATH_SEP;
  strcpy(res + base_len + (sep_missing ? 1 : 0), path);
  return res;
}

/* Open a file which contains tlv commands.  If the file is not found
   it is looked for in the TLV directory.
   No parsing is done. The file descriptor is returned. */
FILE *open_file(char *fname, int relative)
{
  static char TLV_PATH_fname[300];
  int free_fname = 0;

  if (is_relative_path(fname) && relative) {
    fname = make_absolute_path(fname, current_load_path);
    free_fname = 1;
  }

  set_current_load_path(fname);

  FILE *in = fopen(fname, "r");

  /* If the file has not been found then try the
     "system" directory */
  if (in == NULL && tlv_path_exists()) {
    add_to_env(TLV_PATH_fname,fname);

    in = fopen(TLV_PATH_fname,"r");
  }
  if (free_fname)
    free(fname);
  return in;
}

/* Parses an input file and stores the result in parse_tree */
int parse_input()
{
  extern node_ptr parse_tree;

  err_node = parse_tree = NIL;
  int status = yyparse();
  if (status)
    printf("Some error while parsing\n");
  return status;
}

/* Read lines of input, using the parser, and execute them. */
void read_and_do(int prompt)
{
  extern node_ptr iparse_tree;

  extern set_prompt();
  extern char do_prompt; /* From grammar.y */

  /* Loop that reads a line and executes it. */
  while (1) {
    err_node = iparse_tree = NIL;

    if (prompt) {
      set_prompt();
      do_prompt = 1;
    }
    else
      do_prompt = 0;

    yyparse(); /* Parse interactive input */

    if (iparse_tree == NIL)
      break; /* End of file */
    else if (iparse_tree != FAILURE_NODE)
      catch_err(run_1_stmt(iparse_tree)); /* Run statement. */
  }
}

typedef struct {
  char *load_path;
  char *input_file;
  int input_fileno;
  FILE *yyin;
  int yylineno;
  node_ptr err_node;
} load_state;

void save_load_state(load_state *state)
{
  extern char *input_file;
  extern int input_fileno;
  extern FILE *yyin;
  extern int yylineno;

  state->input_file = input_file;
  state->input_fileno = input_fileno;
  state->yyin = yyin;
  state->yylineno = yylineno;
  state->err_node = err_node;
  state->load_path = current_load_path;
}

void restore_load_state(load_state *state)
{
  extern char *input_file;
  extern int input_fileno;
  extern FILE *yyin;
  extern int yylineno;

  input_file = state->input_file;
  input_fileno = state->input_fileno;
  yyin = state->yyin;
  yylineno = state->yylineno;
  err_node = state->err_node;

  if (current_load_path != state->load_path) {
    free(current_load_path);
    current_load_path = state->load_path;
  }
}

static int prepare_load(char *fname, int relative)
{
  extern char *input_file;
  extern int input_fileno;
  extern FILE *yyin;
  extern int yylineno;

  FILE *temp;
  if ((temp = open_file(fname, relative)) != NULL) {
    input_file = fname;
    input_fileno = fname2num(fname);
    yyin = temp;
    yylineno = 0;
    err_node = NIL;

    /* Set silent to 1, so that interactive messages will
       not be printed when programs are loaded from files. */
    silent = 1;

    /* Read file. */
    init_input();
    return 1;
  }
  return 0;
}

void finalize_load(load_state *old_load_state)
{
  extern FILE *yyin;

  fclose(yyin);
  restore_load_state(old_load_state);
    /* input_file = old_input_file; */
    /* input_fileno = old_fileno; */
    /* yyin = old_yyin; */
    /* yylineno = old_yylineno; */
    /* err_node = temperr; */
}

/* This procedure loads a file which contains tlv commands
   (this is used for loading the rules file) */
int load_script_file(char *fname, int relative)
{
  /* extern char *input_file; */
  /* extern int input_fileno; */
  /* extern FILE *yyin; */
  /* extern int yylineno; */

  /* FILE *temp; */

  /* char *old_input_file = input_file; */
  /* int old_fileno = input_fileno; */
  /* FILE *old_yyin = yyin; */
  /* int old_yylineno = yylineno; */
  /* node_ptr temperr = err_node; */

  load_state old_load_state;
  save_load_state(&old_load_state);

  if (prepare_load(fname, relative)) {
    read_and_do(0);
    finalize_load(&old_load_state);
    return  1;
  }
  return 0;
}

int parse_file(char *fname, node_ptr *result)
{
  extern node_ptr parse_tree;

  printf("parse_file: Parsing file %s..\n", fname);

  load_state old_load_state;
  save_load_state(&old_load_state);

  if (prepare_load(fname, 0)) {
    parse_input();
    if (parse_tree == NULL)
      printf("parse_file: null!\n");
    *result = parse_tree;
    finalize_load(&old_load_state);
    return  1;
  }
  return 0;
}

/* Load a special rules files. */
void load_rule_file(void)
{
  /* Default name of rule file. */
  static char* rule_filename ="Rules.tlv";

  /* Get name of rule file. */
  char* rule_file_env = getenv("TLV_RULES");

  /* If the environment variable is not defined then default
     to Rules.tlv . */
  if (!rule_file_env)
    rule_file_env = rule_filename;

  /* Load the file. */
  if (load_script_file(rule_file_env, 0))
    fprintf(tlvstdout, "Loaded rules file %s.\n", rule_file_env);
  else
    fprintf(tlvstderr,"\nThe rule file %s has not been found...\n\n",
            rule_file_env);
}


/* Enter the interactive mode of tlv */
void go_interactive(void)
{
  extern char *input_file;
  extern int input_fileno;
  extern FILE *yyin;
  extern int yylineno;

  fprintf(tlvstdout,"\n      Your wish is my command ... \n\n");

  /*  set_prompt(); */

  input_file = NULL;
  input_fileno = 0;
  yylineno=0;
  yyin = stdin;

  init_input();

  read_and_do(1);
}


/* Initialize script, by initializing hash tables. */
void init_script(void)
{
  progs_hash = new_assoc();
  funcs_hash[0] = new_assoc();
  funcs_hash[1] = new_assoc();
}
