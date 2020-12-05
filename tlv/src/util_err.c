/*
  Changelog:

  Ittai 5/30/04: Use clock() instead of times, because sys/times.h is
  nonstandard. Makes compiling on win32 (mingw32) easier.

 */

#include <stdarg.h>
#include <setjmp.h>
#include <signal.h>  /* For overiding <CTRL-C> */
#include <stdlib.h>
#include <stdio.h>

#include <node.h>
#include <bdd.h>
#include <eval.h>
#include <util_err.h>

#include <storage.h>
#include <hash.h>
#include <assoc.h>

#include <sys/types.h>
/* #include <sys/times.h> */
#include <time.h>
/* #ifndef CLK_TCK */
/* # define CLK_TCK 60 */
/* #endif */

int loading_smv_file = 1;

/* Stack to which evaluation routines push and pop contexts or 
   terms. This is used for printing errors, so that we know in what
   context the error occured. */
static node_ptr atom_stack=0;

jmp_buf longjmp_buf;
int longjmp_on_err = 0;

/* Name of environment variable which holds path for tlv files. */
static char* tlv_path = "TLV_PATH";

/* The name of the directory where the tlv files are */
char* tlv_dir = 0;


/* Name of input file in file routines.*/
char *input_file ;

int input_fileno;


static hash_ptr fname_hash;


/* This variable stores a node which is being currently executed. 
   If there is an error in the program, then it is in executing this
   node, so the error messages should also concern this node. */
node_ptr err_node = NIL;


/**********************************************************************
 File routines.
 **********************************************************************/

/* Open input file, which is to be read using yylex.  */
int open_input(char *filename)
{
  extern int yylineno;
  extern FILE *yyin;

  input_file = filename;

  /* Open input file and assign file descriptor to yyin */
  if(!(yyin = fopen(filename,"r")))
    rpterr("cannot open %s for input",filename);
  yylineno = 1;

  return 1;
}

/* Close input file.                                                    */
void close_input(void)
{
  extern int yylineno;
  extern FILE *yyin;

  fclose(yyin);
  input_file = 0;
  yylineno = 0;
}

/* Returns true if TLV_PATH was found and was evaluated.  */
int tlv_path_exists()
{
  return tlv_dir != 0;
}

/* Add the tlv directory name to the begining of the file name */
void add_to_env(char *result, const char *filename)
{
  if (tlv_dir)
   {
     strcpy(result,tlv_dir);  /* Copy directory name. */
     strcat(result,filename); /* Copy file name. */
   }
  else
    strcpy(result,filename);  /* Copy file name in current directory */ 
}

/* Check if the file exists in the current director, and if
   not, if it exists in the TLV_PATH.
   The full name under which the file was found, is returned.  */
char *find_file_in_path(char *fname)
{
  static char TLV_PATH_fname[300];
  FILE *tempf;

  if (fname == 0)
    return NULL;

  tempf = fopen(fname,"r");

  if (tempf != NULL)
    {
      fclose(tempf);
      return fname;
    }
  /* If the file has not been found then try the "system" directory */
  else if ( tempf == NULL && tlv_path_exists())
    {
       add_to_env(TLV_PATH_fname,fname);

       tempf = fopen(TLV_PATH_fname,"r");
       if ( tempf != NULL )
         {
           fclose(tempf);
           return TLV_PATH_fname;
         }
    }

  return NULL;
}


/**********************************************************************
 Timing routines.
 **********************************************************************/

clock_t lasttime;  /* Used for timing commands settime,chktime */
// struct tms lasttime;  /* Used for timing commands settime,chktime */

void settime_command()
{
  lasttime = clock();
  /* times(&lasttime); */
}

double get_time_used()
{
  clock_t end_time = clock();
  if (lasttime > end_time)
    fprintf(tlvstderr,
            "lasttime > end_time! Did you forget to call Settime?\n");
  double result = ((double) (end_time - lasttime)) / CLOCKS_PER_SEC;
  if (result < 0)
    fprintf(tlvstderr, "get_time_used: Result is negative!\n");
  return result;
}

/* Print time which has passed since last settime. */
void chktime_command()
{
  fprintf(tlvstdout, "user time: %g s\n", get_time_used(clock()));
/*
  struct tms buffer;
  fprintf(tlvstdout,"resources used:\n");
  times(&buffer);
  fprintf(tlvstdout,"user time: %g s, system time: %g s\n",
	 (buffer.tms_utime-lasttime.tms_utime)/(double)CLK_TCK,
	 (buffer.tms_stime-lasttime.tms_stime)/(double)CLK_TCK);
*/
}

/* Print time usage since settime_command was called */
void print_usage(FILE *stream)
{
  fprintf(stream, "\nResources used:\n");
  fprintf(stream, "user time: %g s\n", get_time_used(clock()));
/*
  struct tms buffer;
  fprintf(stream,"\nresources used:\n");
  times(&buffer);
  fprintf(stream,"user time: %g s, system time: %g s\n",
          buffer.tms_utime/(double)CLK_TCK,
          buffer.tms_stime/(double)CLK_TCK);
*/
}


/**********************************************************************
  Control C and jump.
 **********************************************************************/

void handle_ctrlc(int i)
{
/*  printf("<CTRL-C>\n"); */
  set_ctrl_c_handle();  /* Reset handler.  */
  if(longjmp_on_err)longjmp(longjmp_buf,1); /* Jump. */
}

/* Uses handle_ctrlc to handle contol-c  */
void set_ctrl_c_handle(void)
{
  /* Override Control-C */
#ifdef __cplusplus
  signal(SIGINT , (void (*)(...))(handle_ctrlc));
#else
  signal(SIGINT , (void (*)())(handle_ctrlc));
#endif
}


/* The folloing two routines are not used anywhere */
int my_setjmp()
{
  int v;
  longjmp_on_err = 1;
  v = setjmp(longjmp_buf);
  if(v)
    longjmp_on_err = 0;
  return(v);
}

void cancel_my_setjmp()
{
    longjmp_on_err = 0;
}  


/**********************************************************************/

/* Manage atom stack. */

void push_atom(node_ptr s)
{
  atom_stack = cons(s,atom_stack);
}

node_ptr pop_atom(void)
{
  node_ptr temp, result;

  if(!atom_stack)catastrophe("pop_atom: stack empty");

  temp = cdr(atom_stack);
  result = car(atom_stack);

  free_node(atom_stack);
  atom_stack = temp;

  return result;
}

int empty_atom_stack(void)
{
  return atom_stack == 0;
}

/*********************
   Generic Error messages
*********************/

/*VARARGS1  print error message, using format which
   can understand %d, %s. 

  Future work, maybe add %n for printing a node. */
void rpterr(char *fmt,...)
{
  va_list ap;
  char *sval;
  char *p;
  int ival;

  start_err();

  va_start(ap,fmt);

  for (p=fmt; *p; p++) {
    if (*p!= '%') {
      fputc(*p, tlvstderr);
      continue;
    }
    switch (*++p) {
    case 'd':
      ival = va_arg(ap, int);
      fprintf(tlvstderr, "%d", ival);
      break;
    case 's':
      for (sval = va_arg(ap, char *); *sval; sval++)
        fputc(*sval,tlvstderr);
      break;
    case 'n': {
      char buf[200];
      node_ptr nval = va_arg(ap, node_ptr);
      print_node(tlvstderr, nval);
      break;
    }
    default:
      fputc(*p, tlvstderr);
      break;
    }
  }
  va_end(ap);
  finish_err();
}

/* Print critical error and exit program  */
void crash(void)
{
  fprintf(tlvstderr,"Internal error...");
  fprintf(tlvstderr,"\nPlease report this error to elad@wisdom.weizmann.ac.il\n");
  fprintf(tlvstderr,"Send a copy of this output and your input.\n"); 
  exit(1);
}

/* This routine reports an internal error.                  */
/* Error messages are printed and the program stops .       */
void catastrophe(char *s)
{
  fprintf(tlvstderr,s);
  crash();
}

void catastrophe2(char *s,int i)
{
  fprintf(tlvstderr,s,i);
  crash();
}

/* Translate file name to a number. Numbers take less space to
   store inside nodes. We need to store file names in nodes because
   if an error occurs in a script we need to know from which
   file this script came from in order to print a proper error message. */
int next_fnum = 1;
int fname2num (char *fname)
{
  node_ptr fname_key = string_to_atom(fname);
  node_ptr val;

  /* If no translation exists, then insert it into the hash
     table. */
  if (!(val = find_assoc(fname_hash, fname_key))) {
    val = find_NUMBER_node(next_fnum++);
    insert_assoc(fname_hash, fname_key, val);
    insert_assoc(fname_hash, val, fname_key);
  }
  return number_of(val);
}

char *num2fname(int num)
{
  node_ptr num_key = find_NUMBER_node(num);
  node_ptr fname_node = find_assoc(fname_hash, num_key);

  if (fname_node) {
    return atom_to_string(fname_node);
  }
  else
    return "";
}


/* Print the start of an error message which contains the file name  */
/* and line number in which the error occured                        */
void start_err(void)
{
  extern int yylineno;

  char *fname = (err_node == NIL) ? input_file:
                                    num2fname(err_node->fileno);
  int  lineno = (err_node == NIL) ? yylineno :
                                    err_node->lineno;

  fprintf(tlvstderr,"\n");
  if(fname && fname[0] != 0) {
      fprintf(tlvstderr,"file %s: ", fname);
      if (lineno)
          fprintf(tlvstderr,"line %d: ",lineno);
  }
}


/* If reading smv file, print context using atom stack.  */
void finish_err(void)
{
  if (loading_smv_file)
    while(atom_stack) {
      node_ptr s = car(atom_stack);
      atom_stack = cdr(atom_stack);
      fprintf(tlvstderr, "in definition of ");
      print_node(tlvstderr, s);
      if (s->lineno)
        fprintf(tlvstderr, " at line %d", s->lineno);
      fprintf(tlvstderr, "\n");
    }
  else {
    /* If we are in the middle of a routine then we have to 
       remove all frames. If we are not in the middle of a 
       routine then
       no harm is done by trying to remove all frames. */
    pop_all_frames();
    clear_eval_stack();
  }

  /* The variable "longjmp_on_err" is 1 only when called from
     grammer.y in the routine "catch_error". These calls occur only
     in interactive mode. What they do is allow interactive errors
     without exiting from the program.
     The routine "longjmp" jumps out of this routine and never returns */
  if (longjmp_on_err) longjmp(longjmp_buf, 1);

  if (loading_smv_file)
    exit(1);
}

/**********************************************************************

  Specific error messages.

**********************************************************************/

/* Print error message about an undefined symbol */
void undefined(node_ptr s)
{
  start_err();
  print_node(tlvstderr, s);
  fprintf(tlvstderr, " undefined ");
  finish_err();
}

/* Print error message about a redefined symbol */
void redefining(node_ptr s)
{
  start_err();
  fprintf(tlvstderr,"redefining ");
  print_node(tlvstderr,s);
  finish_err();
}

void circular(node_ptr s)
{
  start_err();
  fprintf(tlvstderr,"recursively defined: ");
  print_node(tlvstderr,s);
  finish_err();
}

void toomanyvars(void)
{
  start_err();
  fprintf(tlvstderr,"too many variables");
  finish_err();
}

void type_error(node_ptr n)
{
  start_err();
  indent_node(tlvstderr,"type error: value = ",n,"");
  finish_err();
}  

void multiple_assignment(node_ptr t1)
{
  start_err();
  fprintf(tlvstderr,"multiply assigned: ");
  print_node(tlvstderr,t1);
  finish_err();
}

void range_error(node_ptr n, node_ptr the_var)
{
  start_err();
  indent_node(tlvstderr,"cannot assign value ",n," to variable ");
  print_node(tlvstderr,the_var);
  finish_err();
}

/* Print error message : Not a number */
void notanumber(node_ptr n)
{
  start_err();
  fprintf(tlvstderr,"not a number: ");
  print_node(tlvstderr,n);
  finish_err();
}

/* Print error message : Not a number */
void variable_owned_by_two(node_ptr n)
{
  start_err();
  fprintf(tlvstderr,"Variable ");
  print_node(tlvstderr,n);
  fprintf(tlvstderr," owned by two synchronous modules");

  finish_err();
}


/**********************************************************************/

/* Initialize *all* utility packages. (except storage) */
void init_util(void)
{
  extern int verbose;

  /* Initialize file descriptors. */
  tlvstdout = stdout;
  tlvstderr = stderr;


  init_string();
  init_assoc();

  /* It is important that init_bdd is after init_node */
  init_node();     /* node.h   */
  init_bdd();      /* bdd.h    */

  init_symbols();
  init_script();

  fname_hash = new_assoc();

  /* Get tlv system directory from envronment variable. */ 
 
  tlv_dir = getenv(tlv_path);

  /* If the directory name does not end in "/" then add it. */
  if (tlv_dir && tlv_dir[strlen(tlv_dir) - 1 ] != '/') {

    char *temp = tlv_dir;

    tlv_dir = (char *) malloc(strlen(tlv_dir) + 2);
    strcpy(tlv_dir,temp);
    strcat(tlv_dir,"/");
  }

  if (verbose)
    if (tlv_dir)
      fprintf(tlvstderr,"TLV_PATH=%s\n",tlv_dir);
    else
      fprintf(tlvstderr,"TLV_PATH is not set\n");

  init_input();

  init_eval();
}
