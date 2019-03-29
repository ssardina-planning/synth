/* This file contains various utilities: open files, time statistics,
   ctrl-c handling, and printing errors.  */

#ifndef UTILDEF
#define UTILDEF

#include <node.h>
#include <stdio.h>

/* Implement error catching using setjmp */
#include <setjmp.h>


/* Use this instead of stdout & stderr. Using this everywhere in tlv
   allows us to divert error or output to different files. Actually,
   this is how the log an append commands are implemented. */
FILE *tlvstderr, *tlvstdout;

/* Assign the node currently being evaluated to this variable,
   if you want an error message to be printed when there is 
   an error. */
extern node_ptr err_node;

/**********************************************************************
 Handle ctrl C
**********************************************************************/

#define catch_err(c) {longjmp_on_err = 1; if(!setjmp(longjmp_buf))c; longjmp_on_err = 0;}
extern int longjmp_on_err;
extern jmp_buf longjmp_buf;

/* Start handling ctrl-c  */
void set_ctrl_c_handle(void);


/**********************************************************************
 Parsing and file utilities.
**********************************************************************/


extern int yyparse(void);
/*extern int yylex(void);*/

/* Open and close files which are to be read using yylex.  */
int open_input(char *filename);
void close_input(void);

/* Add the tlv directory name to the begining of the file name "filename".
   The result is returned in the variable result, however, no memory
   is allocated. The user is relied upon. */
void add_to_env(char *result, const char *filename); 

/* Check if file exists along path and returns full name of the
   file, or NULL if the file doesn't exist along the path. */
char *find_file_in_path(char *fname);

/* Returns TRUE if the environment variable TLV_PATH is defined. */
int tlv_path_exists();

/**********************************************************************
  Timing utilities
**********************************************************************/

/* Measures the time of computation */
void settime_command();
void chktime_command(); /* Print time which has passed since last settime. */

/* Print time usage.  */
void print_usage(FILE *stream);


/* Associate file names with numbers which can be stored
   succinctly in a node_ptr. */
int fname2num (char *fname);
char *num2fname(int num);


/**********************************************************************/

/* Stack which stores current context during semantic
   analisys. Used to print error message. */
void push_atom(node_ptr s);
node_ptr pop_atom(void);
int empty_atom_stack(void);


/* Print error messages */

void rpterr(char *fmt,...);

/* Print critical error and exit program  */
void catastrophe2(char *s,int i);
void catastrophe(char *s);


/* Print file name and line number of error. */
void start_err(void);

/* Print context and perform cleanup after error in interactive mode. */
void finish_err(void);

/* Print specific error messages. */
void undefined(node_ptr s);
void redefining(node_ptr s);
void circular(node_ptr s);
void toomanyvars(void);
void type_error(node_ptr n);
void multiple_assignment(node_ptr t1);
void range_error(node_ptr n, node_ptr the_var);
void notanumber(node_ptr n);
void variable_owned_by_two(node_ptr n);

/* Initialize *all* utility packages. (Except storage) */
void init_util(void);

#endif
