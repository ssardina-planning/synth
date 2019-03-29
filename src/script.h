/* This file deals with tlv-Basic scripts.  
   A script is a sequence of statements ih tlv-Basic.
 
   Note that some of the commands and functions of tlv-Basic are
   defined in tlv.c . script.c contains the implementation of
   a general scripting language.  tlv.c contains specific code
   which implements tlv specific commands. This file can be used
   to implement new programs which require a scripting language
   but use different data structures than tlv. 

   In short, this file is an attempt to separate the generic part
   of the scripting language, from parts specific to tlv, which
   reside in tlv.c */


/* If silent == 1 then no messages are printed when new functions
   or procedures are recorded. This is useful when loading files.
   If it is 1 then messages are printed. This is used interactively 
   so the user gets feedback once defintion of a subprogram has
   completed. */
extern int silent;

/* Initialize usage of this file . */
void init_script(void);

/* Print all defined procedures/functions. */
void print_procs(void);
void print_funcs(void);

/* Commands to define new procedures or functions. 
   stmts is the body of the subprogram. 
   typ is the type of the object which the function returns (0-bdd, 1-formula) */
void to_command(node_ptr name, node_ptr param, node_ptr stmts);
void func_command(node_ptr name, node_ptr param, node_ptr stmts, int typ);

/* Execute a list of statements in tlv-Basic. */
void* run_stmts(node_ptr stmts, int typ);

/* Execute a single statement in tlv-Basic. */
void run_1_stmt(node_ptr stmt);

/* All following routines ending with _command are called from
   grammar.y . They are implementations of specific commands
   in tlv-Basic. */

/* Execute a user defined subprogram. In run_func, the
   returned pointer points to the result of the function. 
   The third parameter, typ, specifies different return types
   of the function. */
void run_command(node_ptr name, node_ptr args);
void *run_func(node_ptr name, node_ptr args, int typ);

/* Print */
void print_command(node_ptr n);

/* Let lhs := rhs */
void assign_command(node_ptr lhs,node_ptr rhs);

/* Dump */
void dump_command(node_ptr n, node_ptr fname, node_ptr b);

/* Exit n ;  n - is number with which to set exit status. */
void exit_command(node_ptr num);

/* Loading scripts from files. */
FILE *open_file(char *fname, int relative) ;
int load_script_file(char *fname, int relative);
void load_rule_file(void);

/* Read and parse a file */
int parse_file(char *fname, node_ptr *result);

/* Enter interactive mode. */
void go_interactive(void);


/**********************************************************************/

/* The following are all pointers to functions. The functions are not
   defined in this file. They are defined in tlv.c . These functions
   implement tlv-specific parts of the scripting language. tlv.c connects
   its own implementation by assigning to one of the function pointer
   below. */

/* Evaluate node "n" with context "context" to data structure.
   "parm" is the node_ptr of a formal parameter. If parm == NIL then
   the default data type is returned. Otherwise the data type returned can
   be determined by the parameter specification and by typ. */
extern void *(*script_eval_node)(node_ptr parm, node_ptr n,node_ptr context,
                                 int typ);

/* Additional types of evaluation . */
extern int (*script_eval_node_to_boolean)(node_ptr n, node_ptr context);
extern int (*script_eval_num)(node_ptr num,node_ptr context);
extern node_ptr (*script_eval_node_to_symbol_key)
           (node_ptr n, node_ptr context);

/* determine value which denotes null value. */
extern void *(*script_null_value)(int typ);

extern void (*script_free_value)(void *val);

/* Insert a dynamic variable. */
extern void (*script_insert_dynamic_var)(node_ptr parm_key,void *val);

/* Evaluate a node and print it to the screen. */
extern void (*script_eval_node_and_print)(node_ptr n);

/* Assign and Dump commands. */
extern void (*script_assign_command)(node_ptr lhs,
                               node_ptr rhs);
extern void (*script_dump_command)(node_ptr n,
                                   node_ptr fname,
                                   node_ptr b);

/* Declare a new program variable. */
extern void (*script_declare_var)(node_ptr n);

/* Try to execute a tlv-specific command. Returns 1 if successful. */
extern int (*script_application_command)(node_ptr stmt,node_ptr args);

/* Try to execute a tlv-specific function. */
/* The values returned from the function should already have
   their reference counteres increased.
   The function may return NULL if there were problems in the arguments,
   such as wrong number of arguments. */
extern void *(*script_application_function[5])(node_ptr name,node_ptr args);
