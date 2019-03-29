#include <stdio.h>
#include <storage.h>
#include <node.h>
#include <hash.h>
#include <bdd.h>
#include <assoc.h>
#include <util_err.h>
#include <mystring.h>
#include <script.h>
#include <smv.h>
#include <tlv.h>
#include <symbols.h>
#include <y.tab.h>
#include <version.h>

/* Variables for reodering. */
extern int reorder;
extern int reorder_bits;
extern int reorder_size;

/* True if the source file has suffix .spl . */
int source_is_spl = 0;

/* Command line agrument value: Amount of disjunction in transition system.
    1: total : all the transition relation is in a single item.
    2: each upper level asynchrounous process is in a different transition.
    3: Each possible combination of synchronous processes generates an
       additional transition. */
extern int disj_amount;

/* Is true if tlv is run by a gui.  */
extern int has_gui;

/* Values used by bdd.c and can be changed by command line parameters */
extern int KEYTABLESIZE;
extern int APPLY_CACHE_SIZE;
extern int MINI_CACHE_SIZE;

/* Values used by symbols.c and can be chanaged by command line parameters */
int verbose = 0, option_interactive = 1;

/* Name of input file  */
extern char *input_file;
extern int input_fileno;

/* Garbage collection treshold. When the amount of garbage passes
   the threshold then garbage collection is performed. */
extern int gc_threshold;

/* Flag which controls how preservation bdd's are represented.  
   extern int pres_representation; */

/* File names for output and input order files. */
char *input_order_file = 0;

/* Name of the program being run ( Is updated from argv ) */
static char *myname;

/* Name of filename to load automatically */
char *load_me = 0;

/* Tree which contains the whole SMV program */
extern node_ptr parse_tree;

/* When this variable is 0, then the program
   does not halt when a syntax error occurs.
   While reading the initial SMV program, it is on,
   so that any syntax error will stop the whole program. */
extern int loading_smv_file;

int no_input_file = 0;

/*----------------------------------------------------------------------*/

void parse_smv_input_file(char *);
void finished_parsing_smv();

main(int argc, char **argv)
{
  /* Initialize storage */
  init_storage();

  /********************************/
  /* Read command line parameters */
  /********************************/

  argc--;

  myname = *(argv++); /* Extract name of program (which is first argument) */

  /* At least one argument is required */
  if(argc<1) 
    /*    rpterr("command line error (at least one argument required)");*/
    no_input_file = 1;

  /*                                                            */
  /* Loop which reads command line arguments from last to first */
  /*                                                            */
  while(argc){

    /* If argument doesn't start with "-" then load it after
       loading the program */
    if(argc == 1 && (**argv) != '-'){
      input_file = *(argv++);
      argc--;
      continue;
      }

    if((**argv) != '-'){
      load_me = *(argv++);
      argc--;
      continue;
    }

    if(strcmp(*argv,"-v")==0){ 
      argv++;
      sscanf(*(argv++),"%d",&verbose);
      set_bdd_verbose(verbose);
      /*      setlinebuf(stdout);
      setlinebuf(stderr);*/
    }
    else if(strcmp(*argv,"-i")==0){
      argv++;
      input_order_file = *(argv++);
    }
    else if(strcmp(*argv,"-o")==0){
      argv++;
      set_output_order_file(*(argv++));
    }
    else if(strcmp(*argv,"-k")==0){
      argv++;
      sscanf(*(argv++),"%d",&KEYTABLESIZE);
    }
    else if(strcmp(*argv,"-c")==0){
      argv++;
      sscanf(*(argv++),"%d",&APPLY_CACHE_SIZE);
    }
    else if(strcmp(*argv,"-m")==0){
      argv++;
      sscanf(*(argv++),"%d",&MINI_CACHE_SIZE);
    }
    else if(strcmp(*argv,"-gc")==0){
      argv++;
      sscanf(*(argv++),"%d",&gc_threshold);
    }
    /*    else if(strcmp(*argv,"-pr")==0){
      argv++;
      argc--;
      pres_representation = 1;
      continue;
      } */
    else if(strcmp(*argv, "-gui")==0){
      argv++;
      argc--; // Ittai: This line is possibly a bug (might need to be removed)
      has_gui = 1;
      continue;
    }
    else if(strcmp(*argv, "-disj")==0){
      argv++;
      argc--;
      sscanf(*(argv++), "%d", &disj_amount);
      argc--;
      if (disj_amount < 0 || disj_amount > 2)
        rpterr("-disj paramter must be between 0 and 2");
      continue;
    }
#ifdef REORDER
    else if(strcmp(*argv, "-reorder") == 0) {
      argv++;
      argc--;
      reorder = 1;
      continue;
    }
    else if(strcmp(*argv, "-reorderbits") == 0) {
      argv++;
      sscanf(*(argv++),"%d",&reorder_bits);
      reorder_bits *= 2;
    }
    else if(strcmp(*argv, "-reordersize") == 0) {
      argv++;
      sscanf(*(argv++),"%d",&reorder_size);
    }
#endif
    else
      rpterr("undefined: %s",*argv);
    argc -= 2;
  }

  /* Initialize various sections of the program */
  init_util();

  /* Initialize tlv specific things. */
  init_tlv();

#if SYS == cyg
#else
        setlinebuf(stdout);
#endif

  /* Print data about table sizes */
  if (verbose) {
    fprintf(stderr, "Key table size: %d\n", KEYTABLESIZE);
    fprintf(stderr, "Apply cache size: %d\n", APPLY_CACHE_SIZE);
  }
  if (MINI_CACHE_SIZE > APPLY_CACHE_SIZE)
    rpterr("mini-cache-size (%d) is larger than the cache-size (%d)",
	   MINI_CACHE_SIZE, APPLY_CACHE_SIZE);

  /* If there is no input file, then start with an empty fts.
     This currently doesn't work well, first of all, because the
     rule files do not know how to handle this case,  and secondly
     I think there are additional problems, although I am not sure
     what these are.  */
  if (no_input_file)
    empty_fts();
  else
    parse_smv_input_file(input_file);

  /* From now on dont fly when errors occur */
  /* Indicate that an smv file is not being loaded now.
     Different error messages should be produced as a result. */
  finished_parsing_smv();

  /* Load rules file */
  /* From here on there is a point to use tlvstderr, tlvstdout,
     since before this they must still be set to stderr, stdout */
  load_rule_file();

  /* Read another file ( usually proof file )*/
  if (load_me)
    if (load_script_file(load_me, 0))
      fprintf(tlvstderr,"\nLoaded file %s .\n", load_me);
    else
      fprintf(tlvstderr,"\nThe file %s has not been found...\n\n", load_me);

  /*
    If the symbol YYDEBUG is true then output debugging information
    on the parser's condition.
    {
      extern int yydebug;
      yydebug = 1;
    }

    Does not work with bison
  */

  /* Enter interactive mode.  */
  if (option_interactive) {
    set_ctrl_c_handle(); /* Override Control-C */
    go_interactive();
  }
}

/* Parse an smv/spl program, in the filename input_file (using yy_parse).
   Exit program if there was an error in parsing. */
void parse_smv_input_file(char *filename)
{
  char *tempfile;
  char *tempf = filename;

  /* Check that the file exists, if not, check if exists in
     system directory. It returns the complete filename where
     the file has been found */

  if (filename == 0)
    rpterr("Error: The smv file should be the last parameter on the command "
           "line\n");
  else if ((tempf = find_file_in_path(filename)) == NULL)
    rpterr("cannot open %s for input", filename);
  else {
    filename = tempf;
    if (verbose)
      fprintf(tlvstdout, "Loading file %s.\n", filename);
  }

  /* If the file has .spl suffix then assume it is spl file,
     and invoke spl to smv compiler.  */
  if (!strcmp(filename + strlen(filename) - 4, ".spl")) {
    char command[200];
    int result;

    tempfile = tmpnam(NULL);

    source_is_spl = 1;
    if (verbose)
      fprintf(stderr, "Compiling spl file into temporary file %s\n",
              tempfile);
    command[0] = (char) NULL;
    sprintf(command, "splc -s %s -o %s", filename, tempfile);

    /* Execute command for compiling spl into smv */
    result = system(command);
    if (verbose) fprintf(stderr, "result = %d\n", result);

    if (result) exit(1);

    filename = tempfile;
  }

  open_input(filename);
  input_fileno = fname2num(filename);

  fprintf(stdout, "TLV version " TLV_VERSION "\n");
  if (verbose) {fprintf(stdout, "Parsing..."); fflush(stderr);}
  if (yyparse()) exit(1);  /* Parse input file.  */
  if (verbose) fprintf(stdout, "done.\n");

  /* Close input file */
  close_input();

  if (source_is_spl && !verbose)
    remove(tempfile);

  /*------------------------------------------------------------*/
  /* This is the main procedure where all the real work is done */
  /*------------------------------------------------------------*/

  smv2fts();
}

void finished_parsing_smv() {
  loading_smv_file = 0;
}
