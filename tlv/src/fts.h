/* These are Routines for dealing with data structures such as fts and
   components.

  FTS stands for Fair Transition System. Each system is translated to an
  fts. A single smv file may contain several systems, and thus generate
  several fts-s. */

/* The types fts_data, and component_type are the most important
   data types in this file. In various passes over the source smv
   files, the information is collected and calculated using
   this data structure.

   fts_data is a linked list of fair transition systems.
   Each system generates a link in the list, i.e. an fts.
   Most smv files only contain a single system.

   One field of fts_data is "components" which contains
   a tree of components. A component is an instantiated module.
   If a system does not instantiate any additional modules
   (beside main) then there will be only one node in components.
   Otherwise the tree of components will indicate how the
   components are composed, whether synchronously or
   asynchronously.
 */

typedef struct component_type {

  /* Information which was gathered during instantiation */

  node_ptr owned ; /* Variables which the component modifies + OWNED section */
  node_ptr trans;  /* TRANS sections */
  node_ptr assign; /* ASSIGN sections */

  /* Information which is calculated */
  /*    bdd_ptr local_t;
        bdd_ptr local_d; */

  /* Information PROPogated from bottom to top */

  /* List of variables owned by component.
     A variable which is owned will not be preserved by a transition
     which is associated with this component, but will be preserved
     in other transitions. */
  node_ptr prop_owned;

  /* Bdd's which are parts of the transition associated with this component. */
  bdd_ptr  prop_t;  /* TRANS and next() assignments. */
  bdd_ptr  prop_d; /* Combinational assignments. */

  node_ptr  prop_t_F;  /* TRANS and next() assignments. */
  node_ptr  prop_d_F; /* Combinational assignments. */

  /* Information about sons. */
  int composition_type;  /* Either SYNCHCOMP or ASYNCHCOMP */
  struct component_type *c1, *c2;  /* Pointers to sons. */

  /* Context in which component was defined. */
  node_ptr context;
} component_rec, *component_ptr;

struct fts_data {
    int fts_no;  /* Serial id of fts. */
    node_ptr name;

    /* List of variables defined in fts.*/
    node_ptr variables;

    /* List of kind names. */
    node_ptr kinds ;

    component_ptr components;  /* Tree of all components. */

    /* Items which are computed per system. */

    /* Initial condition. */
    node_ptr init;

    /* Bdd which stores identity relation V = V'*/
    bdd_ptr id;

    /* Fairness conditions. */
    node_ptr just;
    node_ptr compassion;

   /* list of ltl formulas with name of primary variable. */
    node_ptr ltl_list;

    struct fts_data *next;  /* Next system */
} ;

typedef struct fts_data *fts;

extern fts fts_list;  /* Don't use these directly. */
extern node_ptr list_of_all_kinds;

/**********************************************************************/
/* Creating new objects.                                              */
/**********************************************************************/

/* Create and return new fts. */
fts new_fts(node_ptr sys_name);

/* Create and return new component. */
component_ptr new_component(void);

/* Create and return new component, filled with 
   composition type, two child components, and context */
component_ptr new_component_fill(int ctype,
                                 component_ptr c1, component_ptr c2,
                                 node_ptr context);



/**********************************************************************/
/* Composing objects.                                                 */
/**********************************************************************/

/* Return a component which is a syncronous composition of 
   components c1,c2 . */
component_ptr synch_compose(component_ptr c1, component_ptr c2);

/* Adds an asynchronous "process" component to the fts */
void add_component_as_top_process_of_fts(fts f, component_ptr c);


/**********************************************************************/
/*                                                  */
/**********************************************************************/

/* Returns 1 if the component is empty. */
int empty_component(component_ptr c);

/* Add the variable of the system f, to the sets of kinds specified in 
   the kind_list. */
void add_kinds(fts f, node_ptr variable, node_ptr kind_list);


/**********************************************************************/
/*                                                  */
/**********************************************************************/

/* Call this after all fts have been created. 
   It numbers the fts's and sets some dynamic variable. */
void number_fts(void);


/**********************************************************************/

/* Definitions which can should be used in order to access
   and traverse the fts structures. */

/* Get id number of fts f */
#define FTS_NUM(f) f->fts_no

#define FTS_NAME(f) f->name

#define LOOP_OVER_FTS_LIST(f) for (f = fts_list; f ; f = f-> next)
#define LOOP_OVER_ALL_KINDS(k) for (k = list_of_all_kinds; k; k = cdr(k))


#define add_init_to_fts( f, i ) f->init = find_node(AND,f->init, i);
#define add_justice_list_to_fts( f, jl )  f->just = append(f->just, jl);
#define add_compassion_to_fts( f, cp, cq )  f->compassion = \
         cons( cons( cp, cq), f->compassion);

#define add_assign_to_component(c, ass) c->assign = find_node(AND, ass, c->assign);
