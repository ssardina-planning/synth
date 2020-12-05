/**********************************************************************

 This file defines node which have knowledge of the
 internal structure of smv/tlv parse trees. How they
 should be constructed, and how information is be retrieved from
 the parse tree.

**********************************************************************/



/**********************************************************************
  SMV Program structure
 **********************************************************************/

/* Constructing and accessing programs. */

#define LOOP_OVER_MODULES(program, currmodule, temp_node_ptr) \
  for (temp_node_ptr=program, currmodule=car(temp_node_ptr); \
       currmodule; \
       temp_node_ptr = cdr(temp_node_ptr), \
         currmodule = (temp_node_ptr == NIL) ? NIL : car(temp_node_ptr) )

/* Constructing and accessing modules. The signature is the name and
   parameters of the module. */

#define new_module(signature, sections)  new_node(MODULE,signature, sections)
#define new_signature(name, params)  new_node(MODTYPE,name,params)

#define name_of_module(module)      find_atom(caar(module))
#define params_of_module(module)    cdar(module) /* Get parameter list of module */
#define sections_of_module(module)  cdr(module)


/* Returns true if node is probably a term. */
#define is_term(n) (n != NIL && (n->type == ARRAY || n->type == DOT || n->type == ATOM ))


/**********************************************************************
  SMV assignments in ASSIGN section.
 **********************************************************************/

/* Create a new left hand side which can be either: term, init(term) or next(term).
   kind is either CURRENT_ASS, SMALLINIT or NEXT */
#define CURRENT_ASS ((NEXT > SMALLINIT) ? NEXT + 1 : SMALLINIT + 1)
#define new_left_hand_side(kind, term) ( kind == CURRENT_ASS ? term : new_node(kind,term,NIL)  )
#define is_init_lhs(lhs) ( lhs->type == SMALLINIT )
#define is_next_lhs(lhs) ( lhs->type == NEXT )
#define is_current_lhs(lhs) ( is_term(lhs) )

#define new_smv_assignment(lhs, expr) ( new_node(EQDEF,lhs,expr) )
#define is_init_assignment(ass) ( is_init_lhs(car(ass)) )
#define is_next_assignment(ass) ( is_next_lhs(car(ass)) )
#define is_current_assignment(ass) ( is_current_lhs(car(ass)) )

/* get left hand side of assignment */
#define lhs_of_assignment(ass) ( car(ass) )
/* Get term of left hand side of assignment (stripped of NEXT, INIT) */
#define term_of_assignment(ass) ( is_current_assignment(ass) ? car(ass): caar(ass) )


/**********************************************************************
 Things common to smv and tlv
 **********************************************************************/

#define new_smv_if(condition, then, els) new_node(IFSMV,condition,cons(then,els)) 
#define new_tlv_if(condition, then, els) new_node(IF,   condition,cons(then,els)) 

#define condition_of_if(if_node) car(if_node)
#define then_of_if(if_node) cadr(if_node)
#define else_of_if(if_node) cddr(if_node)


/**********************************************************************
  Expressions
 **********************************************************************/


/* Constructing expressions */
#define new_true new_node(TRUEEXP,NIL,NIL)

#define new_default_param(param, value) new_node(EQDEF, param, value)
#define is_default_param(p) (p->type == EQDEF)
#define default_param_formal(p) (p->left.nodetype)
#define default_param_value(p) (p->right.nodetype)

/**********************************************************************
  TLV Basic
 **********************************************************************/

/*#define new_tlvfor(atom, from, to, stmts) new_node(TLVFOR,new_node(IN,atom,cons(from,to)),stmts)
  #define atom_of_tlvfor(for_node)  caar(for_node)
  #define from_of_tlvfor(for_node) cadar(for_node)
  #define to_of_tlvfor(for_node)   cddar(for_node)
  #define stmts_of_tlvfor(for_node)  cdr(for_node)
*/


#define is_loop_stmt(stmt) ( stmt->type == WHILE )
/*  || stmt->type == TLVFOR || stmt->type == FIX )*/

node_ptr new_tlvfor(node_ptr atom,
                    int direction,  /* PLUS or MINUS */ 
                    node_ptr from, node_ptr to, 
                    node_ptr stmts);

node_ptr new_fix(node_ptr expr,
                 node_ptr stmts);
