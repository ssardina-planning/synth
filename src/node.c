/***************************************************************************\
*module: nodemgr                                                            *
*created: 12-18-87 by KLM                                                   *
*uses: smv.h                                                                *
*init: init_node                                                            *
*                                                                           *
*allocate and initialize nodes                                              *
*                                                                           *
*                                                                           *
* Changed to implement bounded until - Sergio Campos - 05/92                *
*                                                                           *
* Changed implementation of bounded for SMV 2.3                             *
*   - steed@iil.intel.com - 07/92                                           *
*                                                                           *
\***************************************************************************/
#include <stdio.h>
#include <storage.h>
#include <node.h>
#include <hash.h>
#include <mystring.h>
#include <util_err.h>
#include <assoc.h>
#include <y.tab.h>

/* Define record manager and hash table for nodes */
static mgr_ptr node_mgr;
static hash_ptr node_hash;

/* An associative hash table */
hash_ptr subst_hash;

#define NODE_HASH_SIZE 16381

/* Pointers to nodes which contain the numbers 0,1 */
node_ptr zero_number,one_number;

/* Pointer to node which is a list of the two previous node :
   zero_number and one_number.  Types in SMV are represented
   as lists of items, so this variable will contain the
   boolean type: a list of {0,1} */
node_ptr boolean_type;


/* Node hash function for hash table */
static int node_hash_fun(rec_ptr n)
{
  return((( ((node_ptr)n)->type)     )  +
	 (( ((node_ptr)n)->left.inttype) << 1)  +
	 (( ((node_ptr)n)->right.inttype) << 2));
}

/* Node equality function for hash table */
static int node_eq_fun(rec_ptr node1, rec_ptr node2)
{
  return(( ((node_ptr)node1)->left.inttype == ((node_ptr)node2)->left.inttype) &&
	 ( ((node_ptr)node1)->right.inttype == ((node_ptr)node2)->right.inttype) &&
	 ( ((node_ptr)node1)->type == ((node_ptr)node2)->type));
}



/***************************************************************************\
*function: init_node							    *
*									    *
*initialize node manager						    *
\***************************************************************************/
void init_node()
{
  node_mgr = new_mgr(sizeof(struct node));

  node_hash = new_hash(NODE_HASH_SIZE,node_hash_fun,node_eq_fun,node_mgr);
  subst_hash = new_assoc();

  /* Initialize constants which are used a lot */
  zero_number = find_NUMBER_node(0);
  one_number = find_NUMBER_node(1);

  boolean_type = cons(zero_number,cons(one_number,NIL));
}


/***************************************************************************\
*function: new_node							    *
*									    *
*allocates and initializes space for one node				    *
\***************************************************************************/
node_ptr new_node(int type, node_ptr left, node_ptr right)
{
    extern int yylineno;
    extern int input_fileno;
    node_ptr temp;
    temp = (node_ptr) new_rec (node_mgr);
    temp -> type = type;
    temp -> fileno = input_fileno;
    temp -> lineno = yylineno;
    temp -> left.nodetype = left;
    temp -> right.nodetype = right;
    return temp;
}

node_ptr find_node(int type, node_ptr left, node_ptr right)
{
  extern int yylineno;
  extern int input_fileno;
  node_rec temp;

  temp.type = type;
  temp.fileno = input_fileno;
  temp.lineno = yylineno;
  temp.left.nodetype = left;
  temp.right.nodetype = right;
  return (node_ptr) insert_hash(node_hash, (rec_ptr) &temp);
}


node_ptr new_NUMBER_node(int num)
{
  return new_node(NUMBER, (node_ptr) num, NIL);
}

node_ptr find_NUMBER_node(int num)
{
  return find_node(NUMBER, (node_ptr) num, NIL);
}

node_ptr new_string_node(int type, char *s, node_ptr right)
{
  return new_node(type, (node_ptr) find_string(s), right);
}

/* Find an atom in the node hash */
node_ptr find_atom(node_ptr a)
{
  if (a == NIL)
    return a;
  return
    find_node(a->type, a->left.nodetype, a->right.nodetype);
}

/* Turn a string (char *) into an ATOM */
node_ptr string_to_atom(char *s)
{
  return find_node(ATOM, (node_ptr) find_string(s), NIL);
}

char *atom_to_string(node_ptr a)
{
  return a->left.strtype->text;
}

/*----------------------------------------------------------------------*/
/*  Lisp like functions, which manipulate lists                         */
/*----------------------------------------------------------------------*/

/* Concatenate two nodes into a list */
node_ptr cons(node_ptr x, node_ptr y)
{
  return new_node(LIST,x,y);
}

/* Return left son */
node_ptr car(node_ptr n)
{
  return n->left.nodetype;
}

void set_car(node_ptr n, node_ptr new_car)
{
  n->left.nodetype = new_car;
}

/* Return right son */
node_ptr cdr(node_ptr n)
{
  return n->right.nodetype;
}

void set_cdr(node_ptr n, node_ptr new_cdr)
{
  n->right.nodetype = new_cdr;
}

/* Append y to the rightmost leave of the tree whose root is x */
node_ptr append(node_ptr x, node_ptr y)
{
  if(x==NIL)return(y);
  x->right.nodetype = append(x->right.nodetype,y);
  return(x);
}


/* Check if item n is in list r. Returns 1 if is in, 0 otherwise. */
int in_list(node_ptr n,node_ptr r)
{
  while(r){
    if(car(r) == n)return(1);
    r = cdr(r);
  }
  return(0);
}

int member(node_ptr n,node_ptr r)
{
  return in_list(n,r);
}

/* Returns the length of the list. */
int length(node_ptr n)
{
  int result=0;
  node_ptr temp =n;

  while (temp) {
    temp = cdr(temp);
    result++;
  }
  return result; 
}

int list_length(node_ptr n)
{
  return length(n);
}

/* Builds a (reverse) list of elements from l1 that are not in l2.
   Preserves the arguments */
node_ptr list_minus(node_ptr l1, node_ptr l2)
{
  node_ptr tmp = NIL;
  while (l1) {
    if (!member(car(l1), l2))
      tmp = cons(car(l1), tmp);
    l1 = cdr(l1);
  }
  return tmp;
}

/* Remove one item l2, of l1. If l2 is not a member of l1 then
   l1 remains the same. Doesn't preserve l1. */
node_ptr list_minus_one(node_ptr l1, node_ptr member)
{
  /* if (l1 == NIL) */
  /*   return NIL; */
  /* else if (car(l1) == member)  /* Remove the item. */
  /*   return cdr(l1); */
  /* else { */
  /*   l1->right.nodetype = list_minus_one(cdr(l1), member); */
  /*   return l1; */
  /* } */

  node_ptr result;
  if (l1 == NIL)
    result = NIL;
  else if (car(l1) == member)
    result = cdr(l1);
  else {
    node_ptr rest = cdr(l1), prev = l1;
    while (rest != NIL && car(rest) != member) {
      prev = rest;
      rest = cdr(rest);
    }
    if (rest != NIL)
      set_cdr(prev, cdr(rest));
    result = l1;
  }
  return result;
}


/* Executes a function on a list and returns transformed list */
node_ptr map(node_ptr (*f)(node_ptr n), node_ptr l)
{
  node_ptr t;
  if(l == NIL)return(NIL);
  t = (*f)(car(l));
  return(cons(t,map(f,cdr(l))));
}

void walk(void (*f)(node_ptr n),node_ptr l)
{
  if(l == NIL)return;
  (*f)(car(l));
  walk(f,cdr(l));
}

/* Reverse the list order of n */
node_ptr reverse(node_ptr n)
{
  node_ptr y=NIL;
  while(n){
    node_ptr z = n->right.nodetype;
    n->right.nodetype = y;
    y = n;
    n = z;
  }
  return(y);
}

/* Return last item of list. */
node_ptr last(node_ptr n)
{
  if(!n)catastrophe("last: n == NIL");
  if(!cdr(n))return(car(n));
  return(last(cdr(n)));
}


/* Return list of odd elements in list  1,3,5,...
   ( the root's index is 1 so it is returned) */
node_ptr odd_elements(node_ptr l)
{
  if(l == NIL)return(NIL);
  return(cons(car(l),even_elements(cdr(l))));
}

/* Return list of even elements in list. */
node_ptr even_elements(node_ptr l)
{
  if(l == NIL)return(NIL);
  return(odd_elements(cdr(l)));
}


/***************************************************************************\
*function: free_node							    *
*									    *
*free space allocated to a node						    *
\***************************************************************************/
void free_node(node_ptr n)
{
  free_rec(node_mgr, (rec_ptr) n);
}

void free_list(node_ptr a)
{
  if(a==NIL)return;
  free_list(cdr(a));
  free_node(a);
}


char *op_string(node_ptr n)
{
  if (!n) return "";

  switch (n->type) {
  case TRUEEXP: return "TRUE";
  case FALSEEXP: return "FALSE";
  case ATOM:
  case DOT:
  case ARRAY: return "ident";
  case FUNC: return "func";
  case NEXT:   return "next";
  case NUMBER: return "number";
  case LIST: return "list";
  case TWODOTS: return "..";
  case IMPLIES: return "->";
  case IFF: return "<->";
  case OR: return "|";
  case AND: return "&";
  case NOT: return "!";

  case EQUAL: return "="; 
  case NOTEQUAL: return "!="; 
  case LT:    return "<";
  case GT:    return ">";
  case LE:    return "<=";
  case GE:    return ">=";

  case UNION: return "union";
  case SETIN: return "in"; 

  case MOD:   return "mod";
  case PLUS:  return "+";
  case MINUS: return "-";
  case TIMES: return "*";
  case DIVIDE: return "/";

  case LTL: return "ltl"; 
  case CTL: return "ctl"; 
  case NEXT_LTL: return "()"; 
  case EVENTUALLY:   return "<>"   ;
  case ALWAYS:       return "[]"    ;
  case WEAKPREVIOUS: return "(~)"   ;
  case PREVIOUSLY:   return "(_)"   ;
  case ONCE:         return "<_>"   ;
  case HASALWAYSBEEN:return "[_]"    ;
  case LTLUNTIL:     return "Until" ;
  case WAITINGFOR:   return "Awaits";
  case SINCE:        return "Since" ;
  case BACKTO:       return "Backto";
  case ENTAILS:      return "==>"   ;
  case CONGRUENT:    return "<==>"  ;

  case EX: return "EX";
  case AX: return "AX";
  case EF: return "EF";
  case AF: return "AF";
  case EG: return "EG";
  case AG: return "AG";
  case EU: return "EU";
  case AU: return "AU";
  case EBU: return "EBU";
  case ABU: return "ABU";
  case EBF: return "EBF";
  case ABF: return "ABF";
  case EBG: return "EBG";
  case ABG: return "ABG";

  default:     return "";
  }
}


int int_number_of_operands(int typ)
{
  switch (typ) {

  case TRUEEXP: 
  case FALSEEXP:
  case ATOM:
  case DOT:
  case ARRAY: 
  case NUMBER: return 0;

  case NOT:
  case NEXT:
  case LTL: 
  case CTL: 
  case NEXT_LTL: 
  case EVENTUALLY:   
  case ALWAYS:       
  case WEAKPREVIOUS: 
  case PREVIOUSLY:   
  case ONCE:         
  case HASALWAYSBEEN:
  case EX: 
  case AX: 
  case EF: 
  case AF: 
  case EG: 
  case AG: return 1 ;

  case LIST: 
  case TWODOTS: 
  case IMPLIES: 
  case IFF: 
  case OR: 
  case AND: 
  case EQUAL:
  case NOTEQUAL:
  case LT:   
  case GT:
  case LE:
  case GE:
  case UNION: 
  case SETIN: 
  case MOD:   
  case PLUS:  
  case MINUS: 
  case TIMES: 
  case DIVIDE: 
  case LTLUNTIL:       
  case WAITINGFOR:  
  case SINCE:       
  case BACKTO:      
  case ENTAILS:     
  case CONGRUENT:   
  case UNTIL:  
  case BUNTIL:  
  case EU:  
  case AU:  return 2;

  case EBF: 
  case ABF: 
  case EBG: 
  case ABG: return 3;

  case EBU: 
  case ABU: return 4 ;

  default: return 2;
  }

}

int number_of_operands(node_ptr n)
{
  if (!n) return 0;

  return int_number_of_operands(n->type);
}



int int_priority(int typ)
{
  switch (typ) {

  /* For the items which return negative numbers, we want to be sure
     that parenthesis will be added . */  
  case LTL: 
  case CTL: return -2; 

  case NEXT:   return -1;

  case TWODOTS: return 3;

  case IMPLIES: 
  case IFF: return 4;

  case OR: return 5;

  case AND: return 6;

  case NOT: return 7;

  case LTLUNTIL:        
  case WAITINGFOR:   
  case SINCE:        
  case BACKTO: return 8;

  case NEXT_LTL:     
  case EVENTUALLY:   
  case ALWAYS:       
  case WEAKPREVIOUS: 
  case PREVIOUSLY:   
  case ONCE:         
  case HASALWAYSBEEN:
  case ENTAILS:      
  case CONGRUENT:    
  case EX: 
  case AX: 
  case EF: 
  case AF: 
  case EG: 
  case AG: 
  case EBF: 
  case ABF: 
  case EBG: 
  case ABG: return 9;

  case EQUAL: 
  case NOTEQUAL:
  case LT:    
  case GT:    
  case LE:    
  case GE:    
  case EU: 
  case AU: 
  case EBU:
  case ABU: return 10;

  case UNION: return 11;
  case SETIN: return 12; 

  case MOD:   return 13;
  case PLUS:  
  case MINUS: return 14;
  case TIMES: 
  case DIVIDE: return 15;

  default:     return 0;
  }
}

int priority(node_ptr n)
{
  if (!n) return 0;

  return int_priority(n->type);

}


int is_tl(int typ)
{
  switch (typ) {
  case LTLUNTIL:        
  case WAITINGFOR:   
  case SINCE:        
  case BACKTO: 

  case NEXT_LTL:     
  case EVENTUALLY:   
  case ALWAYS:       
  case WEAKPREVIOUS: 
  case PREVIOUSLY:   
  case ONCE:         
  case HASALWAYSBEEN:
  case ENTAILS:      
  case CONGRUENT:    
  case EX: 
  case AX: 
  case EF: 
  case AF: 
  case EG: 
  case AG: 
  case EBF: 
  case ABF: 
  case EBG: 
  case ABG: return 1;
  }

  return 0;
}

int is_relation(int typ)
{
  switch (typ) {
  case EQUAL: 
  case NOTEQUAL:
  case LT:    
  case GT:    
  case LE:    
  case GE:    
  case SETIN: return 1;
  }

  return 0;
}

/***************************************************************************\
* function: my_strncat
*
* concatenate string s2 to the end of string s1. The total length of s1
* cannot be bigger then size. If it is bigger then size then it is cut
* to be size "size" and a non zero value is returned.
* If strncat was successfull then 0 is returned.
\***************************************************************************/
static int my_strncat(char *s1, char *s2, int size)
{
  while(size && *s2){
    if(*s1)
      s1++;
    else{
      *(s1++) = *(s2++);
      *s1 = 0;
    }
    size--;
  }
  return(!*s2);
}

/***********************************************************************
 This is the routine which actually prints the node "n: into buffer
 "str" of size "size"

 The "p" parameter contains the priority of the parent of the current
 node "n". The local variable "prio" contains the current priority.
 If prio < p then this means that the current node was surrounded by
 parenthesis.
 For example, the expresion 1 * 2 + 3 would be parsed as (1 * 2) + 3.
 But if we want 1 * ( 2 + 3 ) then we must use the parenthesis. This
 would appear in the parse tree as:

    *
   / \
  1   +
     / \
     2  3

 However, the parse tree doesn't contain the parenthesis. So in order
 to print the expression back to the user in the way that the user entered
 the expression we have to find where the priority of a node is lower
 than its parent and then print parentheis around this expression.

 ***********************************************************************/



static int put_brackets(int prio, int p, node_ptr n)
{
  if (
       /* We want to put brackets around expressions which are nested 
          deeper in the tree yet have lower priority. */
       prio< p ||

       /* Another case we want brackets is when a relational expression
          ( e.g x = y) is a subexpression of a temporal operator. Although
          the priorities do not make a parenthesis necessary, adding 
          parenthesis makes things much clearer. */
       (is_relation(n->type) && (p == int_priority(ALWAYS) || 
                                 p == int_priority(LTLUNTIL) ) ) ||
  
       /* Another case we want brackets is when we have a sequence
          of temporal operators with two operands. The right associativity
          is not usually displayed well, so in this case we always display
          the brackets */

       (is_tl(n->type) && number_of_operands(n) == 2 && p == prio)

       /* Finally, always put brackets around Implies */
       || n->type == IMPLIES
      )
    return 1;

  return 0;
}


static int sprint_node1(char *str, int size, node_ptr n, int p)
{
  char *op;
  int prio;
  int put_brack ;

  if (!n) return(1);
  if (n == (node_ptr)(-1))
    return(my_strncat(str, "*no value*", size));

  switch (n->type) {
  case CONTEXT:
    if (car(n)!= NIL)
      return
        my_strncat(str, "<", size) &&
        sprint_node(str, size, car(n)) &&
        my_strncat(str, ">", size) &&
        sprint_node(str, size, cdr(n));
    else
      return sprint_node1(str, size, cdr(n), p);
  case QUOTE:
    return my_strncat(str, atom_to_string(n), size);
  case TRUEEXP:
    return my_strncat(str, "TRUE", size);
  case FALSEEXP:
    return my_strncat(str, "FALSE",size);
  case ATOM:
    if (!my_strncat(str, n->left.strtype->text, size))
      return 0;
    if (cdr(n)) {
      char buf[20];
      sprintf(buf, "_%d", n->right.inttype);
      return my_strncat(str, buf, size);
    }
    return 1;
  case NUMBER:
    {
      char buf[20];
      sprintf(buf, "%d", n->left.inttype);
      return my_strncat(str, buf, size);
    }
  case DOT:
    if (!n->left.nodetype)
      return sprint_node(str, size, n->right.nodetype);
    return
      sprint_node(str, size, n->left.nodetype) &&
      my_strncat(str, ".", size) &&
      sprint_node(str, size, n->right.nodetype);
  case LIST:
    return
      sprint_node(str, size, n->left.nodetype) &&
      (!n->right.nodetype ||
       (my_strncat(str, ",", size) &&
        sprint_node(str, size, n->right.nodetype)));
  case ARRAY:
    return
      sprint_node(str, size, n->left.nodetype) && my_strncat(str, "[", size) &&
      sprint_node(str, size, n->right.nodetype) && my_strncat(str, "]", size);

  case NEXT:
    return
      my_strncat(str, "next(", size) &&
      sprint_node1(str, size, n->left.nodetype, 0) &&
      my_strncat(str, ")", size);

  case SMALLINIT:
    return
      my_strncat(str, "init(", size) &&
      sprint_node1(str, size, n->left.nodetype, 0) &&
      my_strncat(str, ")", size);

  case EQDEF:
    return
      sprint_node1(str, size, n->left.nodetype, 0) &&
      my_strncat(str, " := ", size) &&
      sprint_node1(str, size, n->right.nodetype, 0) &&
      my_strncat(str, ";", size);

  case EU:
  case AU:
    if (n->type == EU)
      {if(!my_strncat(str,"E",size))return(0);}
    else
      if(!my_strncat(str,"A",size))return(0);

    prio = 8; 

    return (!my_strncat(str,"(",size) &&
            sprint_node1(str,size,n->left.nodetype,prio) &&
            my_strncat(str," U ",size) &&
            sprint_node1(str,size,n->right.nodetype,prio) &&
            my_strncat(str,")",size));

  case EBU:
    if(!my_strncat(str,"E",size))return(0);
    op = "BU"; prio = 8; p = 9; break;
  case ABU:
    if(!my_strncat(str,"A",size))return(0);
    op = "BU"; prio = 8; p = 9; break;

  case EBF: op = "EBF "; prio = 8;  break;
  case ABF: op = "ABF "; prio = 8;  break;
  case EBG: op = "EBG "; prio = 8;  break;
  case ABG: op = "ABG "; prio = 8;  break;

  case TWODOTS:
  case IMPLIES:
  case IFF: 
  case OR: 
  case AND: 
  case NOT: 

  case NEXT_LTL:     
  case EVENTUALLY:   
  case ALWAYS:       
  case WEAKPREVIOUS: 
  case PREVIOUSLY:   
  case ONCE:         
  case HASALWAYSBEEN:
  case LTLUNTIL:        
  case WAITINGFOR:   
  case SINCE:        
  case BACKTO:       
  case ENTAILS:      
  case CONGRUENT:    

  case EX: 
  case AX: 
  case EF: 
  case AF: 
  case EG: 
  case AG: 

  case NOTEQUAL:
  case EQUAL: 
  case LT:    
  case GT:    
  case LE:    
  case GE:    
  case UNION: 
  case SETIN: 
  case MOD:   
  case PLUS:  
  case MINUS: 
  case TIMES: 
  case DIVIDE: prio = priority(n); break;

  case CASE: 
    if (p != -1)
      if(!my_strncat(str," ( case ",size))return(0);

    if(!sprint_node1(str,size,caar(n),-1))return(0);    
    if(!my_strncat(str," : ",size))return(0);
    if(!sprint_node1(str,size,cdar(n),-1))return(0);    
    if(!my_strncat(str," ; ",size))return(0);
    if(!sprint_node1(str,size,cdr(n),-1))return(0);    

    if (p != -1)
      if(!my_strncat(str," esac ) ",size))return(0);

    return 1;
    break;

  case FUNC: 
    if(!sprint_node1(str,size,n->left.nodetype,prio))return(0);
    if(!my_strncat(str,"(",size))return(0);
    { 
      /* Print function arguments. */
      node_ptr arg = n->right.nodetype;
      while (arg) {

        /* Use priority 0 since we do not want an additional parenthesis. */
        if(!sprint_node1(str,size,arg,0))return(0);

        arg = cdr(arg);
        if (arg) 
        if(!my_strncat(str,",",size))return(0);
      }
      
    }

    if(!my_strncat(str,")",size))return(0);

    return 1;

  default:
    fprintf(stderr,"Dont know how to print type %d\n",n->type);
    return(my_strncat(str,"*no value*",size));
  }


    put_brack = put_brackets(prio,p,n);

  if(put_brack && !my_strncat(str,"(",size))return(0);


  switch(number_of_operands(n)){
  case 1:
    if(!my_strncat(str,op_string(n),size))return(0);
    if(!sprint_node1(str,size,n->left.nodetype,prio))return(0);
    break;
  case 2:
    if(!sprint_node1(str,size,n->left.nodetype,prio))return(0);
    if(!my_strncat(str," ",size))return(0);
    if(!my_strncat(str,op_string(n),size))return(0);
    if(!my_strncat(str," ",size))return(0);
    if(!sprint_node1(str,size,n->right.nodetype,prio))return(0);
    break;
  case 3:
    /* EF a..b f */
    if(!my_strncat(str,op,size))return(0);                /* EF */
    if(!sprint_node1(str,size,(n->right.nodetype)->left.nodetype,prio))
                                       return(0);         /* a */
    if(!my_strncat(str,"..",size)) return(0);
    if(!sprint_node1(str,size,(n->right.nodetype)->right.nodetype,prio))
                                       return(0);         /* b */
    if(!my_strncat(str," ",size))return(0);
    if(!sprint_node1(str,size,n->left.nodetype,prio))return(0); /* f */
    break;
  case 4:
    /* E[f BU a..b g] */
    if(!sprint_node1(str,size,(n->left.nodetype)->left.nodetype,prio))
                                       return(0);         /* f */
    if(!my_strncat(str," ",size))return(0);
    if(!my_strncat(str,op,size))return(0);                /* BU */
    if(!my_strncat(str," ",size))return(0);
    if(!sprint_node1(str,size,(n->right.nodetype)->left.nodetype,prio))
                                       return(0);         /* a */
    if(!my_strncat(str,"..",size)) return(0);
    if(!sprint_node1(str,size,(n->right.nodetype)->right.nodetype,prio))
                                       return(0);         /* b */
    if(!my_strncat(str," ",size))return(0);
    if(!sprint_node1(str,size,(n->left.nodetype)->right.nodetype,prio))
                                       return(0);         /* g */
    break;
  }

  if(put_brack && !my_strncat(str,")",size))return(0);

  return(1);
}



/* Print a node "n" to a buffer "str" of size "size */
int sprint_node(char *str, int size, node_ptr n)
{
  return(sprint_node1(str,size,n,0));
}

static int indent_size = 0;

void add_to_indent(int i)
{
  indent_size += i;
}

/* Print node n to stream at a specific column */
static int print_node_atcol(FILE *stream,
                            node_ptr n,
                            int col)
{
  char buf[41];
  int c,p;
  buf[0] = 0;

  /* Print the node into the buffer "buf" */
  c = sprint_node(buf,40,n);

  p = strlen(buf);
  if(!c) p += 3;

  /* If we are too wide then reset "col" to produce right alignment */
  if(col + p >= 79){
    fprintf(stream,"\n");
    col = 0;
    while((col++) < indent_size + 1)fprintf(stream,"  ");
  }

  /* Print the buffer on the screen */
  fprintf(stream,"%s",buf);

  /* If there was not enough space in "buf" print "..." */
  if(!c)fprintf(stream,"...");
  return(col + p);
}

/* Print node n to stream */
void print_node(FILE *stream, node_ptr n)
{
  print_node_atcol(stream,n,0);
}



/********************************************************************/

/* Printing node to a file */

void fprint_list_cb(ff,l)
FILE *ff;
node_ptr l;
{
  fprintf(ff,"{");
  while(l) {
    fprint_node(ff,car(l));
    if(cdr(l)) fprintf(ff,",");
    l=cdr(l);
  }
  fprintf(ff,"}");
}

void fprint_list_rev(ff,l)
FILE *ff;
node_ptr l;
{
  if(l==NIL) return;
  fprint_list_rev(ff,cdr(l));
  if(cdr(l)) fprintf(ff,",");
  fprint_node(ff,car(l));
  l=cdr(l);
}

static void fprint_node1(ff,n,p)
FILE *ff;
node_ptr n;
int p;
{
  char *op;
  int prio,
      opkind;     /* 0: unary, 1: binary, 2: terciary, 3:quad */
  int put_brack;

  if(!n)return;
  if(n == (node_ptr)(-1)) { fprintf(ff," *no value* "); return;}
  switch(n->type){
  case TRUEEXP:
    fprintf(ff,"TRUE"); return;
  case FALSEEXP:
    fprintf(ff,"FALSE"); return;
  case ATOM:
    fprintf(ff,n->left.strtype->text); return;
  case NUMBER:
    fprintf(ff,"%d",car(n)); return;
  case DOT:
    if(!n->left.nodetype) fprint_node(ff,n->right.nodetype);
    else {
      fprint_node(ff,n->left.nodetype);
      fprintf(ff,".");
      fprint_node(ff,n->right.nodetype);
    }
    return;
  case LIST: fprint_list_cb(ff,n); return;
  case ARRAY:
    fprint_node(ff,n->left.nodetype);
    fprintf(ff,"[");
    fprint_node(ff,n->right.nodetype);
    fprintf(ff,"]");
    return;
  case TWODOTS: op = ".."; prio = 3; opkind = 1; break;
  case IMPLIES: op = "->"; prio = 4; opkind = 1; break;
  case IFF: op = "<->"; prio = 4; opkind = 1; break;
  case OR: op = "|"; prio = 5; opkind = 1; break;
  case AND: op = "&"; prio = 6; opkind = 1; break;
  case NOT: op = "!"; prio = 7; opkind = 0; break;
  case EX: op = "EX "; prio = 8; opkind = 0; break;
  case AX: op = "AX "; prio = 8; opkind = 0; break;
  case EF: op = "EF "; prio = 8; opkind = 0; break;
  case AF: op = "AF "; prio = 8; opkind = 0; break;
  case EG: op = "EG "; prio = 8; opkind = 0; break;
  case AG: op = "AG "; prio = 8; opkind = 0; break;
  case EU:
    fprintf(ff,"E");
    op = "U"; prio = 8; p = 9; opkind = 1; break;
  case AU:
    fprintf(ff,"A");
    op = "U"; prio = 8; p = 9; opkind = 1; break;
  case EBU:
    fprintf(ff,"E");
    op = "BU"; prio = 8; p = 9; opkind = 3; break;
  case ABU:
    fprintf(ff,"A");
    op = "BU"; prio = 8; p = 9; opkind = 3; break;
  case EBF: op = "EBF "; prio = 8; opkind = 2; break;
  case ABF: op = "ABF "; prio = 8; opkind = 2; break;
  case EBG: op = "EBG "; prio = 8; opkind = 2; break;
  case ABG: op = "ABG "; prio = 8; opkind = 2; break;
#ifdef TIMING
  case MINU:
    fprintf(ff,"MIN");
    op = ","; prio = 8; p = 9; opkind = 1; break;
  case MAXU:
    fprintf(ff,"MAX");
    op = ","; prio = 8; p = 9; opkind = 1; break;
#endif
  case EQUAL: op = "="; prio = 9; opkind = 1; break;
  case NOTEQUAL: op = "!="; prio = 9; opkind = 1; break;
  case LT:    op = "<"; prio = 9; opkind = 1; break;
  case GT:    op = ">"; prio = 9; opkind = 1; break;
  case LE:    op = "<="; prio = 9; opkind = 1; break;
  case GE:    op = ">="; prio = 9; opkind = 1; break;
  case UNION: op = "union"; prio = 10; opkind = 1; break;
  case SETIN: op = "in"; prio = 11; opkind = 1; break;
  case SETNOTIN: op = "notin"; prio = 11; opkind = 1; break;
  case MOD:   op = "mod"; prio = 12; opkind = 1; break;
  case PLUS:  op = "+"; prio = 13; opkind = 1; break;
  case MINUS: op = "-"; prio = 13; opkind = 1; break;
  case TIMES: op = "*"; prio = 14; opkind = 1; break;
  case DIVIDE: op = "/"; prio = 14; opkind = 1; break;
  case NEXT:
    fprintf(ff,"next");
    op = ""; prio = 0; p = 1; opkind = 0; break;
  default:
    catastrophe2("fprint_node1: type = %d",n->type);
  }

  put_brack = put_brackets(prio,p,n);

  if(put_brack)fprintf(ff,"(");
  switch(opkind){
  case 0:
    fprintf(ff,op);
    fprint_node1(ff,n->left.nodetype,prio);
    break;
  case 1:
    fprint_node1(ff,n->left.nodetype,prio);
    fprintf(ff," %s ",op);
    fprint_node1(ff,n->right.nodetype,prio);
    break;
  case 2:
    /* EF a..b f */
    fprintf(ff,op);                /* EF */
    fprint_node1(ff,(n->right.nodetype)->left.nodetype,prio); /* a */
    fprintf(ff,"..");
    fprint_node1(ff,(n->right.nodetype)->right.nodetype,prio); /* b */
    fprintf(ff," ");
    fprint_node1(ff,n->left.nodetype,prio); /* f */
    break;
  case 3:
    /* E[f BU a..b g] */
    fprint_node1(ff,(n->left.nodetype)->left.nodetype,prio); /* f */
    fprintf(ff," %s ",op); /* BU */
    fprint_node1(ff,(n->right.nodetype)->left.nodetype,prio); /* a */
    fprintf(ff,"..");
    fprint_node1(ff,(n->right.nodetype)->right.nodetype,prio); /* b */
    fprintf(ff," ");
    fprint_node1(ff,(n->left.nodetype)->right.nodetype,prio); /* g */
    break;
  }
  if(put_brack)fprintf(ff,")");
  return;
}

void fprint_node(FILE *ff, node_ptr n)
{
  fprint_node1(ff,n,0);
}

void print_node_stdout(node_ptr n)
{
  fprint_node(tlvstdout,n);
}

/**********************************************************************/



void indent(FILE *stream)
{
  int i;
  for(i=0;i<indent_size;i++)fprintf(stream,"  ");
}

void indent_node(FILE *stream,
                 char *s1,node_ptr n,char *s2)
{
  indent(stream);
  fprintf(stream,"%s",s1);
  print_node(stream,n);
  fprintf(stream,"%s",s2);
}

node_ptr subst_node(node_ptr n)
{
  node_ptr m;
  if(n==NIL)return(n);
  switch(n->type){
  case ATOM:
    m = find_assoc(subst_hash,n);
    if(m)return(m);
    else return(n);
  case ATLINE:
    return(find_node(ATLINE,n->left.nodetype,
		     subst_node(n->right.nodetype)));
  default:
    return(find_node(n->type,
		     subst_node(n->left.nodetype),
		     subst_node(n->right.nodetype)));
  }
}

node_ptr key_node(node_ptr n)
{
  if(n==NIL)return(n);
  switch(n->type){
  case ATOM:
    {
      char c = *(n->left.strtype->text);
      if(c <= 'Z' && c >= 'A')return(NIL);
      return(n);
    }
  case ATLINE:
    return(key_node(n->right.nodetype));
  default:
    return(key_node(n->left.nodetype));
  }
}


void make_subst_hash(node_ptr subst)
{
  clear_hash(subst_hash);
  while(subst){
    node_ptr neww = subst->left.nodetype->left.nodetype;
    node_ptr old = subst->left.nodetype->right.nodetype;
    if(find_assoc(subst_hash,old)){
      /*      start_err();*/
      fprintf(stderr,"Multiple substitution for ");
      print_node(tlvstderr,old);
      /*      finish_err();*/
    }
    insert_assoc(subst_hash,old,neww);
    subst = subst->right.nodetype;
  }
}


int isvar_node(node_ptr n)
{
  char firstchar;
  if(n->type != ATOM)return(0);
  firstchar = *(n->left.strtype->text);
  return(firstchar <= 'Z' && firstchar >= 'A');
}

static node_ptr subst_list;

static int unify(node_ptr n1,node_ptr n2)
{
  int v1,v2;
  node_ptr repl;
  if(n1 == n2)return(1);
  if(n1 == NIL || n2 == NIL)return(0);
  v1 = isvar_node(n1);
  v2 = isvar_node(n2);
  if(v1 && (repl = find_assoc(subst_hash,n1)))
    return(unify(repl,n2));
  if(v2 && (repl = find_assoc(subst_hash,n2)))
    return(unify(n1,repl));
  if(v1){
    insert_assoc(subst_hash,n1,n2);
    subst_list = cons(find_node(OVER,n2,n1),subst_list);
    return(1);
  }
  if(v2){
    insert_assoc(subst_hash,n2,n1);
    subst_list = cons(find_node(OVER,n1,n2),subst_list);
    return(1);
  }
  if(n1->type==ATOM || n2->type==ATOM || n1->type != n2->type)return(0);
  return(unify(car(n1),car(n2)) && unify(cdr(n1),cdr(n2)));
}
  
int occur_check(node_ptr n)
{
  if(n == NIL)return(1);
  if(n->type == OVER)n=cdr(n);
  if(isvar_node(n)){
    node_ptr a = find_assoc(subst_hash,n);
    if(a == FAILURE_NODE)return(0);
    if(n){
      insert_assoc(subst_hash,n,FAILURE_NODE);
      if(!occur_check(a))return(0);
      insert_assoc(subst_hash,n,NIL);
    }
    return(1);
  }
  if(n->type == ATOM)return(1);
  return(occur_check(car(n)) && occur_check(cdr(n)));
}

node_ptr unify_node(node_ptr n1, node_ptr n2, node_ptr sl)
{
  subst_list = sl;
  make_subst_hash(sl);
  if(!unify(n1,n2))return(FAILURE_NODE);
  if(occur_check(subst_list))return(subst_list);
  return(FAILURE_NODE);
}

int match1(node_ptr n1, node_ptr n2)
{
  if(n1 == NIL && n2 == NIL)return(1);
  if(n1 == NIL || n2 == NIL)return(0);
  if(isvar_node(n1)){
    node_ptr m = find_assoc(subst_hash,n1);
    if(!m){
      insert_assoc(subst_hash,n1,n2);
      return(1);
    }
    else return(m == n2);
  }
  if(n1->type == ATOM)return(n1 == n2);
  return(n1->type == n2->type
	 && match1(car(n1),car(n2))
	 && match1(cdr(n1),cdr(n2)));
}

int match_node(node_ptr n1, node_ptr n2)
{
  clear_hash(subst_hash);
  return(match1(n1,n2));
}



/******** Implement STACKS ************/

void push_node(node_ptr *stack, node_ptr n)
{
 *stack = cons(n,*stack);
}

node_ptr top_node(node_ptr *stack)
{
 if (*stack == NIL)
   return NIL;
 else
   return (*stack)->left.nodetype;
}

node_ptr pop_node(node_ptr *stack)
{
 node_ptr old = *stack;
 node_ptr result ;

 if (*stack ==NIL)
   return (NIL);
 else {
   result = car(*stack);
   *stack = cdr(*stack);
   free_node(old);
   return(result);
 }
}

int empty(node_ptr stack)
{
  return (stack == NIL);
}



/*----------------------------------------------------------------------*/
/* Numeric functions */
/*----------------------------------------------------------------------*/


node_ptr numeric_op(int (*op)(int a, int b),
                    node_ptr n1, node_ptr n2)
{
  if(n1->type != NUMBER)notanumber(n1);
  if(n2->type != NUMBER)notanumber(n2);
  return find_NUMBER_node((*op)(n1->left.inttype,n2->left.inttype));
}


node_ptr equal_node(node_ptr n1, node_ptr n2)
{
  if(n1 == n2)return(one_number);
  return(zero_number);
}


static int plus_op(int a, int b) { return(a+b); }

node_ptr plus_node(node_ptr n1, node_ptr n2)
{
  return(numeric_op(plus_op,n1,n2));
}


static int minus_op(int a, int b) { return(a-b); }

node_ptr minus_node(node_ptr n1, node_ptr n2)
{
  return(numeric_op(minus_op,n1,n2));
}

static int times_op(int a, int b) { return(a*b); }

node_ptr times_node(node_ptr n1, node_ptr n2)
{
  return(numeric_op(times_op,n1,n2));
}


static int divide_op(int a, int b)
{
  int r = a%b;
  if(r<0)return(a/b-1);
  return(a/b);
}

node_ptr divide_node(node_ptr n1, node_ptr n2)
{
  return(numeric_op(divide_op,n1,n2));
}


static int mod_op(int a, int b)
{
  int r = a%b;
  if(r<0)r += b;
  return(r);
}

node_ptr mod_node(node_ptr n1, node_ptr n2)
{
  return(numeric_op(mod_op,n1,n2));
}




static int lt_op(int a, int b)
{
  if(a < b)return(1);
  return(0);
}

node_ptr lt_node(node_ptr n1, node_ptr n2)
{
  return(numeric_op(lt_op,n1,n2));
}


static int gt_op(int a, int b)
{
  if(a > b)return(1);
  return(0);
}

node_ptr gt_node(node_ptr n1, node_ptr n2)
{
  return(numeric_op(gt_op,n1,n2));
}


/* In this operation the leafs are supposed to be lists (if they
   are not then they are converted to lists ).
   The result operation is that the lists of the two nodes are
   merged to created a unified list of the resulting node */
node_ptr union_node(node_ptr n1, node_ptr n2)
{
  /* Make both arguments to be LIST */
  if(n1 != NIL && n1->type != LIST)n1 = find_node(LIST,n1,NIL);
  if(n2 != NIL && n2->type != LIST)n2 = find_node(LIST,n2,NIL);

  if(n1 == NIL)return(n2);
  if(n2 == NIL)return(n1);

  /* Merge the lists */
  if(car(n1) == car(n2))
    return(find_node(LIST,car(n1),union_node(cdr(n1),cdr(n2))));
  if(((int)car(n1)) < ((int)car(n2)))
    return(find_node(LIST,car(n1),union_node(cdr(n1),n2)));
  return(find_node(LIST,car(n2),union_node(n1,cdr(n2))));
}


/* This operation handles two cases: 

     1) The second node is not a list.
          The action is equivalent to the "equal_node" function.
     2) The second node (n2) is a list :
          The leaf "one_number" is returned if the first
          node is in the list. */

int setin(node_ptr n1, node_ptr n2)
{
  if(n2 == NIL)
      return 0;

  if(n2->type != LIST){
    if(n1 == n2)
       return 1;
    return 0;
  }

  if(n1 == car(n2))
      return 1;

  return setin(n1,cdr(n2));
}

node_ptr setin_node(node_ptr n1, node_ptr n2)
{
  int result = setin(n1,n2);

  if (result)
    return one_number;
  else
    return zero_number;
}


/* Builds a list of elements from l1 that are not in l2.
   Preserves the arguments. Preserves order of elements. */
node_ptr set_minus_node(node_ptr l1, node_ptr l2)
{
  node_ptr tmp=NIL;
  for(;l1; l1=cdr(l1)) 
    if (!member(car(l1),l2)) 
       tmp = append(tmp,cons(car(l1),NIL));
    
  return(tmp);
}


/* Merge with no duplicates. */
node_ptr merge_node(node_ptr n1, node_ptr n2)
{
    if (n1 == NIL || car(n1) == NIL) return n2;
    if (n2 == NIL || car(n2) == NIL) return n1;

    if ( (int)car(n1) > (int)car(n2))
        return cons( car(n2),merge_node(n1,cdr(n2)) );
    else if ( (int)car(n1) < (int)car(n2))
        return cons( car(n1),merge_node(cdr(n1),n2) );
    else 
        return cons( car(n1),merge_node(cdr(n1),cdr(n2)) );
}


node_ptr sort_node(node_ptr n) 
{
    if ( n == NIL || car(n) == NIL || cdr(n) == NIL ) return n;
    {
       node_ptr n1 = sort_node( odd_elements(n) );
       node_ptr n2 = sort_node( even_elements(n) );
      
       return merge_node(n1,n2);
    }
}


    /* Assuming n1, n2, return an item in their intersection. */
node_ptr intersect_node(node_ptr n1, node_ptr n2)
{
  if (n1 == NIL || car(n1) == NIL) return NIL;
  if (n2 == NIL || car(n2) == NIL) return NIL;

  if ((int) car(n1) > (int) car(n2))
    return intersect_node(n1,cdr(n2));
  else if ((int) car(n1) < (int) car(n2))
    return intersect_node(cdr(n1), n2);
  else
    return car(n1);
}

node_ptr new_tlvfor(node_ptr atom, int direction, node_ptr from, node_ptr to,
                    node_ptr stmts)
{
  node_ptr init_stmt = new_node(LOCAL, atom, (direction == PLUS) ? from : to);

  node_ptr advance_stmt =
    new_node(LET, atom, new_node(direction, atom, find_NUMBER_node(1)));

  node_ptr while_cond = new_node((direction == PLUS) ? LE : GE, atom,
                                 (direction == PLUS) ? to : from);
  node_ptr while_body = append(stmts, cons(advance_stmt, NIL));
  node_ptr while_stmt = new_node(WHILE, while_cond, while_body);

  return cons(while_stmt, cons(init_stmt, NIL));
}

static atom_no = 0;

node_ptr new_temp_name(void)
{
  char strbuf[100];
  strbuf[0] = '0';

  sprintf(strbuf,"___temp%d",atom_no++);

  return string_to_atom(strbuf);
}


/* Represent a Fix statment as While.
   Rewrite
 
   Fix (expr) 
     statements...
   End

   to

   Local new_atom := strange value
   While ( expr != new_atom )
     Let new_atom := expr;
     statements...
   End
*/
node_ptr new_fix(node_ptr expr,
                 node_ptr stmts)
{

  node_ptr new_atom = new_temp_name();

  node_ptr local_stmt = new_node(LOCAL,new_atom, find_NUMBER_node(-99999));

  node_ptr let_stmt = new_node(LET,new_atom, expr);
  node_ptr while_body = cons(let_stmt,stmts);

  node_ptr while_cond = new_node(NOTEQUAL, expr, new_atom);

  node_ptr while_stmt = new_node(WHILE, while_cond, while_body);

  return cons( while_stmt, cons(local_stmt, NIL));

}
