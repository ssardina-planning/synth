/* Main function which translates the parse_tree (which is
   accessed as an extern variable, to a set of bdds, which
   are exported as dynmaic variables. Actually, I think most
   other function except this one should be moved to other
   (new) source files. */

void smv2fts(void);


/* Instantiate one variable. This is used in tlv.c, in order
   to create new program variables via tlvbasic */
void inst_one_variable(
   node_ptr name, node_ptr type,node_ptr context);


/* Function which read/write the order of variables.
   This affects the representation in bdds */
node_ptr read_variable_list_from_file(char *fname);
void write_var_list_to_file(node_ptr variables, char *fname);

