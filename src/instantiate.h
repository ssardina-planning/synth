  
node_ptr instantiation(node_ptr parse_tree);

/* Expand "for" constructor loops. The "tree" parameter
   is a node with type "FOR".  */
node_ptr expand_for_once(node_ptr tree, node_ptr context);
