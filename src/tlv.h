/* This file contains routines which are mostly called from
   script.c . tlv.c implements tlv-specific commands, whereas script.c
   implements a generalized scripting language. */ 


/* Initialize tlv.c */
void init_tlv(void);

/* obsolete function. */
void size_command(node_ptr var);
