-- Some utilities for compatibility with versions < 4

Print "Loading compat.tlv $Revision: 1.5 $\n";

-- To init_compat;
--   Print "Initializing compatibility module. This may take a while..\n";
--   Let total := T( );
--   Print "Compatibility module initialization complete.\n";
-- End

-- This is equivalent to the old "successors" function.
Func reachable_states(set, trans);
  Local closure := set;
  Local front := set;

  Fix (closure)
    Let front := succ(trans, front) & !closure;
    Let closure := closure | front;
  End
  Return closure;
End
