--
-- mctls - model checking CTL_* formulas  (ctls)
--

-- Uses the algorithm from:
-- Yonit Ketsen, Amir Pnueli, Li-on Raviv, Elad Shahar, 
--    "Model checking with strong fairness".

-- Does not print counter example.

Print "Loading MCTLS.tlv $Revision: 4.1 $\n";


----------------------------------------------------------------------
-- Internal function which is used to implement Sat_EL and Sat_AL.

-- Return all states of system for which there exists
-- a path such that the LTL formula p holds.
Func SAT_aux('p, tsn);

  --Print "SAT_aux root:", 'root(p), "\n";

  -- Like line 1 of SAT-Ef.
  --
  -- The value "1" of the second parameter indicates using
  -- weak initial condition.
  Local tester_tsn := create_tester(p, 1);

  -- Like line 2 of SAT-Ef.  
  Local comp := sync(tsn, tester_tsn);

  -- Like line 3 of SAT-Ef.
  Local result := chi(p) & Feasible( comp);

  -- Like line 4 of SAT-Ef
  -- Note that "tester_aux_vars" is the auxiliary variables of
  -- *all* testers. We only want those which belong to the tester
  -- we just created.
  Let result := 
      result forsome set_intersect(tester_aux_vars, V(tester_tsn));

  delete_last_ts;  -- Cleanup.
  delete_last_ts;

  Return result;

End


----------------------------------------------------------------------
-- The following two procedures implement SAT_Ef and SAT_Af from
-- the article. However, instead of returning a value, they store
-- it in a hash.

To Sat_EL 'p, tsn;
  Local s := SAT_aux(p, tsn);
  insert_hash _EL, p, s;
End

To Sat_AL 'p, tsn;
  Local s := ! SAT_aux(addneg(p), tsn);
  insert_hash _AL, p, s;
End


----------------------------------------------------------------------
-- The following two functions assist in implementing line 5 of
-- VALID_CTL* . They return the bdd value which is to be replaced
-- instead of the corresponding basic formula.

Func EL('p);

  -- Find set associated with formula p.
  Local val := value_of_hash(_EL, p);

  If ( success_hash(_EL) )
    Return val;
  Else
    Print "Value ", 'p, "not found in hash _EL\n";
    Return 0;
  End
End


Func AL('p);

  -- Find set associated with formula p.
  Local val := value_of_hash(_AL, p);

  If ( success_hash(_AL) )
    Return val;
  Else
    Print "Value ", 'p, "not found in hash _AL\n";
    Return 0;
  End
End

----------------------------------------------------------------------
-- Implements lines 1-6 of algorithm VALID-CTL*.
Proc expand_EL_AL('p, tsn);

  If (mcverbose) Print "expand_EL_AL root:",'root(p),"\n"; End

  -- Go down the tree, recursion, DFS.

  Case (root(p))

   "func":
        -- BEWARE: 
        -- op(1,p) is the name of the function ( "EL" or "AL" ).
        -- op(2,p) is the list of arguments, but
        -- We only want the first argument, which is op(1,op(2,p))
        Case (op(1,p))
          "EL", "AL" : expand_EL_AL op(1,op(2,p)), tsn; 
        End

        -- Evaluate set of reachable states satisfying basic formula.
        Case (op(1,p))
           "EL": Sat_EL  op(1,op(2,p)), tsn;
           "AL": Sat_AL  op(1,op(2,p)), tsn;
        End

   "!",
   -- Unary temporal operators.
   "()","<>","[]","(~)","(_)","<_>","[_]":
        expand_EL_AL  op(1,p), tsn;

   -- Boolean temporaal operators.
   "&", "|", "->", "<->",
   "Since", "Until", "Awaits", "Backto": 
        expand_EL_AL  op(1,p), tsn;
        expand_EL_AL  op(2,p), tsn;
  End 
  
End

----------------------------------------------------------------------
-- This is the algorithm VALID-CTL* from the article.

Func valid_ctlS('p, tsn);

  -- Initialize top of EL and AL arrays.
  new_hash _EL;
  new_hash _AL;

  -- Implements lines 1-6 of VALID-CTL*
  --
  -- Recursively go down the expression, DFS, and evaluate EL/AL
  -- which do not have an EL/AL nested within them, i.e. "basic
  -- state formulas".
  -- The results of these evaluations are stored in the
  -- hash tables _EL, _AL .

  Call expand_EL_AL(p, tsn);
  
  -- Line 7

  -- This line evaluates also evaluates the parse tree, p, to a bdd,
  -- treating AL and EL as names of functions, so
  -- the functions AL and EL are invoked. They return the
  -- values which are stored in the hash tables _AL, _EL,
  -- which contain the correct evalaution for each formula.

  Local result := I(tsn) -> p ;

  delhash(_EL);  
  delhash(_AL);

  Return result;
End


----------------------------------------------------------------------
--
-- Model check ctl-Star.
--
To mctls 'p, tsn := _s.cur;

  Print "Model checking...\n"; 
  Local result := valid_ctlS(p, tsn);
  Let _status := is_true(result) ? 1 : 0;

  If (_status)
    Print "\n*** Property is VALID ***\n";
  Else
    Print "\n*** Property is NOT VALID ***\n";
  End

End
