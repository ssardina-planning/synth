-- The routines used for creating/verifying testers are:
--
-- 1) create_aux_vars, create_aux_vars_internal :
--      Create auxiliary variables which correspond to tl subformula
--      with principal temporal operator
--
-- 2) chi : Function which translates a tl subformula to corresponding bdd.
--
-- 3) create_tester : Given an ltl formula, creates corresponding tester.
--
----------------------------------------------------------------------

Print "Loading TESTER.tlv $Revision: 4.5 $\n";

-- This is the set of auxiliary variables.
Let tester_aux_vars := 1;

-- The size of the arrays x, xs, x_depth.
Let x_allocated := 0;

-- The size of x which is reserved for auxiliary variables for the ltl
-- formulas which are defined in smv files.
Let x_reserved := 0;


-- Polarity is a number between -1..1, where -1 is negative polarity,
-- +1 is positive polarity, and 0 is both polarities.
Func reverse_polarity(polarity);
    Return -1 * polarity;
End

-- Return true if polarity either positive, or both polarities.
Func is_positive_polarity(polarity);
    Return polarity > -1;
End

-- Return true if polarity either negative, or both polarities.
Func is_negative_polarity(polarity);
    Return polarity < 1;
End

----------------------------------------------------------------------
-- This recursive function creates boolean variables which correspond
-- to subformula of the parameter, __p, which have a temporal operator
-- as their principal operator.
--
-- The new variables are created in the array "x".
-- The parse tree of the corresponding subformula is stored in the array "xs" .
--
-- Slso calculates the depth of nesting of temporal
-- formulas of each subformula of the closure and returns it.
-- The temporal depth is stored in the array "x_depth".
Func create_aux_vars_internal('__p, polarity, use_ltl_defs_from_sys, tsn);
  Local temporal := 0;
  Local foundexp := 0;

  Local polarity1 := polarity;
  Local polarity2 := polarity;

  If (mcdebug)
    Print "create_vars_internal: ", '__p, "\n";
  End

  Case (root(__p))
    "!", "->":
      If (mcdebug)
        Print "root is ! or ->\n";
      End
      Let polarity1 := reverse_polarity(polarity1);
    "<->":
      If (mcdebug)
        Print "root is <->\n";
      End
      -- Set polarity to "both".
      Let polarity1 := 0;
      Let polarity2 := 0;
    "ident":
      If (mcdebug)
        Print "root is ident\n";
      End
      -- Collect propositional variables that the formula __p refers to.
      add_V support(__p), tsn;
      -- Print "create_aux_vars: Added new var -> ", V(tsn), "\n";
    "func":
      Return 0;

    -- Unary temporal operators.
    "()","<>","[]","(~)","(_)","<_>","[_]",

    -- Binary temporal operators.
    "Since", "Until", "Awaits", "Backto":
      If (mcdebug)
        Print "root is temporal\n";
      End
      Let temporal := 1;

      -- Check that a variable hasn't already been created for this
      -- formula. If so, exit this routine.

      For (i in x_reserved + 1...x_top)
        If (xs[i] == __p)
          If (_x_polarity[i] != polarity)
            Let _x_polarity[i] := 0 ; -- Set polarity to both.
          End
          Return x_depth[i];
        End
      End

      -- We are going to add a new auxiliary variable, so increase
      -- x_top to make room for the new variable.
      Let x_top := x_top + 1;
      Let _x_polarity[x_top] := polarity;

      -- If use_ltl_defs_from_sys, then search the array of _ltl_exp to see
      -- if there is an equivalent expression. If there is, then we
      -- are not supposed to generate a new auxiliary variable. Instead
      -- we have to use the variable with the name specified in _ltl_var.
      -- We do this by making x[i] be a dynamic variable which contains
      -- a parse tree. The value will be the name of the variable which
      -- has aleady been defined in the smv file.
      If (use_ltl_defs_from_sys)
        For (i in 1..._ltl_n[use_ltl_defs_from_sys])
          If (_ltl_exp[use_ltl_defs_from_sys][i] == __p)
            Let ' x[x_top] := _ltl_var[use_ltl_defs_from_sys][i];
            Let foundexp := TRUE;
            Break;
          End
        End
      End

      -- Create variable for subformula with principle temporal operator.
      If (x_top > x_allocated)
        If (!foundexp)
          x[x_top] : boolean;
        End
        Let x_allocated := x_top;
      End

      Let tester_aux_vars := set_union(tester_aux_vars, support(x[x_top]));

      -- Add new variable to set V.
      add_V support(x[x_top]), tsn;
      -- Print "create_aux_vars: Added new var -> ", V(tsn), "\n";

      -- Save corresponding symbolic representation of the subformula.
      Let ' xs[x_top] := __p;
  End

  If (mcdebug)
    Print "after case\n";
  End

  If (ops(__p) = 0)
    If (mcdebug)
      Print "Returning 0\n";
    End
    Return 0;
  Else
    If (mcdebug)
      Print "Not returning 0\n";
    End

    Local remember_x_top := x_top;

    -- Recursive calls for 1 or 2 arguments. The variable "max_result"
    -- will contain the maximal temporal depth of the two arguments.
    Local max_result :=
      create_aux_vars_internal(op(1, __p), polarity1, use_ltl_defs_from_sys,
                               tsn);
    If (ops(__p) > 1)
      Local result :=
        create_aux_vars_internal(op(2, __p), polarity2, use_ltl_defs_from_sys,
                                 tsn);
      If (result > max_result)
        Let max_result := result;
      End
    End
    If (temporal)
      Let x_depth[remember_x_top] := max_result + 1;
    End
    Return max_result + temporal;
  End
End

-- Calls the recursive function create_aux_vars_internal(__p1).
-- The temporal depth of the entire formula is in stored in tester.tl_depth .
Proc create_aux_vars('__p1, use_ltl_defs_from_sys, tsn);
  Let x_top := x_reserved;
  Let _s[tsn].tl_depth :=
    create_aux_vars_internal(__p1, +1, use_ltl_defs_from_sys, tsn);
End

----------------------------------------------------------------------
-- The mapping CHI: maps a parse tree of a temporal subformula to its
-- corresponding bdd
Func chi('__pc);
  Case (root(__pc))
    -- Basic state formulas.
    "func",
    "ident", "number", "TRUE","FALSE",
    "next",
    "=", "!=", "<", ">", "<=", ">=", "in", "notin", "union",
    "+", "-", "*","/" :
        Return __pc;

    -- Unary operators
    "!"     : Return ! chi(op(1,__pc));

    -- Boolean operators
    "|"     : Return chi(op(1,__pc)) | chi(op(2,__pc));
    "&"     : Return chi(op(1,__pc)) & chi(op(2,__pc));
    "->"    : Return chi(op(1,__pc)) -> chi(op(2,__pc));
    "<->"   : Return chi(op(1,__pc)) <-> chi(op(2,__pc));

   -- Temporal operators.
   "()","<>","[]","(~)","(_)","<_>","[_]",
   "Since", "Until", "Awaits", "Backto":

      Local j := x_top;
      While (j - x_reserved)
         If (xs[j] == __pc)
           Return x[j];
         End
         Let j := j - 1;
      End

      Print "Variable not found in chi\n";
  End
End


----------------------------------------------------------------------
--
-- Given a temporal formula, create the corresponding tester.
--
Func create_tester('_property, weak, use_ltl_defs_from_sys := 0);
  If (mcverbose) Print "Creating tester...\n"; End

  Local tsn := new_ts();
  Let '_s[tsn].p := _property;  -- Remember the original expression.

  -- Create auxiliary variables. Calculate tester_aux_vars,
  -- _s[tsn].tl_depth .
  If (mcverbose) Print "Creating auxiliary variables...\n"; End
  Run create_aux_vars _property, use_ltl_defs_from_sys, tsn;

  --
  -- Calculate initial condition, transition relation and fairness conditions.
  --
  If (mcverbose) Print "Calculating components of tester...\n"; End

  Local ii := TRUE;
  Local tt := 1;

  Local _old_jn;

  -- Loop over x and xs arrays. This loops over all temporal subformulas of 
  -- the formula we are trying to check. The transition and fairness condition
  -- are calculated.
  Local j := x_top;
  While (j - x_reserved)

    Let _old_jn := _s[tsn].jn;

    Let '_p9 := op(1,xs[j]);
    Let '_q9 := op(2,xs[j]);

    Case (root(xs[j]))
      "()": Let tt := tt & ( x[j] <-> prime(chi(_p9)) );

      "<>": Let tt := tt &  ( x[j] <-> ( chi(_p9) | next(x[j]) ) );
 --            If ( is_positive_polarity(_x_polarity[j]) )
                  add_J  chi(_p9) | ! x[j],  tsn;
 --            End

      "[]": Let tt := tt & ( x[j] <-> ( chi(_p9) & next(x[j]) ));
 --            If ( is_negative_polarity(_x_polarity[j]) )
                  add_J  ! chi(_p9) | x[j],  tsn;
 --            End

      "(_)": Let ii := ii & ! x[j];
             Let tt := tt & ( next(x[j]) <-> chi(_p9) );

      "(~)": Let ii := ii & x[j];
             Let tt := tt & ( next(x[j]) <-> chi(_p9) );

      "<_>": Let ii := ii & ( x[j] <-> chi(_p9) );
             Let tt := tt & ( next(x[j]) <-> ( prime(chi(_p9)) | x[j] ));

      "[_]": Let ii := ii & ( x[j] <-> chi(_p9) );
             Let tt := tt & ( next(x[j]) <-> ( prime(chi(_p9)) & x[j] ));

      "Until":
          Let tt := tt &
               ( x[j] <->
                 ( chi(_q9)  |  (chi(_p9) & next(x[j])) )
               ) ;

 --         If ( is_positive_polarity(_x_polarity[j]) )
               add_J  chi(_q9) | ! x[j],  tsn;
 --         End

      "Awaits" :
          Let tt := tt &
               ( x[j] <->
                 ( chi(_q9)  |  (chi(_p9) & next(x[j])) )
               ) ;

 --         If ( is_negative_polarity(_x_polarity[j]) )
               add_J ( !chi(_p9) & !chi(_q9) ) | x[j],  tsn;
 --         End

      "Since":
          Let ii := ii & ( x[j] <-> chi(_q9) );
          Let tt := tt &
              ( next(x[j]) <->
                (  prime(chi(_q9))  |  (prime(chi(_p9)) & x[j])  )
              ) ;

      "Backto" :
          Let ii := ii & ( x[j] <-> ( chi(_p9) | chi(_q9) ) );
          Let tt := tt &
               ( next(x[j]) <->
                 (  prime(chi(_q9))  |  (prime(chi(_p9)) & x[j])  )
               ) ;
    End

    If (_old_jn = _s[tsn].jn)
      -- The subformula associated with x[j] has no related justice condition.
      Let x_just[j] := 0;
    Else
      Let x_just[j] := nJ(tsn);
    End

    Let j := j - 1;
  End

  -- Weak evaluation (used in TLSIMU and in MCTLS) does not force
  -- initial condition to contain negation of formula (which is used
  -- to show validity by showing that negation of formula isn't satisfiable).
  If (! weak)
    Let ii := ii & ! chi(_property);
  End

  set_I ii, tsn ;
  add_disjunct_T tt, tsn;

  If (use_ltl_defs_from_sys)
    Let x_reserved := x_top;
  End

  Return tsn;
End


----------------------------------------------------------------------
-- Returns transition associated with last state of bounded path.
Func bounded_semantics(tsn, '_property);

  Local no_t := 1;

  -- Loop over x and xs arrays. This loops over all temporal subformulas of 
  -- the formula we are trying to check. The transition and fairness condition
  -- are calculated.
  For (j in reverse x_reserved+1...x_top)
    Let '_p9 := op(1,xs[j]);
    Let '_q9 := op(2,xs[j]);

    Case (root(xs[j]))
      "()", "[]":         Let no_t := no_t & !x[j];
      "<>":               Let no_t := no_t & ( x[j] <-> chi(_p9) );
      "Until", "Awaits":  Let no_t := no_t & ( x[j] <-> chi(_q9) );
    End
  End

  Return no_t;
End
