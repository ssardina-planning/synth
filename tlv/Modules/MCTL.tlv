-- This file provides Model checking of LTL formula.
-- It requires Util.tlv in order to run.
-- The temporal formula are represented symbolically.
--
----------------------------------------------------------------------
-- The main interesting routines for EXTERNAL usage are:
--
-- Check validity of tl formula:
--    valid ltl( tl_formula );
--
-- Model check using a temporal formula:
--    mc ltl( tl_formula );
--
-- Model check sequential program ( halted executions are extended
-- indefinitely by adding the idle transition )
--
--    mcseq ltl( tl_formula);
--
-- Model check using a tester which is provided by the user in the
--
--    mc_tester tsn;
--
----------------------------------------------------------------------
-- Main internal routines:
--
-- Feasible - algorithm FEASIBLE.
--
-- verify;        - verify property, with witness.
--    Checks that the composition is feasible.
--    The composition is created with one of the compose_... routines.
----------------------------------------------------------------------

-- When set to 1 prints timing information in procedure "verify".
Let mcdebug := 0;

-- When set to 1 prints messages in procedures "mc" and "create_tester"
-- (note that create_tester is also called from "valid".
Let mcverbose := 0;

----------------------------------------------------------------------

Print "Loading MCTL.tlv $Revision: 4.11 $\n";



-- Eliminate states from scc which have no predecessors within scc.
-- scc is supposed to be a strongly connected component, however, it
-- also contains chains of states which lead to the scc, but are not
-- in it. This procedure eliminates these chains.
Func elim_pred_chains(scc,tsn);
  Fix (scc)
      Let scc := scc & succ1(scc, tsn);
  End
  Return scc;
End


-- Eliminate states from scc which have no successors within scc.
-- scc is supposed to be a strongly connected component, however, it
-- also contains chains of states which exit the scc, but are not
-- in it. This procedure eliminates these chains.
Func elim_succ_chains(scc,tsn);
  Fix (scc)
      Let scc := scc & pred1(scc, tsn);
  End
  Return scc;
End

----------------------------------------------------------------------

-- Algorithm Feasible(tsn).
--
-- Returns a set of states which induce a graph which contains all
-- the fair SCS's reachable from an initial state.
--
-- This is essentially algorithm "FEASIBLE",
-- from the article: 
-- Yonit Ketsen, Amir Pnueli, Li-on Raviv, Elad Shahar, 
--    "Model checking with strong fairness".
--
-- The line numbers are the line numbers of that algorithm.
-- Read the article for further details.

Func Feasible(tsn);
  Local nj := nJ(tsn);
  Local nc := nC(tsn);
  Local temp;
  Local localj;
  Local localcp;
  Local localcj;

  -- Line 2
  Local new := successors(I(tsn), tsn);
  Local reachable := new;

  -- Determine whether fairness conditions refer to primed variables.
  -- If so, they are treated differently.

  Local primed := prime(V(tsn));
  For (i in 1...nj)
    Local has_primed_j[i] :=
      !is_true(Ji(i, tsn) <-> (Ji(i, tsn) forsome primed));
  End
  For (i in 1...nc)
    Local has_primed_cp[i] :=
      !is_true(Cpi(i, tsn) <-> (Cpi(i, tsn) forsome primed));
    Local has_primed_cq[i] :=
      !is_true(Cqi(i, tsn) <-> (Cqi(i, tsn) forsome primed));
  End

  -- Line 3
  restrict new, TRUE,  tsn;

  -- Lines 4-11
  Fix (new)
    -- Lines 6-7 
    -- Eliminate states from new which have no succeessors within new.
    Let new := elim_succ_chains(new, tsn);
    restrict new, TRUE, tsn;

    -- Lines 8-9
    -- Ensure fulfillment of justice requirements.
    -- Remove from "new" all states which are not R^*-successors
    -- of some justice state.
    For (i in 1...nj)
      If (has_primed_j[i])
        Let localj := has_successors_to(Ji(i,tsn), new, tsn);
      Else
        Let localj := Ji(i,tsn);
      End
      Let new := predecessors(new & localj, tsn);
      restrict new, TRUE,  tsn;
    End 
    -- Lines 10-11
    -- Ensure fulfillment of campassion requirements:
    -- Remove from "new" all p-states which are not R^*-successors
    -- of some q-state for some (p,q) \in C.
    For (i in 1...nc)
      If (has_primed_cp[i])
        Let localcp := has_successors_to( Cpi(i,tsn), new, tsn);
      Else
        Let localcp := Cpi(i,tsn);
      End

      If (has_primed_cq[i])
        Let localcq := has_successors_to(Cqi(i,tsn), new, tsn);
      Else
        Let localcq := Cqi(i,tsn);
      End

      Let new := (new & ! localcp) | predecessors(new & localcq, tsn);
      restrict new, TRUE, tsn;
    End 
  End 

  unrestrict tsn; 
  
  -- Line 12
  restrict reachable, TRUE, tsn;
  Let new := predecessors(new, tsn);

  unrestrict tsn; 
  
  -- Line 13 
  Return new;
End -- Feasible

-- Print temporal formulas.
To prtl _t;
  Local cur_column := 0;
  Local strl;
  Local print_type;

  For (i in 1...x_top)

    -- Determine how it should be printed, if at all (positive or negative)
    If (x[i] & _t)
      If (!x[i] & _t)
        Let print_type := 2;
      Else
        Let print_type := 0; -- positive. (its counter intuitive, but useful)
      End
    Else
      Let print_type := 1; -- negative
    End

    -- Print the string. ( dont if print_type = 2)
    If (print_type in {0,1})

      Let strl := strlen(xs[i]) + print_type * 5;
 
      If (strl + cur_column + 3 > 80)
        Print "\n";
        Let cur_column := 0;
      Else
        If (cur_column > 0)
          Print ",  ";
          Let cur_column := cur_column + 3;
        End
      End

      If (print_type)
        Print "!( ",'xs[i]," )";   
      Else
        Print 'xs[i];
      End

      Let cur_column := cur_column + strl;

    End

  End

  If (cur_column)
    Print "\n";
  End
End

-- Print array "a", of length _len. If _print_tester_vars then
-- the tester vars are also printed. In printing the states add "add" to
-- the state number.
-- If _print_property_val is set then the formula for which the tester
-- was created is also printed in each state (it is only printed if its
-- principle operator is not temporal, otherwise it is already printed
-- as a tester variable.
-- 
To print_array &an_array, _print_tester_vars, _print_property_val, _add, tsn;
  Local _kk;
  For (_k in 1...an_array[0])
    Print "\n---- State no. ", _k + _add, " =\n";

    -- Print propositional variables.
    Let _kk := an_array[_k] forsome tester_aux_vars;
    If (_kk != 1)
      Print _kk;
    End

    -- Print values of tester variables (which all have a temporal operator as 
    -- the principle one.
    If (_print_tester_vars)
      Run prtl an_array[_k];
    End

    -- Print value of the property (note that if it also has a temporal
    -- operator as the principle one then it was already printed).
    If (_print_property_val & exist(_s[tsn].p))
      If (!_print_tester_vars  | !principle_temporal(_s[tsn].p))
        Local chi_result := chi(_s[tsn].p);
        If (chi_result & an_array[_k])
          Print '_s[tsn].p,"\n";
        Else
          Print "!( ", '_s[tsn].p, ")\n";
        End
      End
    End
  End
End

-- Find a bad cycle in system tsn and put it in array "period".
-- The cycle starts from state "s" which is a state in a fair
-- MSCS. The transition system should be retricted such that
-- it is not possible to exit the MSCS.
--To bad_cycle s, & period, tsn;
--End

-- Print counter example.  
--
-- This is essentially algorithm "Witness",
-- from the article:
-- Yonit Ketsen, Amir Pnueli, Li-on Raviv, Elad Shahar,
--    "Model checking with strong fairness".
-- The line numbers are the line numbers of that algorithm.
-- Read the article for further details.
To print_witness _print_tester_vars, final, tsn;
  Local temp;
  Local fulfill;

  -- Lines 1-2 are handled by the caller. ("verify")

  -- Line 3
  restrict final,final, tsn;

  If (mcverbose) Print "Calculating terminal maximal SCS\n"; End

  -- Line 4
  Local s := fsat(final,V(tsn));

  -- Lines 5-6
  While (1)
    Let temp := successors(s, tsn) & !predecessors(s, tsn);
    If (temp)
      Let s := fsat(temp, V(tsn));
    Else
      Break;
    End
  End

  -- Line 7:   Compute MSCS containing s.
  Local final := successors(s, tsn);

  -- Line 9
  -- Find prefix - shortest path from initial state to subgraph final.
  unrestrict tsn;
  new _prefix; -- Initialize counter example array.
  Call path(I(tsn),final, _prefix, tsn);

  ------ Calculate "_period".

  -- Line 8:  This has to come after line 9, because the way
  --          TS.tlv implements restriction.
  restrict final, final, tsn;

  -- Line 10
  push _period, top(_prefix);

  -- Since the last item of the prefix is the first item of
  -- the period we dont need to print the last item of the prefix.
  Let temp := pop(_prefix);

  -- Thread a path through all justice requirements.
  If (mcverbose)
    Print "Assuring period is just\n";
  End

  -- Lines 11-13
  For (i in 1...nJ(tsn))
    -- Line 12, check if j[i] already satisfied
    Let fulfill := 0;
    For (j in 1...length(_period))
      Let fulfill := _period[j] &&& Ji(i,tsn);
      If (fulfill)
        Break;
      End
    End

    -- Line 13
    If (is_false(fulfill))
      Call path(top(_period), final & Ji(i,tsn), _period, tsn);
    End
  End

  -- Thread through all compassion requirements
  If (mcverbose)
    Print "Assuring period is compassionate\n";
  End

  -- Lines 14-16
  For (i in 1... nC(tsn))
    If (final &&& Cpi(i, tsn) )
      -- check if C requirment i is already satisfied
      Let fulfill := 0;
      For (j in 1...length(_period))
        Let fulfill := _period[j] &&& Cqi(i, tsn);
        If (fulfill)
          Break;
        End 
      End 

      If ( is_false(fulfill) )
         -- line 16
        Call path(top(_period), final & Cqi(i, tsn), _period, tsn);
      End
    End

  End -- While (i)

  --
  -- Close cycle
  --

  -- A period of length 1 may be fair, but it might be the case that
  -- _period[1] is not a successor of itself. The routine path
  -- will add nothing.  To solve this
  -- case we add another state to _period, now it will be OK since
  -- _period[1] and _period[n] will not be equal.

  -- Line 17, but modified
  If (_period[1] & top(_period))
    -- The first and last states are already equal, so we do not
    -- need to extend them to complete a cycle, unless period is
    -- a degenerate case of length = 1, which is not a successor of self.
    If (length(_period) = 1)
      -- Check if _period[1] is a successor of itself.
      If (is_false(_period[1] & succ1(_period[1],tsn)) )
        -- _period[1] is not a successor of itself: Add state to _period.
        push _period, fsat(succ1(_period[1], tsn), V(tsn));

        -- Close cycle.
        Call path(top(_period), _period[1], _period, tsn);
      End
    End
  Else
    Call path(top(_period), _period[1], _period, tsn);
  End

  -- There is no need to have the last state of the period
  -- in the counterexample since it already appears in _period[1]
  If (_period[0] > 1)
    Let temp := pop(_period);
  End

  If (mcdebug)     Chktime;  End
  If (mcverbose)   Print "Copy period and prefix to ce\n";  End

  -- Copy _prefix and _period to ce.
  copy ce, _prefix;
  append ce, _period;

  -- Strip auxiliary variables introduced by tester.
  If (is_false(_print_tester_vars))
    For (i in 1...length(ce))
      Let ce[i] := ce[i] forsome tester_aux_vars;
    End
  End

  Let period_start := length(_prefix) + 1;

  --
  -- Printing counter example.
  --
  print_array ce, _print_tester_vars, 0, 0, tsn;
  Print "\nLoop back to state ", period_start, "\n\n";
  Print "The counter example is stored in array ce[1..", length(ce), "] .\n";

  -- Cleanup.
  unrestrict tsn;
  delarr _prefix;
  delarr _period;
End -- print_witness

-- Verify property with witness.
-- Outputs global variable of _status which is 1 when successful.
To verify initial_conjunct, _print_tester_vars, tsn;
  If (mcdebug) Settime; End

  -- "final" contains all the fair SCS's reachable from an initial state.
  set_I I(tsn) & initial_conjunct, tsn;
  Local final := Feasible(tsn);

  If (mcdebug) Chktime; End

  If (final & I(tsn) & initial_conjunct)
    Let _status := 0;
    Print "\n*** Property is NOT VALID ***\n\nCounter-Example Follows:\n";
    print_witness _print_tester_vars, final, tsn;
  Else
    Let _status := 1;
    Print "\n*** Property is VALID ***\n";
  End -- If (final)
End -- verify

----------------------------------------------------------------------
-- For EXTERNAL usage.
----------------------------------------------------------------------

--
-- Check that formula is valid
--
Proc valid ('_p, tsn := _s.cur);
  -- Create transition system of tester.
  Let 'notp := addneg(_p);
  Local tsn := create_tester(notp, 1);

  -- Mc with printout of tester vars in counterexample.
  Run verify !chi(_p), 1, tsn;

  -- Delete tester TSN and composition TSN
  delete_last_ts;
End -- valid

--
-- mc - model check an ltl formula
--
-- For example:
--   mc ltl([] !(at_l3 & at_m3));
--
-- or
--
--   Let 'k := ltl([] !(at_l3 & at_m3));
--   mc k;  -- To verify k.

Proc mc ('_p, tsn := _s.cur);
  If (is_ctl(_p))
    -- Do ctl model checking.
    mcctl _p, tsn;
  Else
    -- Create transition system of tester.
    Let 'notp := addneg(_p);
    Local tester_ts := create_tester(notp, 1);

    -- Create synchronous COMPosition of tester with transition relation.
    If (mcverbose) Print "Composing tester...\n"; End
    Local comp := sync(tsn, tester_ts);

    -- Mc without printout of tester vars in counterexample.
    verify !chi(_p), 0, comp;

    -- Delete both the tester and the composition.
    delete_last_ts;
    delete_last_ts;
  End
End


-- LTL model checking for sequential programs.
To mcseq 'p;

  -- Create transition system of tester.
  Let 'notp := addneg(_p);
  Local tester_ts := create_tester(notp, 1);

  -- We use a copy of the transition system since we are modifying
  -- the system with "add_idle", and we want to keep the original system
  -- intact.
  Local ts_copy := copy_ts();

  -- Since this is a sequential program, probably written
  -- in spl, there is a good chance that the program terminates,
  -- resulting in finite compuatations. So we add idling transitions
  -- in order to make the computations infinite. Otherwise, model
  -- checking will not work.
  add_idle(ts_copy);

  -- Create synchronous COMPosition of tester with transition relation.
  If (mcverbose) Print "Composing tester...\n"; End
  Local comp := sync(ts_copy, tester_ts);

  verify !chi(p), 0, comp; -- Mc without printout of tester vars in counterexample.

  -- Delete the copy, the tester and the composition.
  delete_last_ts;
  delete_last_ts;
  delete_last_ts;
End


--
-- mc - model check using a tester that the user provided.
--
To mc_tester tsn;

  Local temp_I := I(tsn);
  set_I TRUE, tsn;

  Local comp := sync(_s.cur, tsn);

  set_I temp_I, tsn;

  Run verify temp_I, 0, comp; -- Model check ( In old version, since tester._vars = 1,
                     -- then the variables
                     -- of the tester are printed as well, in contrast to "mc").
 
  delete_last_ts;
End
