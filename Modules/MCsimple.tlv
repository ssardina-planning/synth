Print "Loading MCsimple.tlv  $Revision: 4.13 $\n";

-- Model checking of specific formulas.
--
-- These routines are simpler or more effecient than
-- model checking a general formula in temporal logic.

--   check_deadlock
--
--   Invariance,  Cag
--
--   Temp_Entail_tl, Temp_Entail
--   check_react, check_react2,  check_react3

----------------------------------------------------------------------

-- Check for deadlocks.
-- Deadlocked states are those whose only successor is
-- themself.
To check_deadlock tsn := _s.cur;
  Print "\n Check for the absence of Deadlock.\n";

  restrict_rel !_id, tsn;

  -- All states without successors.
  Let deadlock := cax(FALSE);

  unrestrict tsn ;
  Let result := Cag(!deadlock, tsn);
End -- To check_deadlock;


----------------------------------------------------------------------
-- Safety
----------------------------------------------------------------------

-- Model checking safety, using frontier.
Func Cag(arg_ceg, tsn := _s.cur);
  Let bulk := !arg_ceg & pred1(1, tsn);
  Local new := bulk;

  Print "Model checking Invariance Property\n";

  -- Array which remembers the new generated frontiers.
  new bpath;
  push bpath,  bulk;

  While (new)
    -- Find new frontier.
    Let new := pred1(new, tsn) & !bulk;

    -- Remember in frontier array.
    push bpath, new;

    Let bulk := bulk | new;

    If (new & I(tsn))
      Let new := 0;
    End -- If
  End -- end while

  If (bulk & I(tsn))
    Print "\n*** Property is NOT VALID ***\n";
    Print "\nCounter-Example Follows:\n";

    -- Create counter example in new array, which acts like a stack.
    new ce;
    push ce, fsat(pop(bpath) & I(tsn), V(tsn));
    While (length(bpath))
      push ce, fsat(succ1(top(ce), tsn) & pop(bpath), V(tsn));
    End

    -- Print counter example.
    For (i in 1...length(ce))
      Print "\n---- State no. ", i," =\n", ce[i];
    End -- While (pathl)

    Return 0;
  Else
    Print "\n*** Property is VALID ***\n";

    delarr bpath;
    Return 1;
  End -- If (bulk & I(tsn))
End -- Cag

Proc Invariance(arg_inv, tsn := _s.cur);
  Let result := Cag(arg_inv, tsn);
End -- Invariance(arg_inv);

----------------------------------------------------------------------
-- RESPONSE
----------------------------------------------------------------------

Proc array_print(&arr, &running);
  For (k in 1...length(arr))
    Print "\n---- State no. ", running, " =\n", arr[k];
    Let running := running + 1;
  End
End

Func search_array(&arr, what);
  Local fulfill := 0;

  For (j in reverse 1...length(arr))
    Let fulfill := arr[j] & what;
    If (fulfill)
      Break;
    End -- If (fulfill)
  End -- While (j)

  Return fulfill;
End -- search_array(&arr,what);



Func satisfy(arg_satisfy, tsn);
  Return fsat(arg_satisfy, V(tsn));
End -- Func satisfy(arg_satisfy);



Proc Temp_Entail_tl(arg_from,arg_to, tsn := _s.cur);

  mc ltl([](arg_from -> <>(arg_to))), tsn;

End -- Temp_Entail_tl(arg_from,arg_to);

-- Version which allows justice and compassion requirement to refer to
-- the next state.
Func set_feas_simple(tsn := _s.cur);
  Local Total := T(tsn);

  Local i := 1;
  Local primed := prime(V(tsn));
  While (i <= nJ(tsn))
    Let condj[i] := Ji(i,tsn) <-> (Ji(i, tsn) forsome primed);
    If (condj[i])
      Let locj[i] := Ji(i, tsn) & Total;
    End -- If (cond[i])
    Let i := i+1;
  End -- While (i <= _jn)

  Let i := 1;
  While (i <= nC(tsn))
    Let condp[i] := Cpi(i, tsn) <-> (Cpi(i, tsn) forsome primed);
    If (condp[i])
      Let locp[i] := Cpi(i, tsn) & Total;
    End -- If (condp[i])
    Let condq[i] := Cqi(i, tsn) <-> (Cqi(i, tsn) forsome primed);
    If (condq[i])
      Let locq[i] := Cqi(i, tsn) & Total;
    End -- If (condq[i])

    Let i := i+1;
  End -- While (i <= _jn)

  Local new := 1;
  Let   len := 1;

  restrict new, TRUE, tsn;

  Fix (new)
    Let path[len] := new;
    Let len := len + 1;

    Let new := new & pred(new, tsn);
    If (nJ(tsn) > 0)
      Let i := nJ(tsn);
      While (i)
        If (condj[i])
          Let localj := (locj[i] & next(new)) forsome primed;
        Else
          Let localj := Ji(i, tsn);
        End -- If(condj[i])
        restrict new, TRUE, tsn;
        Let new := predecessors(new & localj, tsn);
        Let i := i - 1;
      End -- While (i)
    Else
      Let new := predecessors(new & ((Total & next(new)) forsome primed), tsn);
    End
    Let i := nC(tsn);
    While (i)
      If (condp[i])
        Let localp := (locp[i] & next(new)) forsome primed;
      Else
        Let localp := Cpi(i, tsn);
      End -- If(condp[i])
      If (condq[i])
        Let localq := (locq[i] & next(new)) forsome primed;
      Else
        Let localq := Cqi(i, tsn);
      End -- If(condq[i])
      restrict new, TRUE, tsn;
      Let new := (new & !localp) | predecessors(new & localq, tsn);
      Let i := i - 1;
    End -- While (i)
  End -- (new)

  unrestrict tsn;

  Let newnew := new;
  Let RR     := Total;

  Return new;
End -- set_feas_simple(trans);


-- []( p -> <>q )
Proc Temp_Entail(ass_p, ass_q, tsn := _s.cur);
  Print "Model checking Temporal Entailment for System ",tsn,"\n";

  Local reachable := reachable(tsn);

  -- Restrict transition relation such that it cannot reach q.
  restrict !ass_q, !ass_q, tsn;

  -- Find all fair cycles which do not reach q.
  Local cycles := set_feas_simple(tsn);

  -- Find all reachable p-states  from which there is
  -- a cycle that never reaches q.

  restrict !ass_q, !ass_q, tsn;
  Local pending := predecessors(cycles, tsn) & ass_p & reachable;
  unrestrict tsn;

  If (pending)
    Print "\n*** Property is NOT VALID ***\n",
          "\nCounter-Example Follows:\n";

    -- Used for keeping track of the current state in the
    -- counter example, when it is printed by array_print.
    Local   position := 1;

    -- Initialize array.
    new  prefix;

    -- Find path from initial state, to a p-state of "pending".
    Call path(I(tsn), pending, prefix, tsn);

    restrict !ass_q, !ass_q, tsn;

    -- Continue path from the p-state to the start of a fair cycle
    -- which never reaches q.
    Call path(top(prefix),cycles,prefix, tsn);

    -- Limit the transition system to not exit the cycles.
    restrict cycles, cycles, tsn ;

    -- Find state, _s, such that it belongs to a terminal cycle.
    -- This cycle is guaranteed to be fair.
    Local _s := top(prefix);
    Local temp := successors(_s, tsn) & !predecessors(_s, tsn);
    While (temp)
      Let _s := satisfy(temp, tsn);  
      Let temp := successors(_s, tsn) & !predecessors(_s, tsn);
    End -- While (temp)

    -- Extend path to reach that state.
    Call path(top(prefix), _s, prefix, tsn); 

    -- We are done finding the prefix, so print it.
    Call array_print(prefix, position);

    -- Find period.
    new period;
    push period, _s;
    push period, satisfy(succ1(_s, tsn), tsn);

    Local final := successors(_s, tsn);

    -- Thread path through all justice.
    For (i in 1...nJ(tsn))
      If (search_array(period,Ji(i, tsn)))
        -- Print"\n Period not extended\n";
        Let _dummy := 1;
      Else
        -- Print"\n extend period from ",periodsize;
        -- Let a := a;
        Call path(top(period), final & Ji(i, tsn), period, tsn);
        -- Print" to ",periodsize,"\n";
      End -- If (search_array(period,Ji(i))

    End -- For (i)

    Local necessary;

    -- Thread path through all compassion.
    For (i in 1...nC(tsn))
      -- Print"\n Treating compassion requirement ",i,"\n";
      Let necessary := final & Cpi(i, tsn);
      If (necessary)
        If (search_array(period, Cqi(i, tsn)))
          -- Print"\n Period not extended\n";
          Let _dummy := 1;
        Else
          Let goal := final & Cqi(i, tsn);
          If (goal)
            -- Print"\n extend period from ",periodsize;
            Call path(top(period), goal, period, tsn);
            -- Print" to ",periodsize,"\n";
          Else
            -- Print"\n Period not extended\n";
            Let _dummy := 1;
          End -- If (goal)
        End -- If (search_array(period, Cqi(i)))
      End -- If (necessary)

    End -- While (i)

    -- Close cycle
    Call path(top(period), _s, period, tsn);
    Local temp := pop(period);  -- Last state repeats at beggining, so omit.

    Print "\n Repeating Period\n";

    -- Print period.
    Call array_print(period, position);
    Let _reply := 0;
  Else 
    Print "\n*** Property is VALID ***\n";
    Let _reply := 1;
  End -- If (pending)

  unrestrict tsn;
End -- Temp_Entail

----------------------------------------------------------------------

Proc check_react(p,q,r, tsn := _s.cur);  -- Check reactivity property
  Print "Model checking Reactivity Property\n";

  add_J q, tsn;
  Call Temp_Entail(p,r,tsn);
  pop_J tsn;
End -- Proc check_react(p,q,r);


Proc check_react2(p,q_1,q_2,r, tsn := _s.cur);  -- Check 2-reactivity property
  Print "Model checking Reactivity(2) Property\n";

  add_J q_1, tsn;
  add_J q_2, tsn;
  Call Temp_Entail(p,r,tsn);
  pop_J tsn;
  pop_J tsn;

End -- Proc check_react2(p,q_1,q_2,r);


Proc check_react3(p,q_1,q_2,q_3,r, tsn := _s.cur);
  -- Check 3-reactivity property
  Print "Model checking Reactivity(3) Property\n";

  add_J q_1, tsn;
  add_J q_2, tsn;
  add_J q_3, tsn;
  Call Temp_Entail(p,r,tsn);
  pop_J tsn;
  pop_J tsn;
  pop_J tsn;

End -- Proc check_react3(p,q_1,q_2,q_3,r);
