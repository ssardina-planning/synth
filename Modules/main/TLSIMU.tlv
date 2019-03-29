-- This file has routines which copy the current simulation and
-- annotate it with the evaluation of temporal formulas given in a file.
--
--     To fsimtl '_p;  -- _p contians only future temporal operators.
--                        The model can be looped
--
--     To simtl '_p;   -- _p can contain both future and past operators
--                         but future operators are interpreted under bounded
--                         sematics. The model cannot be looped.
--
-- Which copies a simulation and evaluates the temporal subformulas.


-- This file is supposed to use MCTL and SIMULATE to create a simulation
-- for which we evaluate a temporal formula on some locations.

-- Copy simu to simt.
To copysimu;
  copy simt, simu;
  Let simt_loop := simu_loop;
End


-- Propogate values to step _step from its successor in the model.
To propogate _step, tester_id;

  If (_step = simt[0])
    If ( simt_loop )
      Local temp := simt[_step] & T(tester_id) & prime(simt[simt_loop]);
    Else
      -- tester.no_t is what should be conjuncted to a step in order
      -- to obtain bounded sematics with no loop. It is only used here.
      -- It falsifies \G, \X .
      Local temp := simt[_step] & _s[tester_id].no_t;
    End   
  Else
    Local temp := simt[_step] & T(tester_id) & prime(simt[_step + 1]);
  End

  Let simt[_step] := temp forsome prime( set_union( V(tester_id), V() ) );
  
End


-- Propogate values to step _step from its successor in the model.
To propogate_back _step, tester_id;

  If (_step > 1)
    Local temp := simt[_step - 1] & T(tester_id) & prime(simt[_step]);
    Let simt[_step] := unprime(temp forsome 
                               set_union( V(tester_id), V() ) ) ;  
  End

End


To fillsimt onlyfuture, tester_id;

  -- We will handle variables according to their temporal depth with
  -- subforulas with low depth, first. 
  Local _j;
  Local chi_just;
  Local chi_found;

  If (!onlyfuture)
    Let simt[1] := simt[1] & I(tester_id);
  End

  For (_dep in 1..._s[tester_id].tl_depth)

    -- Handle justice conditions.
    If ( onlyfuture & (simt_loop > 0) )

      For (_k in reverse 1...x_top)

        If (x_depth[_k] = _dep)

          -- If there is a loop, handle justice conditions if exist.
          If ( x_just[_k] > 0)
            Let chi_just := Ji(x_just[_k], tester_id) forall x[_k]; 
            Let xvar_just := Ji(x_just[_k], tester_id) forall support(chi_just);

            -- Check: if all period is !chi_just we can add a xvar_just state to 
            -- the period.
            Let chi_found := 0;
            Let _j := simt[0];
            While (_j - simt_loop + 1)
              If (simt[_j] & chi_just)
                Let chi_found := 1;
                Break;
              End
              Let _j := _j - 1;
            End

            If (!chi_found)
              -- Add to the last state (it must be in the period).
              Let simt[simt[0]] := simt[simt[0]] & xvar_just;
            End
          End

        End
      End

    End

    -- Propogate values for this level ( for each depth we have to do this once ).

    -- For a loop we have to do an additional sweep (do we?).
    If (simt_loop)
      Let _j := simt[0];
      While (_j - simt_loop + 1)
        Run propogate _j, tester_id;
        Let _j := _j - 1;
      End
    End

    -- Do the normal sweep
    For (_j in reverse 1...simt[0])
      Run propogate _j, tester_id;
    End


    If (!onlyfuture)
      For (_j in 2...simt[0])
        Run propogate_back _j, tester_id;
      End
    End
  End

End


To simtl_internal '_p, onlyfuture;

  If (length(simu) = 0)
    Print "You must first create a simulation/model\n";
    Return;
  End

  -- Copy simulation to another array (simt).
  Run copysimu;

  -- Generate tester with weak initial condition.
  Local tester := create_tester(_p, 1, 0);
  Let _s[tester].no_t := bounded_semantics(tester, _p);

  -- Fill simt,
  -- until all steps of the tl-simulation have assignments for all
  -- tester variables.
  Run fillsimt onlyfuture, tester;

  -- Print the tl simulation.
  Run print_array simt,1,1,0, tester;

  If (simt_loop)
    Print "\nLoop back to state ",simt_loop,"\n";
  End
  
  delete_last_ts;

End


-- fsimtl = Future simtl
To fsimtl '_p;
  simtl_internal _p, 1;
End 


-- simtl = both future and path but with no loop.
To simtl '_p;
    If (simu_loop)
      Print "Cannot evaluate past formulas with looped model\n";
    Else
      simtl_internal _p, 0;
    End
End 
