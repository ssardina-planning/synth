-- Module for running simulations of a program.
--
-- -- Create n items of simulation which is an execution
-- To simulate n;

-- Create only the first step according to expression e.
-- To start e;

-- Extend simulation .
-- To cont n;

-- Try to extend simulation by one step, where in the next step,
--             e holds.
-- To step e;

-- Truncate simulation at step n;
-- To trunc n;

-- Show all the simulation up till now.
-- To show_all;

-- Show window of simluation around step n.
-- Let window_size := 3;
-- To show n;

-- Print current (i.e. last) item of the simulation.
-- To curr;

-- Print last item of the simulation.
-- To last;

-- Find location (if exists) of expression "e" in execution.
-- To find e;

-- Evaluate a propositional expression, exp in a specific state, n, of the simulation.
-- To eval exp, n;  

-- Evaluate a propositional expression, exp in a specific state, n,
-- of the simulation. The difference between eval_next and eval is that
-- eval_next takes into consideration states n and n+1 of the simulation,
-- so references to "next()" in the expression have meaning.
-- To eval_next exp, n;  

-- Make the simulation "infinite" by looping back the end to state n
-- This is only used by TLVSIMU.tlv
-- To setloop n;


-- 
-- Routines to modify the simulatio randomly...
--

-- Set a step of the simulation (with no connection to the transition relation).
-- To setstep n,e;

-- Append a step of the simulation (with no connection to the transition relation).
-- To appstep e;

-- Change the value of a variable in a step of the simulation.
-- To setvar n,v,e;


Print "Loading SIMULATE $Revision: 4.4 $\n";

-- This function (and all references to it) should be removed once
-- a better frsat routine is in place. It comes to solve the following
-- problem: when new variables are added *after* the smv or spl program
-- is loaded - such variables enter the simulation because of the "frsat"
-- function (which should probably be extened by another parameter as in
-- the case of fsat). The following function takes a bdd and wipes out
-- any reference for these new variables:
Func clear_new_vars(_state);
  Local _mask := set_minus(support(_state),V());
  Return _state forsome _mask;
End


Let simu_loop := 0;  -- Loopback.

-- Initialize array simu, which will contain the simulation.
new simu;


-- Return random next state from state "state".
Func random_step(state);

  -- We add  (T() forsome primed) so that if the transition relation
  -- enforces constraints on the current state ( e.g.. combinational
  -- circuit) then this is expressed in the next state.
  Local state_succ := succ1(state);
  Local nstep := state_succ & (T( ) forsome prime(V( )));

  -- If nstep is false, then there is no successor of "state"
  -- which in itself has a successor. However, we still might
  -- be able to obtain a successor which does not have a successor 
  -- (this state will be the last state of the run).
  -- So lets try again.
  If (is_false(nstep))
      Let nstep := state_succ;
  End

  Return clear_new_vars(frsat(nstep));
End

--
-- CREATE SIMULATION S
--

-- Create only the first step of the simulation according to
-- expression e.
To start e;
  new simu;
  Local first_state :=
    clear_new_vars(frsat(I() & e & (T( ) forsome prime(V( )))));

  If (first_state)
    push simu, first_state;
    Print "First step of simulation has been created\n";
  Else
    Print
      "The expression you specified doesn't conform to the initial condition\n";
  End
End


-- Create n items of simulation  which is an execution
To simulate n;

  start TRUE; -- Initialize simulation .

  If (length(simu) = 0)
    Print "Simulation not created: stuck on first state\n"; 
  Else
    Run cont n - 1;
    Print "New simulation created\n";
  End
End

To sim n;
  simulate n;
End

-- Extend simulation .
To cont n;

  Local next_step;

  If (length(simu) > 0)
    Print "Adding ",n," new steps to simulation \n";

    For (i in 1...n)
      Let next_step := random_step(top(simu));
      push simu, next_step;

      If (is_false(next_step))
        Print "Simulation execution terminated at step ",length(simu),"\n";
        Break;
      End
    End
    
  Else
    Print "There is no simulation to continue. Run 'simulate' first\n";
  End
End

-- Try to extend simulation by one step, where in the next step, e holds.
To step e;

  If (length(simu) = 0)
    Print "You have not created a simulation yet...\n";
    Return;
  End

  Let nstate := succ1(top(simu)) & e;
  If (nstate)
    push simu, clear_new_vars(frsat(nstate));
    Print "Step ",length (simu)," was added to simulation\n";
  Else  
    Print "The expression does not hold on any successor\n";
  End
End


-- Truncate simulation at step n;
To trunc n;
  If (n< length(simu) & n > -1)
    Let simu[0] := n;
    Print "Simulation truncated at step ",n,"\n";
  End 
End

--
-- PRINT SIMULATION S
--

To print_step k;

  Print "---- Step ",k,"\n";

  If (simu[k])
    Print simu[k];
  Else
    Print "Halt\n";
  End
End

-- Show all the simulation up till now.
To show_all;
 
  Local len := length(simu);

  If (len = 0)
    Print "You have not created a simulation yet...\n";
  Else
      For (k in 1...len)
        Run print_step k;
      End

      If (simu_loop)
        Print "Loop back to step ", simu_loop,"\n";
      End
  End
End

To sa;
  show_all;
End

-- Show window of simluation around step n.
Let window_size := 3;
To show n;

  Local len := length(simu);

  If (len)
      For (i in n - window_size ... n + window_size)
        If (i>0 & i <= len)
          Run print_step i;
        End
      End
  Else
      Print "You have not created a simulation yet...\n";
  End

End

-- Print current (i.e. last) item of the simulation.
To curr;
  If (length(simu) = 0)
    Print "You have not created a simulation yet...\n";
  Else
    Run print_step length(simu);
  End
End


-- Print last item of the simulation.
To last;
  Local len := length(simu);
  If ( len = 0)
    Print "You have not created a simulation yet...\n";
  Else
    If (simu[len])
      Run print_step len;
    Else
      Run print_step len - 1;
    End
  End
End

--
-- CHECK PROPERTIES OF SIMULATION
--

-- Find location (if exists) of expression "e" in execution.
To find e;
  Local len := length(simu);
  For (k in 1...len)
    If (simu[k] & e)
      Print "The expression holds at step ",k,"\n";
      Return;
    End
  End

  Print "The expression was not found in the simulation\n";
End


-- Evaluate a propositional expression, exp in a specific state, n, 
-- of the simulation.
To eval exp, n;  
  If (n > 0 & n <= length(simu))
    Print value(exp & simu[n]),"\n";
  Else
    Print n," is out of range; must be in ",1,"..",length(simu),"\n";
  End
End


-- Evaluate a propositional expression, exp in a specific state, n, 
-- of the simulation.
To eval_next exp, n;  
  If (n > 0 & n < length(simu))
    Print value(exp & simu[n] & next(simu[n + 1]) ),"\n";
  Else
    Print n," is out of range; must be in ",1,"..",length(simu) - 1,"\n";
  End
End

-- Make the simulation "infinite" by looping back the end to state n
-- This is only used by TLVSIMU.tlv
To setloop n;

  If (n >=0 & n <= length(simu))
    Let simu_loop := n;
    If (n=0)
      Print "Loop back has been canceled\n";
    Else
      Print "Loop set to go back to step ",n,"\n";
    End
  Else
    Print n," is out of range; must be in ",0,"..",length(simu),"\n";
  End

End

-- 
-- Routines to modify the simulation randomly...
--

-- Set a step of the simulation (with no connection to the transition relation).
To setstep n,e;
  
  If (n > 0 & n <= length(simu))
    Let simu[n] := fsat(e,V());
    Print "Step ",n," has been set\n";
  Else
    Print n," is out of range; must be in ",1,"..",length(simu),"\n";
  End

End


-- Append a step of the simulation (with no connection to the transition relation).
To appstep e;
  push simu, fsat(e,V());
  Print "A step has been appended to the simulation\n";
End


-- Change the value of a variable in a step of the simulation.
To setvar n,&v,e;

  If (n > 0 & n <= length(simu))
    Let simu[n] := assign(simu[n],v,e);
    Print "Variable ",'v," of step ",n," has been set\n";    
  Else
    Print n,"is out of range; must be in ",1,"..",length(simu),"\n";
  End

End
