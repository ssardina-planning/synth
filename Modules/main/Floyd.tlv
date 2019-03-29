-- This module implements the floyd method of verifying
-- a sequential program. No concurrent programs are allowed!!!
--
-- The original program must be an spl program.
--
-- The only exported routine is:
--
--    chk_inv c,e,n;
--
-- c and e are both arrays of length n.
-- c is an array of cuts and e an array of invriants which 
-- should hold on the corresponding cuts.
-- A cut is simply of the following form:
--
--  Let c[1] := at_l_1;
--
-- One of the cuts must be at the initial program location.
--
-- All cuts must be disjoint, i.e., the same location cannot
-- appear twice in the array c.
-- 
-- The cuts must cut all loops.
--
-- It is not required that the final program location have
-- a cut, but that would mean that you dont know in what 
-- state the program terminates.
--
-- If there are cuts which are not reachable from the initial
-- state, they are not checked.

Print "Loading Floyd.tlv $Revision: 4.1 $\n";

-- Print all program locations.  Used for debugging.
To print_loc;
  Local k := pi1;
  Local s;

  While(k)
    Let s := sat(k);
    Print s;

    Let k := case
               !s =0 : 0;
               1     : k;
             esac;
  End
End



-- Check that all loops are cut. In order to find an uncut
-- loop we find a location which is reachable from itself (but
-- not via a cut).
Func exists_uncut_loop(&c,n);

  Local i;
  Local i1;
  Local locations := pi1;
  Local curr_loc;

  While(locations)

    Let curr_loc := sat(locations);

    -- We now try to find if curr_loc is reachable
    -- from itself without passing through cuts.

    Let reachable := curr_loc;
    Let no_of_iterations := 0;

    While(1)

      -- Find adjacent successors.
      Let reachable := succ1(reachable) & !reachable;

      -- Remove all successors which are on a cut.
      Let i := n;
      While(i)

        -- Remove intersection of cut and reachable from reachable
        Let cuts_sect := reachable & c[i];
        If (cuts_sect)
          Let reachable := reachable & ! cuts_sect;
        End

        Let i := i - 1;
      End


      If (reachable)
        -- Check that "reachable" doesn't include the curr_loc.
        -- If it does then this means that curr_loc is reachable
        -- from itself not via cuts.
        If (reachable & curr_loc)
          Return curr_loc;
        End


        -- Check to see how long have we been running this
        -- procedure. If it is too long then it may be the case
        -- that there is a loop but it does not include curr_loc
        -- and thus we are stuck in an infinite loop.
        If (no_of_iterations > size(pi1))
          Break;
        End
      Else
        Break;
      End

      Let no_of_iterations := no_of_iterations + 1;
    End

    -- Remove curr_loc from the list of locations we still need
    -- to check for self-reachability.
    Let locations := case
               !curr_loc =0 : 0;
               1            : locations;
             esac;
  End

  Return 0;
  
End


-- Array c - cuts,  Array e - expressions

To chk_inv &c,&e,n;

  -- Test that the array "c" is disjoint.
  Local j1:=n;
  Local j2;
  While (j1 - 1)
   
    Let j2 := j1 -1 ;
    While (j2)
      If (c[j1] & c[j2])
        Print "Error: The cut array is not disjoint\n";
        Print "Array items ",j1,",",j2," have nonempty intersection\n";
        Return;
      End

      Let j2 := j2 - 1 ;
    End

    Let j1 := j1 - 1 ;
  End

  -- Initial condition should be labeled by one cut.
  Local i:= n;
  Local init_cut := 0;
  While (i)
    If (I() & c[i])
      Let init_cut := i;
      Local stat[i] := 1;
    Else
      Local stat[i] := 0;
    End
    Let i := i - 1;
  End

  If (init_cut)
    -- Do superficial check to see that initial condition is reasonable.
    -- We only check that _i and the initial cut expression have an 
    -- intersection. If they dont have an intersection then it is obvious
    -- that the initial cut expression cannot hold at the initial state.

    -- We may want the expression of the initial cut to be more
    -- restrictive that _i, for example, if we have a program which 
    -- recieves some nondeterminstic input (like x,y in order to compute
    -- x/y) then we might want to restrict the value of y to y>0 even
    -- if there is no "where y>0" clause in the program.
    -- On the other hand we may want the expression of the initial cut
    -- to be less restrictive than _i, for example, if we dont need
    -- to be as restrictive as _i in order to carry out the proof.
    If (e[init_cut] & I())
      -- Do nothing
      Let i := i;
    Else
      Print "Error: There is no interesection between the expression of the\n";
      Print "initial cut and the initial condition. \n";
      Return;
    End
  Else
    Print "Error: Initial condition should have a cut\n";
    Return;
  End


  Local result := exists_uncut_loop(c,n);
  If (result)
    Print "Error: There exists an uncut loop.\n";
    Print "It inculdes the following location : ",result;
    Return;
  End

  While (1)
  
    -- Find an array item of status 1 (the successor invariants
    -- of this cut should be checked but haven't been yet).
    Let i := n;
    While (i)
      If (stat[i] = 1)
        Let stat[i] := 2;
        Break;
      End
      Let i := i - 1;
    End

    -- If i=0 then there are no more cuts to check.
    If (i > 0)
      Let curr_cut := i;
    Else
      Break;
    End

    -- Generate all successors of curr_cut until all possible
    -- adjacent cuts have been encoutered.

    Let curr_state := c[curr_cut] & e[curr_cut];

    -- All the locations which have been reached from the current cut.
    Let _count := 0;

    While (curr_state)

      -- Find immediate successors (no idle steps)
      Let curr_state := succ1(curr_state)& ! curr_state;

      -- Search for intersection with cuts.
      Let i := n;
      While (i)
        Let cuts_sect := curr_state & c[i];

        If (cuts_sect)
          -- Check if cut invariant holds on cut
          If (!(cuts_sect -> e[i]))
            -- We have found a counter example.
            Print "Error: Counter example found:\n";
            Print "It is possible that at cut ",curr_cut,
                  " the corresponding invariant holds\n";
            Print "yet in adjacent cut ",i,
                   " the corresponding expression does NOT hold...\n",
                   "For example, the following can hold at cut ",i,"\n",
                   !( cuts_sect -> e[i]);
            Return;
          Else
            Let curr_state := curr_state & ! cuts_sect;

            -- If this cut has not been encountered before then
            -- mark this cut so we will check if all successor cuts
            -- of his hold.
            Let stat[i] := case
                             stat[i] = 0 : 1;
                             1           : stat[i];
                           esac;
          End
        End

        Let i := i - 1;
      End

      Let _count := _count + 1;

      If (_count = 100)
        Print "I am giving up. This is taking too long\n";
        Print "I am trying to find all cuts reachable from cut ",
              curr_cut," but I am not able to reach them\n";
        Print "You have probably forgotten to cut one of the loops\n";
        Return;
      End

    End

  End

  -- Print out which cuts were reached.
  Print "In all reachable cuts the invariants are true\n";
  Print "The reachable cuts are:\n";

  For (i1 in 1...n)
    If (stat[i1])
      Print i1," ";
    End
  End
  Print "\n";

End

