Print "Loading Abstract.tlv  $Revision: 4.3 $\n";

----------------------------------------------------------------------
-- Abstraction.

-- The inputs should be as follows:
--
--  corr : Represents Oa = Oc
--
-- Automatically computed from the smv file:
--   Ia, Ic, rho_a, rho_c, Va, 
--   Wa, Wc : Owned variables (sets)
--
-- Abstract requires Util.tlv,  MCTL.tlv and MCsimple.tlv .


-- Cn - System number of concrete system.
-- An - System number of abstract system.


-- Verify premises A1 of Abadi-Lamport abstraction.
Func al_A1(An, new_ts);

    Print "\nA1: Is -> Ia[alp]\n";

    Local kapIa := ((I(An) & alp) forsome V(An));
    Let counter := !(I(new_ts) -> kapIa);
--    Let counter := !(Is & alp -> Ia);
    If (counter)
      Print "\n Premise A1 failed\n", counter;
      Return 0;
    Else
      Print "Premise A1 OK\n";
      Return 1;
    End -- If (counter)

End




-- Verify premises A4, A5 of Abadi-Lamport abstraction.
Func al_A4_A5(An, new_ts);

    Print "\n A4: Check abstract jutice requirements\n";

    Local _count  := nJ(An);
    Let _status := 1;

    While (_count & _status)

      Print "\n Check abstract justice requirement: ",_count,"\n";
      Local kapJ := ((Ji(_count, An) & alp) forsome V(An));
      Local isident := 0;

      For (_jj in 1...nJ(new_ts))
        If ( is_false(Ji(_jj, new_ts) & !kapJ) )
          Print "\n Abstract justice ",_count,
                " is implied by concrete justice ",_jj,"\n";
          Let isident := 1;
          Break;
        End -- If (_j[_jj] & !kapJ)
      End -- While (_jj)

      If (!isident)
        Print "Verifying _j[",_count,"] : \n";
        Call Temp_Entail(1,kapJ, new_ts);
        If (!_reply)
          Print "\n Abstraction does not hold\n";
          Return 0;
        End -- If (!_reply)
      End -- If (!isident)

      Let _count := _count - 1;
    End -- While (_count & _status)


    Print "\n A5: Check abstract compassion requirements\n";

    Let _count  := nC(An);
    Let _status := 1;

    While (_count & _status)

      Print "\n Check abstract compassion requirement: ",_count,"\n";
      Local kapp := ((Cpi(_count, An) & alp) forsome Va);
      Local kapq := ((Cqi(_count, An) & alp) forsome Va);
      Let isident := 0;

      For (_jj in 1...nC(new_ts))
        If ( is_false( (kapp & !Cpi(_jj, new_ts) ) | 
                       (kapq & !Cqi(_jj, new_ts) ) ) )
          Print "\n Abstract compassion ",_count,
                " is implied by concrete compassion ",_jj,"\n";
          Let isident := 1;
          Break;
        End -- If ((kapp & !_cp[_jj]) | (kapq & !_cq[_jj]))
      End -- While (_jj)

      If (!isident)
        Print "Verifying cp,cq[",_count,"] : \n";
        Call check_react(1,kapp,kapq, new_ts);
        If (!_reply)
          Print "\n Abstraction does not hold\n";
          Return 0; 
        End -- If (!_reply)
      End -- If (!isident)

      Let _count := _count - 1;
    End -- While (_count & _status)

    Return 1;
End



   
To alabs Cn := 1, An := 2, Guide := 3; -- Abadi Lamport abstraction style

    Local Va := V(An);

    # Compute rhos and initial conditions of abstract and concrete systems.
    Local Ic := I(Cn);
    Local Ia := I(An);
    Local I3 := I(Guide);

    # Find owned variables.
    Local Wc := set_union(owned(Cn),owned(Guide));
    Local Wa := owned(An);

    Local rho_c := T(Cn) | id_of(Wc);
    Local rho_a := T(An) | id_of(Wa);

    Local Is := Ic & I3;
    Local rho_s := rho_c & T(Guide);

    -- Create new transition system!!

    -- Copy concrete system to new system.
--    Local new_ts := copy_ts(Cn);
    Let new_ts := copy_ts(Cn);
    set_I Is, new_ts ;

    -- Add shared variables
    add_V V(Guide), new_ts;

    -- Add shared owned variables
    add_O owned(Guide), new_ts;

    -- Erase old transition relation and set new one.
    erase_T new_ts;
    add_disjunct_T rho_s, new_ts;

    -- Add justice requirements of guide to new system.
    For (i in 1...nJ(Guide))
       add_J  Ji(i, Guide), new_ts;
    End

    Local _rr := reachable(new_ts);

    If ( ! al_A1(An, new_ts) )
        delete_last_ts;
        Return;
    End

    Print "\nA2: rho_s -> rho_a[alp][alp']\n";
--    Let kaprhoa := (((rho_a & alp & next(alp)) forsome Va) forsome next(Va));
    Let kaprhoa := ((rho_a & next(alp)) forsome next(Va));
--    Let counter := !(_rr & rho_s -> kaprhoa);
    Let counter := !(_rr & rho_s & alp -> kaprhoa);
    If (counter)
      Print "\n Premise A2 failed\n", counter;
      delete_last_ts;
      Return;
    Else
      Print "Premise A2 OK\n";
    End -- If (counter)


    Print "\nA3: Oc = Oa[alp]\n";
    Let kapcorr := ((corr & alp) forsome Va);
    Let counter := !(_rr -> kapcorr);
    If (counter)
      Print "\n Premise A3 failed\n", counter;
      delete_last_ts;
      Return;
    Else
      Print "Premise A3 OK\n";
    End -- If (counter)

    If ( al_A4_A5(An, new_ts) )
       Print "\n Abstraction proven\n";
    End

  delete_last_ts;

End -- alabs


----------------------------------------------------------------------

-- Abadi Lamport abstraction style for closed systems
To close-alabs  Cn := 1, An := 2, Guide := 3;

    Local Va := V(An);

    # Compute rhos and initial conditions of abstract and concrete systems.
    Local Ic := I(Cn);
    Local Ia := I(An);
    Local I3 := I(Guide);

    Local rho_c := T(Cn);
    Local rho_a := T(An);

    Local Is := Ic & I3;
    Local rho_s := rho_c & T(Guide);


    -- Create new transition system!!

    -- Copy concrete system to new system.
    Local new_ts := copy_ts(Cn);
    set_I Is, new_ts;

    -- Add shared variables
    add_V V(Guide), new_ts;

    -- Erase old transition relation and set new one.
    erase_T new_ts;
    add_disjunct_T  rho_s, new_ts;

    -- Add justice requirements of guide to new system.
    For (i in 1...nJ(Guide))
       add_J  Ji(i, Guide), new_ts;
    End

    Local _rr := reachable(new_ts) & set_feas_simple(new_ts);

    If ( ! al_A1(An, new_ts) )
        delete_last_ts;
        Return;
    End

    Print "\nA2: rho_s -> rho_a[alp][alp']\n";
    Let kaprhoa := ((rho_a & next(alp)) forsome next(Va));
    Let counter := !(_rr & rho_s & alp & next(_rr) -> kaprhoa);
    If (counter)
      Print "\n Premise A2 failed\n", counter;
      delete_last_ts;
      Return;
    Else
      Print "Premise A2 OK\n";
    End -- If (counter)

    Print "\nA3: Oc = Oa[alp]\n";
    Let kapcorr := ((corr & alp) forsome Va);
    Let counter := !(_rr -> kapcorr);
    If (counter)
      Print "\n Premise A3 failed\n", counter;
      delete_last_ts;
      Return;
    Else
      Print "Premise A3 OK\n";
    End -- If (counter)


    If ( al_A4_A5(An, new_ts) )
       Print "\n Abstraction proven\n";
    End

    delete_last_ts;

End -- close-alabs
