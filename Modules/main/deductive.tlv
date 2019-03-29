--
--   A file implementing various deductive rules
--
--  binv, inv, invx
--
--  well, well-lex
--
Print "Loading modified deductive.tlv $Revision: 4.9 $\n";

------------------------------------------------------------------------
-- SAFETY
------------------------------------------------------------------------

Proc binv_old(p, tsn := _s.cur);

  Print "Checking Premise I1\n";
  Let counter := I(tsn) & !p;
  If (counter)
    Print "Premise I1 is not valid. Counter-example =\n";
    Let counter1 := counter;
    Print counter;
  Else
    Print "Premise I1 is valid. Checking Premise I2.\n";
    Let counter := refute_T(p & !next(p), tsn);
    Let counter2 := sat(counter);
    If (counter)
      Print "Premise I2 is not valid. Counter-example =\n";
      Print counter2;
      Let src2  := (counter2 forsome prime(V(tsn)));
      Let dest2 := unprime(counter2 forsome V(tsn));
    Else
      Print "Premise I2 is valid.\n * * * Assertion p is invariant.\n";
    End -- If (counter)
  End -- If (counter)
End -- binv

Proc binv(p, tsn := _s.cur);

  Print "Checking Premise I1\n";
  Let counter := I(tsn) & !p;
  If (counter)
    Print "Premise I1 is not valid. Counter-example =\n";
    Let counter1 := counter;
    Print counter;
  Else
    Print "Premise I1 is valid. Checking Premise I2.\n";
    Let counter := refute_T2(p, !next(p), tsn);
    Let counter2 := sat(counter);
    If (counter)
      Print "Premise I2 is not valid. Counter-example =\n";
      Print counter2;
      Let src2  := (counter2 forsome prime(V(tsn)));
      Let dest2 := unprime(counter2 forsome V(tsn));
    Else
      Print "Premise I2 is valid.\n * * * Assertion p is invariant.\n";
    End -- If (counter)
  End -- If (counter)
End -- binv


Proc inv(p, phi, tsn := _s.cur);

  Print "Checking Premise I1\n";
  Let counter := I(tsn) & !phi;
  If (counter)
    Print "Premise I1 is not valid. Counter-example =\n";
    Print counter;
  Else
    Print "Premise I1 is valid. Checking Premise I2.\n";
    Let counter := refute_T2(phi, !next(phi), tsn);
    If (counter)
      Print "Premise I2 is not valid. Counter-example =\n";
      Print counter;
    Else
      Print "Premise I2 is valid. Checking Presmise I3.\n";
      Let counter := phi & !p;
      If (counter)
        Print "Premise I3 is not valid. Counter-example =\n";
        Print counter;
      Else
        Print "Premise I3 is valid.\n * * * Assertion p is invariant.\n";
      End -- If (counter)
    End -- If (counter)
  End -- If (counter)
End -- inv


Proc invx(p,aux, tsn := _s.cur);

  Print "Checking Premise I1\n";
  Let counter := I(tsn) & !p;
  If (counter)
    Print "Premise I1 is not valid. Counter-example =\n";
    Let counter1 := counter;
    Print counter;
  Else
    Print "Premise I1 is valid. Checking Premise I2.\n";
    Let counter := refute_T2(aux & p, !next(p), tsn);
    Let counter2 := sat(counter);
    If (counter)
      Print "Premise I2 is not valid. Counter-example =\n";
      Print counter;
      Let src2  := (counter2 forsome prime(V(tsn)));
      Let dest2 := unprime(counter2 forsome V(tsn));
    Else
      Print "Premise I2 is valid.\n * * * Assertion p is invariant.\n";
    End -- If (counter)
  End -- If (counter)
End -- invx(p,aux)


Proc isvalid(p);

  Let counter := !p;
  If (counter)
    Print "Formula is not valid. Counter-example =\n";
    Print counter, "\n";
  Else
    Print "Formula is valid.\n";
  End -- If(counter)

End -- isvalid


----------------------------------------------------------------------
-- RESPONSE
----------------------------------------------------------------------

Proc well(start, goal,_inv, & helpful, delta, tsn := _s.cur);

  Let pend := 0;
  Let _nh  := nJ(tsn);

  If (_nh != length(helpful))
    Print "\n Length of helpful array unequal to number ",
          "of justice requirements\n";
    Return;
  End -- If (_nh != length(helpful))

  Let j := _nh;
  While (j)
    Let pend := pend | helpful[j];
    Let j := j - 1;
  End -- While (j)

  Print "\n Apply rule well\n";

  Let counter1 := !(start & _inv -> (goal | pend));
  If (counter1)
    Print "\n Premise 1 false. Counter-Example:\n", counter1;
    Return;
  End -- If (counter1)

  Let j := _nh;
  While (j)
    Let counter2 := !(_inv & helpful[j] & T(tsn) ->
    (next(helpful[j]) & delta=next(delta) & !Ji(j, tsn)) | next(goal) |
             next(pend) & (delta > next(delta))); 
    If (counter2)
      Print "\n Premise 2 false for j: ",j," Counter-Example:\n", counter2;
      Return;
    End -- If (counter2)

    Let j := j - 1;
  End -- While (j)

  Print "\n Property is Valid\n";

End -- well(start, goal,_inv, & helpful, delta);


Proc well-lex(start, goal, _inv, & helpful, & delta, sized, tsn := _s.cur);

  Let pend := 0;
  Let _nh  := nJ(tsn);

  If (_nh != length(helpful))
    Print "\n Length of helpful array unequal to number ",
          "of justice requirements\n";
    Return;
  End -- If (_nh != length(helpful))

  Let j := _nh;
  While (j)
    Let pend := pend | helpful[j];
    Let j := j - 1;
  End -- While (j)

  Print "\n Apply rule well-lex\n";

  Let delgt := 0;
  Let deleq := 1;
  Let k := 1;
  While (k <= sized)
    Let delgt := delgt | deleq & delta[k] > next(delta[k]);
    Let deleq := deleq & delta[k] = next(delta[k]);
    Let k := k+1;
  End -- While (k <= sized)
  
  Let counter1 := !(start & _inv -> (goal | pend));
  If (counter1)
    Print "\n Premise 1 false. Counter-Example:\n", counter1;
    Return;
  End -- If (counter1)

  Let j := _nh;
  While (j)
    Let counter2 := !(_inv & helpful[j] & T(tsn) ->
    (next(helpful[j]) & deleq & !J(j, tsn)) | next(goal) |
             next(pend) & delgt); 
    If (counter2)
      Print "\n Premise 2 false for j: ",j," Counter-Example:\n", counter2;
      Return;
    End -- If (counter2)

    Let j := j - 1;
  End -- While (j)

  Print "\n Property is Valid\n";

End -- well-lex(start, goal, _inv, & helpful, & delta, sized, tsn := _s.cur);

----------------------------------------------------------------------

Proc distr(start,goal,_inv, & helpful, & delta, tsn := _s.cur);

  Let pend := 0;
  Let _nh  := nJ(tsn);

  If (_nh != length(helpful) | _nh != length(delta))
    Print "\n Length of helpful or delta arrays unequal to number ",
          "of justice requirements\n";
    Return;
  End -- If (_nh != length(helpful))
  Let conjd := 1;
  Let disjd := 0;

  Let j := _nh;
  While (j)
    Let pend := pend | helpful[j];
    Let conjd := conjd & (delta[j] >= next(delta[j]));
    Let disjd := disjd | (delta[j] >  next(delta[j]));
    Let j := j - 1;
  End -- While (j)

  Print "\n Apply rule distr\n";

  Let counter1 := !(start & _inv -> (goal | pend));
  If (counter1)
    Print "\n Premise 1 false. Counter-Example:\n", counter1;
    Return;
  End -- If (counter1)

  Let j := _nh;
  While (j)
    Let counter2 := !(_inv & helpful[j] & T(tsn) & !goal ->
    (next(helpful[j]) & !Ji(j,tsn) | next(goal) | next(pend) & disjd));
    If (counter2)
      Print "\n Premise 2 false for j: ",j," Counter-Example:\n", counter2;
      Return;
    End -- If (counter2)

    Let j := j - 1;
  End -- While (j)

  Let counter3 := !(_inv & pend & T(tsn) & !goal ->
  (next(goal) | conjd));
  If (counter3)
    Print "\n Premise 3 false. Counter-Example:\n", counter3;
    Return;
  End -- If (counter3)

  Print "\n Property is Valid\n";

End -- distr(start,goal,_inv & helpful, & delta);

