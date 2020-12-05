-- Synthesis for (\G p)-games
-- Useful entries: check_realizability, symb_strategy, enumerate_symb
--                 print_automat

Let debug  := 0;
Let doform := 0;
Let onlyz  := 0;
Let onlyy  := 0;
Let verbose := 1;

To eol;
  Print ("\n");
End -- To eol;

To abort;
  Print ("\n Execution Aborted\n");
  Local aaa := zzz;
End -- To abort;

Func null(bdd);
  If (bdd)
    Return 0;
  Else
    Return 1;
  End -- If (bdd)
End -- Function null(bdd);

To prepare_synt;

  Let vars1 := V(1);
  Let vars2 := V(2);
  Let vars  := vars1 & vars2;
  Let prv1 := prime(V(1));
  Let prv2 := prime(V(2));
  Let prv  := prv1 & prv2;
  Let trans1 := Ti(1,1);
  Let trans2 := Ti(1,2);

  Let cts := 0;

End -- To prepare_synt;

Func cox(state);
  Let rec_state := state;
  Let exy := ((trans2 & prime(state)) forsome prv2);
  Let rcox := ((trans1 -> exy) forall prv1);
  Let prcox := prime(rcox);
  Return rcox;
End -- Func cox(state);

To check_realizability;  -- Externally accessible

  Print "\n Check Realizability\n";
  prepare_synt;
  Let win := winm(good);
  Let initial := I(1) & I(2);
  Let counter := initial & !win;
  If (counter)
    Print "\n Specification is unrealizable\n";
    Print counter;
    Let realizable := 0;
    Return;
  Else
    Let realizable := 1;
  End -- If (counter)

  Print "\n Specification is realizable \n";

End -- To check_realizability;

Func winm(invp);
  Local z := 1;
  Fix (z)
    Let z := invp & cox(z);
  End -- Fix (z)
  Return z;
End -- Func winm(invp);

To push_state given_state, given_j;
  Let height := height + 1;
  Let state_stack[height] := given_state;
  Let j_stack[height] := given_j;
End -- To push_state given_state, given_j;

To pop_state;
  Let p_state := state_stack[height];
  Let p_j     := j_stack[height];
  Let height       := height - 1;
End -- To pop_state;

Func add_candidate(candidate,jcand);
  Local i := 1;
  While (i <= aut_size)
    If (candidate & aut_state[i])
      If (jcand = aut_j[i])
        Return i;
      End -- If (jcand = aut_j[i])
    End -- If (candidate & aut_state[i])
    Let i := i + 1;
  End -- While (i <= aut_size)
  Let aut_state[i] := fsat(candidate);
  Let aut_j[i]     := jcand;
  Let aut_ns[i]    := 0;
  Let aut_size     := i;
  push_state aut_state[i],jcand;
  Return i;
End -- Func add_candidate(candidate,jcand);

To build_symb;
  If (cts=0)
    Let cts := new_ts();
    Call set_I(I(1) & I(2),cts);
    Call set_V(vars,cts);
    Call erase_T(cts);
    Let trans := win & trans12 & next(win);
    Call add_disjunct_T(trans,cts);
    Let _s[cts].jn := 0;
  End -- If (cts=0)
  Let progreach := reachable(cts);
End -- To build_symb;

To check_symb;
  -- Check that a symbolic strategy is correct
  Print "\n Check that a symbolic strategy is correct\n";
  build_symb;
  -- Check that transition relation is total
  Let wintrans := trans & win;
  Let from := (wintrans forsome prv) & trans1;
  Let avsuc := (wintrans forsome prv2);
  If (is_true(from <-> avsuc))
    Print "\n","Transition relation is complete\n";
  Else
    Print "\n","Transition relation is incomplete \n";
    Print from & !avsuc;
    abort;
  End -- If (is_true(from <-> avsuc))     
  Let counter := progreach & !good;
  If (counter)
    Print "\n A winning state violates invariant property\n", counter;
    abort;
  Else
    Print "\n All winning states satisfy invariant\n";
  End -- If (counter)
End -- check_symb;

To symb_strategy;
-- Compute symbolic strategy
  Let trans12 := trans1 & trans2;
  build_symb;
End -- To symb_strategy;

To push_stat given_state;
  Let height := height + 1;
  Let stat_stack[height] := given_state;
End -- To push_stat given_state, given_j;

To pop_stat;
  Let p_state := stat_stack[height];
  Let height       := height - 1;
End -- To pop_stat;


To enumerate_symb;
  Let height := 0;
  Let auto_size := 0;

-- Place all initial states in stack

  Let iset := I(cts);
  While (iset)
    Let state := fsat(iset);
    push_stat state;
    Let iset := iset & !state;
  End -- While (iset)
  Let nproc := 0;
  While (height)
-- Repeat until stack is empty
    pop_stat;
    Let new_state := find_auto(p_state);
    Let candidate := succ1(p_state,cts);
    If (null(candidate))
      Print ("\n Following state has no winning successor\n");
      Print p_state;
      eol;
      abort;
    End -- If (null(candidate))
    While (candidate)
      -- Add candidate to successors of "new_state"
      Let gsucc := add_candidat(candidate);
      Let auto_ns[new_state] := auto_ns[new_state] + 1;
      Let auto_suc[new_state][auto_ns[new_state]] := gsucc;
      Let candidate := candidate & !auto_state[gsucc];
    End -- While (candidate)
  End -- While (height)
End -- To enumerate_symb;

Func find_auto(g_state);
  Local i := 1;
  While (i <= auto_size)
    If (is_true(g_state <-> auto_state[i]))
      Return i;
    End -- If (is_true(g_state <-> auto_state[i]))
    Let i := i+1;
  End -- While (i <= aut_size)
  Let auto_state[i] := g_state;
  Let auto_ns[i]    := 0;
  Let auto_size := i;
  Return i;
End -- Func find_auto(g_state);

Func add_candidat(candidate);
  Local i := 1;
  While (i <= auto_size)
    If (candidate & auto_state[i])
      Return i;
    End -- If (candidate & aut_state[i])
    Let i := i + 1;
  End -- While (i <= auto_size)
  Let auto_state[i] := fsat(candidate);
  Let auto_ns[i]    := 0;
  Let auto_size     := i;
  push_stat auto_state[i];
  Return i;
End -- Func add_candidat(candidate);

To print_automat;
  -- Print automaton
  Print "\n Automaton States\n\n";
  Local ntrans := 0;
  For (i in 1...auto_size)
    Print "State ",i,"\n",auto_state[i],"\n";
  End -- For (i in 1...auto_size)
  Print "\n Automaton Transitions\n\n";
  For (i in 1...auto_size)
    Print "From ",i," to ";
    Let ntrans := ntrans + auto_ns[i];
    For (j in 1...auto_ns[i])
      Print " ",auto_suc[i][j];
    End -- For (j in 1...auto_ns[i])
    Print "\n";
  End -- For (i in 1...auto_size)
  Print "\n","Automaton has ",auto_size," states, and ",ntrans,
  " transitions\n";
End -- To print_automat;

To count_states;
  enumerate_symb;
  Let ntrans := 0;
  For (i in 1...auto_size)
    Let ntrans := ntrans + auto_ns[i];
  End -- For (i in 1...auto_size)
    Print "\n","Automaton has ",auto_size," states, and ",ntrans,
  " transitions\n";
End -- coun_states

