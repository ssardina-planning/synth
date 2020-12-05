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

To prepare_synt; --(FP) initializes variables

  Let vars1 := V(1); --(FP) environment variables
  Let vars2 := V(2); --(FP) system variables
  Let vars  := vars1 & vars2; 
  Let prv1 := prime(V(1)); 
  Let prv2 := prime(V(2));
  Let prv  := prv1 & prv2;
--  Let feasible1 := find_feas(Ti(1,1));
--  Let trans1 := Ti(1,1) & next(feasible1);
  Let trans1 := Ti(1,1); --(FP) environment's transition relation
--  Let feasible2 := find_feas(Ti(1,2)); 
--  Let trans2 := Ti(1,2) & next(feasible2);
  Let trans2 := Ti(1,2);--(FP) system's transition relation

  Let nps := nJ(1); -- nr. of justice premises
  Let nqs := nJ(2); -- nr. of justice consequences
  Let cts := 0; -- ??

End -- To prepare_synt;

Func cox(state);
	Print "computing cox","\n";
  Let rec_state := state;
  Let exy := ((trans2 & prime(state)) forsome prv2);
  Let rcox := ((trans1 -> exy) forall prv1);
  Let prcox := prime(rcox);
  Return rcox;
End -- Func cox(state);

To check_realizability;

  Print "\n Check Realizability\n";
  prepare_synt;
  Let win := winm(nps,nqs);
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

Func winm(nps, nqs);
  Local x;
  Local y;
  Local z;
  Let ix := 0;
  Let iy := 0;
  Let iz := 0;
  Let oldz := 0;
  Let z    := 1;
  
    Let oldz := z;
    Let j := 1;
	Let oldy := 1;
	Let y    := 0;
	Let cy   := 1;
	Print "I(1):---\n"; form I(1); Print "---\n";
	Print "I(2):---\n"; form I(2); Print "---\n";
	While ((y != oldy) & !is_true((I(1) & I(2)) -> y) )
		-- Print "\tComputing Y:\n";
		Let oldy := y;
		Let start := Ji(j,2) | cox(y);
		Let y := 0;
		Let i := 1;
		Let x := start;
		Let x[j][cy][i] := x;
		Let y := y | start;
		
		Let y[j][cy] := y;
		Let cy := cy + 1;
		Let iy := iy + 1;
			
		Print "\t\tY:"; form y; Print "\n\n";
		-- Print "\nexpression value: \n------------------\n", ((I(1) & I(2)) -> y), "\n-------------------\n\n";
	End -- While (y != oldy)
      Let z := y;
      Let maxcy[j] := cy - 2; --(FP) needed for computing the strategy
      Let z[j] := z;
      Let iz := iz+1;
--    Let z[iz] := z;
	Print "Total number of iterations for computing Y: ", iy , "\n";
	Return y;
End -- Func winm(nps, & p, q);

Func find_feas(trans);
  Local old := FALSE;
  Local R := trans;
  Local i;
  Local new := 1;
  Let len := 1;

  While (!(new = old))
    Let old := new;
    Let new := new & pred(R, new);
    Let i := nJ(1);
    While (i)
      Let new := predecessors(new & _j[i], new & R);
      Let i := i - 1;
    End -- While (i)

  End -- (!(new = old))

  Return predecessors(new,trans);

End -- find_feas(trans);

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

To initialize_sym_strategy;
 For (i1 in 1...nqs)
     Let same_j[i1] := 0;
     Let next_j[i1] := 0;
 End -- For
End -- initilize_sym_strategy

Func find_aut(g_state,g_j);
  Local i := 1;
  While (i <= aut_size)
    If (g_state != aut_state[i])
      Let i := i + 1;
    Else
      If (g_j != aut_j[i])
        Let i := i + 1;
      Else
        Return i;
      End -- If (g_j != aut_j[i])
    End -- If (g_state != aut_state[i])
  End -- While (i <= aut_size)
  Let aut_state[i] := g_state;
  Let aut_j[i]     := g_j;
  Let aut_ns[i]    := 0;
  Let aut_size := i;
  Return i;
End -- Func find_aut(g_state,g_j);

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
End -- Func find_aut(g_state,g_j);


To find_sym_strategy;
   
   initialize_sym_strategy;
   Local temp := 0;
   Let trans12 := trans1 & trans2;
   Print "Computing the strategies i i\n";
   For (j in 1...nqs)
	 Local previous := 0;
	 For (i in 1...maxcy[j]+1)
	       For (k in 1...nps)
                     If (debug)
		       Print "Working on x[",j,"][",i,"][",k,"]\n";
                     End -- If (debug)
		     Let temp := !Ji(j,2) & trans12 &
			         prime(x[j][i][k]) & 
                            !((trans12 & prime(previous)) forsome prv2);
		     Let same_j[j] := same_j[j] | temp;
		     Let previous := previous | x[j][i][k];
	       End -- For (k in 1...nps)
         End -- For (i in 1...maxcy[j]+1)
   End -- For (j in 1...nqs)
   
   Print "Computing the strategies i i+1\n";
   For (j in 1 ...nqs)
	 Let nextj := (j mod nqs) + 1;
	 Let previous := 0;
	 For (i in 1 ...maxcy[j]+1)
	       For (k in 1...nps)
                     If (debug)
		       Print "Working on x[",nextj,"][",i,"][",k,"]\n";
                     End -- If (debug)
		     Let temp := Ji(j,2) & trans12 &
				 prime(x[nextj][i][k]) &
                           !((trans12 & prime(previous)) forsome prv2);
		     Let next_j[j] := next_j[j] | temp;
		     Let previous := previous | x[nextj][i][k];
	       End -- For (k in 1...nps)
         End -- For (i in 1...maxcy[j]+1)
   End -- For (j in 1...nqs)
   build_symb;
End -- Func find_sym_strategy

To find_strategy;
  Let height := 0;
  Let aut_size := 0;

-- Place all initial states in stack

  Let iset := initial;
  While (iset)
    Let state := fsat(iset);
    push_state state,1;
    Let iset := iset & !state;
  End -- While (iset)
  Let nproc := 0;
  While (height)
-- Repeat until stack is empty
    pop_state;
    Let new_state := find_aut(p_state,p_j);
-- Find minimal cy and i such that p_state \in x[p_j][cy][i]
    Let pcy := 0;
    Let cy  := 1;
    While ((cy <= maxcy[p_j]) & (pcy=0))
      If (p_state & y[p_j][cy])
        Let pcy := cy;
      Else
        Let cy := cy + 1;
      End -- If (p_state & y[p_j][cy]}
    End -- While ((cy <= maxcy[p_j]) & (pcy=0))
    If (pcy=0)
      Print "Following state is not in z[",p_j,"]\n";
      Print p_state;
      eol;
      abort;
    End -- If (pcy=0)
    Let i := 1;
    Let pi := 0;
    While ((i <= nps) & (pi = 0))
      If (p_state & x[p_j][pcy][i])
        Let pi := i;
      Else
        Let i := i + 1;
      End -- If (p_state & x[p_j][pcy][i])
    End -- While ((i <= nps) & (pi = 0))
   If (pi=0)
      Print "Following state is not in y[",p_j,"][",pcy,"]\n";
      Print p_state;
      eol;
      abort;
    End -- If (pi=0)
-- Compute set of environment successors
    Let envs := succ(trans1,p_state) & vars2;
    Let nes  := 0;
    While (envs)
      Let ones := fsat(envs);
      Let envs := envs & !ones;
      Let nes := nes + 1;
      Let ens[nes] := (ones forsome vars2);
    End -- While (envs)
-- For each environment successor, find a strategy successor
    For (e in 1...nes)
      -- Search if an e-successor already exists
      Let ces := ens[e];
        Let fulls := unprime((trans2 & p_state & prime(ces)) forsome vars);
        -- Check if p_state satisfies !Ji(pi,1) & csucc(x[p_j][pcy][pi])
        Let candidate := 0;
        Let jcand     := p_j;
        If (p_state & !Ji(pi,1))
          If (fulls & x[p_j][pcy][pi])
            Let candidate := fulls & x[p_j][pcy][pi];
          End -- If (fulls & x[p_j][pcy][pi])
        End -- If (p_state & !Ji(pi,1))
        If (null(candidate))
          -- Check if p_state satisfies Ji(p_j,2) & csucc(z[p_j+1])
          Let nxpj := (p_j mod nqs) + 1;
          If (p_state & Ji(p_j,2))
            If (fulls & z[nxpj])
              Let candidate := fulls & z[nxpj];
              Let jcand     := nxpj;
            End -- If (fulls & z[nxpj])
          End -- If (p_state & Ji(p_j,2))
        End -- If (null(candidate))
        If (null(candidate))
          -- Check if p_state satisfies csucc(y[p_j][pcy-1])
          If (pcy>1)
            If (fulls & y[p_j][pcy - 1])
              Let candidate := fulls & y[p_j][pcy - 1];
            End -- If (fulls & y[p_j][pcy - 1])
          End -- If (pcy>1)
        End -- If (null(candidate))
        If (null(candidate))
          Print ("\n Following state has no winning successor\n");
          Print p_state;
          eol;
          abort;
        End -- If (null(candidate))
        -- Add candidate to successors of "new_state"
        Let gsucc := add_candidate(candidate,jcand);
        Let aut_ns[new_state] := aut_ns[new_state] + 1;
        Let aut_suc[new_state][aut_ns[new_state]] := gsucc; 
    End -- For (e in 1...nes)
  End -- While (height)
End -- find_strategy;

To print_automaton;
  -- Print automaton
  Print "\n Automaton States\n\n";
  For (i in 1...aut_size)
    Print "State ",i," rank ",aut_j[i],"\n",aut_state[i],"\n";
  End -- For (i in 1...aut_size)
  Print "\n Automaton Transitions\n\n";
  For (i in 1...aut_size)
    Print "From ",i," to ";
    For (j in 1...aut_ns[i])
      Print " ",aut_suc[i][j];
    End -- For (j in 1...aut_ns[i])
    Print "\n";
  End -- For (i in 1...aut_size)
End -- To print_automaton;

To check_consistency;
  Call set_I(I(1) & I(2), 3);
  Call set_V(V(1) & V(2), 3);
  Call add_disjunct_T(T(1) & T(2), 3);
  For (i in 1...nJ(1))
    Call add_J(Ji(i,1),3);
  End -- For (i in 1...nJ(1))
  For (i in 1...nJ(2))
    Call add_J(Ji(i,2), 3);
  End -- For (i in 1...nJ(2))
  Print "\n Check Consistency of Specification\n";
  Let feas := set_feas_simple(3);
  Let counter := I(3) & !feas;
  If (counter)
    Print "\n Specification is inconsistent\n";
    Print counter;
    Return;
  End -- If (counter)

  Print "\n Specification is consistent \n";

End -- To check_consistency;

To build_symb;
  If (cts=0)
    Let cts := new_ts();
    Call set_I(I(1) & I(2)& jx=1,cts);
    Call set_V(vars,cts);
    Call erase_T(cts);
    Let trans := 0;
    For (j in 1...nqs)
      Let jp1 := (j mod nqs) + 1;
      Let trans := trans | (jx=j) & (prime(jx)=j) & same_j[j]; -- (FP) what are arrays same_j and next_j ?
      Let trans := trans | (jx=j) & (prime(jx)=jp1) & next_j[j]; -- ?? 
    End -- For (j in 1...nqs)
    Call add_disjunct_T(trans,cts);
    Let _s[cts].jn := 0;
    For (j in 1...nps)
      Call add_J(Ji(j,1),cts);
    End -- For (j in 1...nps)
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
  For (j in 1...nqs)
    Call Temp_Entail(1,Ji(j,2),cts);
--    Call Temp_Entail_tl(1,Ji(j,2),cts);
    If (_reply=0)
      Print "\n","Synthesized program fails to satisfy Justice requirement ",
            j,"\n";
      abort;
    End -- If (reply=0)
  End -- For (j in 1...nqs)
End -- check_symb;

To symb_strategy;
-- Compute symbolic strategy
  Let trans12 := trans1 & trans2;
  For (j in 1...nqs)
    Let same_j[j] := 0;
  End -- For (j in 1...nqs)
  For (j in 1...nqs)
    Let jp1 := (j mod nqs) + 1;
    Let next_j[j] := z[j]& trans12 & Ji(j,2) & next(z[jp1]); 
  End -- For (j in 1...nqs)
  For (j in 1...nqs)
    Let low := y[j][1];
    For (r in 2...maxcy[j])
      Let cand := (y[j][r] & !low) & trans12 & next(low);
      Let prev := ((same_j[j] | next_j[j]) forsome prv2);
--        Let prev := (next_j[j] forsome prv2);
--        Let same_j[j] := same_j[j] | (cand & !prev);
      Let same_j[j] := same_j[j] | cand;
      Let low := low | y[j][r];
    End -- For (r in 2...maxcy[j])
  End -- For (j in 1...nqs)
  For (j in 1...nqs)
    Let low := 0;
--    For (r in 2...maxcy[j])
    For (r in 1...maxcy[j])
      For (i in 1...nps)
--        Let cand := x[j][r][i] & trans12 & !Ji(i,1);
      Let cand := x[j][r][i] & !low & trans12 & !Ji(i,1) & next(x[j][r][i]);
--        Let cand := x[j][r][i] & trans12 & !Ji(i,1) & next(x[j][r][i]);
        Let prev := ((same_j[j] | next_j[j]) forsome prv2);
--          Let prev := (next_j[j] forsome prv2);
        Let same_j[j] := same_j[j] | (cand & !prev);
--        Let same_j[j] := same_j[j] | cand;
        Let low := low | x[j][r][i];
      End -- For (i in 1...nps)
    End -- For (r in 1...maxcy[j])
  End -- For (j in 1...nqs)
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
	form p_state;
	Print cts;
    Let candidate := succ1(p_state,cts); -- (FP) What is transition system cts? It is built in function "build_symb"...
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

To optimize_symb;
-- Optimize synthesized program
  Let vjx := vset(jx);
  Let vpjx := vset(next(jx));
  Let prog_vars := set_minus(vars,support(jx));
  Let prog_id := id_of(prog_vars);
  Let reduced := 1;
  Let trans := T(cts);
  Let init_  := I(cts);
  count_states;
--  numstate reacable(cts);
  While (reduced)
    Let reduced := 0;
    For (j1 in 1...nqs)
      For (j2 in 1...nqs)
        If (j1 != j2)
          Let idle := trans & (jx=j1) & prog_id & (next(jx)=j2);
          If (idle)
            Let reduced := 1;
            Let lstate := (idle forsome prv) forsome vjx;
            Let add := 
		((trans & prime(lstate) & (prime(jx)=j1)) forsome vpjx) & 
		(next(jx)=j2);
            Let remove := prime(lstate) & (next(jx)=j1) | lstate & (jx=j1);
            Let add_init := ((init_ & lstate & (jx=j1)) forsome vjx) & (jx=j2);
--	    Print "initial:\n";form init_ & lstate & jx=j1; Print "\n";
--	    Print "projinit:\n";form (init_ & lstate & jx=j1) forsome
--          jx; Print "\n";
--	    Print "add:\n";form add_init;Print "\n";
            Let rem_init := lstate & (jx=j1);
            Let transo := trans;
            Let trans := (trans & !remove) | add;
            Let init_  := (init_ & !rem_init) | add_init;
--	    Print "Result: ",init_,"\n";
            Print "\n","Reduce ",j1," ",j2," ",size(trans),"\n";
            Call set_I(init_,cts);
            Let _s[cts].t[1] := trans;
--            numstate reachable(cts);
            count_states;
--            abort;
          End -- If (idle)
        End -- If (j1 != j2)
      End -- For (j2 in 1...nqs)
    End -- For (j1 in 1...nqs)
  End -- While (reduced)
  Call set_I(init_,cts);
  Let _s[cts].t[1] := trans;
End -- To optimize_symb;

To count_states;
  enumerate_symb;
  Let ntrans := 0;
  For (i in 1...auto_size)
    Let ntrans := ntrans + auto_ns[i];
  End -- For (i in 1...auto_size)
    Print "\n","Automaton has ",auto_size," states, and ",ntrans,
  " transitions\n";
End -- coun_states

Func min_rank(state,gj);
  For (r in 1...maxcy[gj])
    If (y[gj][r] & state)
      Return r;
    End -- If (y[gj][r] & state)
  End -- For (r in 1...maxcy[gj])
  Return 0;
End -- min_rank(state,gj);