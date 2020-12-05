-- TS: Transition system package.
--  Create, query and perform algorithms on transition systems.

-- The paramter "tsn", Transition System Number, identifies on
-- which transition system do we want to operate on.

-- Note that an empty transition system has FALSE as a transition
-- relation, and TRUE as an initial condition.  To initialize the
-- transition relation to some expression, you should add it as a
-- disjunct.

----------------------------------------------------------------------
-- The following are various types of transition systems.
-- Setting a transition system to use one of these representations
-- causes a change in the underlying algorithms. 
--
Let DSPLIT := 1;   -- The way tlv creates the transition systems by default.
Let DISJUNCT := 2;


----------------------------------------------------------------------
-- Setting and getting current TS.


-- Set current ts. Parameter can be system name, or number.
-- Many other functions use the current transition system.
To set_curr_ts '_name;

  -- Check if _name is a number, evaluate it, else get number from system
  -- name
  Case (root(_name))
    "number" : Local _eval := _name;  
     default : Local _eval := sys_num(_name); 
  End

  If (_eval > 0 & _eval <= _s.top )
       Let _s.cur := _eval;
  Else
      Print "Error: set_curr_ts: transition system ", '_name, 
            " does not exist!\n",
            "Current transition system was not changed\n";
  End
  
End

-- Set to current transition system, but put old transition system number
-- on a stack so we can recover it.
To push_curr_ts '_name;
    push _s.curr_tsn_stack, _s.cur;
    set_curr_ts _name;
End

-- pop old tsn from stack.
To pop_curr_ts;
   Let _s.cur := pop(_s.curr_tsn_stack);
End


-- Return current ts number
Func get_curr_ts();
  Return _s.cur;
End


----------------------------------------------------------------------
-- Getting information about the total number of transition systems.


-- Return number of transition systems which currently exist.
Func get_num_ts();
  Return _s.top;
End

-- Return number of transition systems which existed right after
-- the smv file was loaded. This tells us how many systems there
-- were in the smv file.
Func get_num_sys();
  Return _s.n;
End


----------------------------------------------------------------------
-- Creating new transition systems, and filling them with content.


-- Get ID number for a new transition system.
Func new_ts(type := DISJUNCT);
  Let _s.top := _s.top + 1;

  Let _s[_s.top].type := type;

  -- Initialize components
  Let _s[_s.top].tn := 0;
  Let _s[_s.top].jn := 0;
  Let _s[_s.top].cn := 0;

  Let _s[_s.top].i := TRUE;
  Let _s[_s.top].v := TRUE;

  Return _s.top;
End


-- Copy one transition system to another existing transition system
To copy_ts to, from;
  rcopy _s[to], _s[from];
End

-- Return a new copy of an existsing ts.
Func copy_ts(tsn := _s.cur);
  Local new_ts := new_ts();
  rcopy _s[new_ts], _s[tsn];
  Return new_ts;
End


Proc delete_last_ts(); 

  -- Delete transition.

  For (i in 1..._s[_s.top].tn)
    If (_s[_s.top].type = DSPLIT)
      delvar _s[_s.top].t_comb[i];
      delvar _s[_s.top].t_pres[i];
    End
    delvar _s[_s.top].t[i];
  End

  delvar _s[_s.top].tn;

  -- Delete fairness arrays.

  For (i in 1..._s[_s.top].jn)
    delvar _s[_s.top].j[i];
  End

  delvar _s[_s.top].jn;

  For (i in 1..._s[_s.top].cn)
    delvar _s[_s.top].cp[i];
    delvar _s[_s.top].cq[i];
  End

  delvar _s[_s.top].cn;

  -- Delete other elements.

  delvar _s[_s.top].i;
  delvar _s[_s.top].v;
  delvar _s[_s.top].type;

  Let _s.top := _s.top - 1;
End

----------------------------------------------------------------------
-- Setting, and getting components of transition systems.


---------- Initial condition

To set_I _i, tsn := _s.cur;
  Let _s[tsn].i := _i;
End -- To set_I _i, tsn := _s.cur;


Func I(tsn := _s.cur);
  Return _s[tsn].i;
End

---------- Variables

To set_V v, tsn := _s.cur;
  Let _s[tsn].v := v;
End -- To set_V v, tsn := _s.cur;

To add_V v, tsn := _s.cur;
  Let _s[tsn].v := set_union(_s[tsn].v, v);
End -- To add_V v, tsn := _s.cur;


Func V(tsn := _s.cur);
  Return _s[tsn].v;
End


---------- Owned

To set_O o, tsn := _s.cur;
  Let _s[tsn].o := o;
End -- To set_O o, tsn := _s.cur;

To add_O o, tsn := _s.cur;
  Let _s[tsn].o := set_union(_s[tsn].o, o);
End -- To add_O o, tsn := _s.cur;

Func owned(tsn := _s.cur);
  If (exist(_s[tsn].o))
    Return _s[tsn].o;
  Else
    Return 1;
  End
End


---------- Setting transition

--  Add conjuncts and disjuncts to TS.

To add_disjunct_T _t, tsn := _s.cur;
  If ( _s[tsn].type = DISJUNCT)
    Let _s[tsn].tn := _s[tsn].tn + 1;
    Local i := _s[tsn].tn;
    Let _s[tsn].t[i]      := _t;
  Else
    add_split_T _t,TRUE, TRUE, tsn;
  End
End -- To add_disjunct_T _t, tsn := _s.cur;


To add_conjunct_T _t, tsn := _s.cur;
  For (i in 1..._s[tsn].tn)
    Let _s[tsn].t[i] := _s[tsn].t[i] & _t;
  End
End -- To add_conjunct_T _t, tsn := _s.cur;


-- Only used for type DSPLIT.
To add_split_T seq, comb, pres, tsn := _s.cur;
  Let _s[tsn].tn := _s[tsn].tn + 1;
  Local i := _s[tsn].tn;

  Let _s[tsn].t[i]      := seq;
  Let _s[tsn].t_comb[i] := comb;
  Let _s[tsn].t_pres[i] := pres;
End -- To add_split_T seq, comb, pres, tsn := _s.cur;


-------- Getting transition

-- Return i-th component of transition system.
Func Ti(i, tsn := _s.cur);
  If (_s[tsn].type = DSPLIT)
    Return _s[tsn].t[i] &  _s[tsn].t_comb[i] &  _s[tsn].t_pres[i];
  Else
    Return _s[tsn].t[i];
  End
End

-- Get number of components
Func nT(tsn := _s.cur);
    Return _s[tsn].tn;
End


-- Return total transition relation.
Func T(tsn := _s.cur);

  Local total := FALSE;
  For (i in 1..._s[tsn].tn)
      Let total := total | Ti(i, tsn);
  End

  Return total;
End

---------- Justice

-- Add justice requirement to a system.
To add_J _j, tsn := _s.cur;
  Let _s[tsn].jn := _s[tsn].jn + 1;
  Let _s[tsn].j[ _s[tsn].jn ] := _j;
End -- To add_J _j, tsn := _s.cur;

-- Remove last justice requirement which was added.
To pop_J tsn := _s.cur;
  delvar _s[tsn].j[ _s[tsn].jn ];
  Let _s[tsn].jn := _s[tsn].jn - 1;
End -- To pop_J tsn := _s.cur;

-- Get justice requirement i of a system.
Func Ji(i, tsn := _s.cur);
  Return _s[tsn].j[i];
End

-- Number of justice requirements of a system.
Func nJ(tsn := _s.cur);
  Return _s[tsn].jn;
End

-- Append justice requirements from one system to another.
To append_J to, from;
  Local nj := nJ(from);
  For (i in 1...nj)
      add_J  Ji(i,from), to;
  End
End

---------- Compassion

-- Add compassion requirement.
To add_C  _cp, _cq, tsn := _s.cur;
  Let _s[tsn].cn := _s[tsn].cn + 1;
  Let _s[tsn].cp[ _s[tsn].cn ] := _cp ;
  Let _s[tsn].cq[ _s[tsn].cn ] := _cq ;
End

-- Get compassion requirement i of a system.
Func Cpi(i, tsn := _s.cur);
  Return _s[tsn].cp[i];
End

Func Cqi(i, tsn := _s.cur);
  Return _s[tsn].cq[i];
End

-- Get number of compassion requirements of a system.
Func nC( tsn := _s.cur );
  Return _s[tsn].cn;
End

To append_C to, from;
  Local nc := nC(from);
  For (i in 1...nc)
      add_C  Cpi(i,from), Cqi(i,from), to;
  End
End

-- Remove last compassion requirement which was added.
To pop_C tsn := _s.cur;
  If (_s[tsn].cn > 0)
    delvar _s[tsn].cp[ _s[tsn].cn ];
    delvar _s[tsn].cq[ _s[tsn].cn ];
    Let _s[tsn].cn := _s[tsn].cn - 1;
  End
End -- To pop_C tsn := _s.cur;

----------------------------------------------------------------------

To append_fairness to, from;
    append_J to, from;
    append_C to, from;
End

----------------------------------------------------------------------
-- Manipulate the structure of the transition system


-- Change type of transition system.
To set_type type, tsn := _s.cur;

  If (type = DISJUNCT & _s[tsn].type = DSPLIT)
      For (i in 1...nT(tsn))
        Let _s[tsn].t[i] := Ti(i,tsn);
      End
  Else
      If (_s[tsn].type != type)
        -- The user wants to convert to DSPLIT.
        -- This routine doesn't handle this.
        Print "Can't convert from current type to new type\n";
      End
  End
 
End -- To set_type type, tsn := _s.cur;

-- Make transition relation be FALSE.
To erase_T tsn := _s.cur ;
    Let _s[tsn].tn := 0;
End

-- Returns new system which is equivalent to the system identied
-- by the "tsn" parameter, but which has more disjunctive components
-- which may improve performance. The first parameter
-- is an array according to which the disjunction is made.
--
-- If the array doesn't cover all possible states, then the rest
-- of the states are generated automatically.
Func disjunct (&arr, tsn := _s.cur);
  Local new_tsn := copy_ts(tsn);
   
  erase_T new_tsn;

  Local disjunct_arr := FALSE;

  -- Iterate over all transition components.
  For (i in 1...nT(tsn))

      -- Add disjuncts for Ti.
      For (disj in 1...length(arr))
          add_disjunct_T Ti(i, tsn) & arr[disj], new_tsn;
          Let disjunct_arr := disjunct_arr | arr[disj];
      End

      -- State space not covered by "arr".
      Local whats_left := !disjunct_arr;

      If (whats_left)
          add_disjunct_T Ti(i, tsn) & whats_left, new_tsn;
      End

  End

  Return new_tsn;
End 



-- Modify transition system, by adding idling transitions where the
-- transition doesn't generate successors.

To add_idle tsn;
  
  -- Find states which do *NOT* have a succssor.
  Local no_succ := no_successors( TRUE, tsn);

  -- Extend transition by adding idling transitions for
  -- all states with no successors.
  If (no_succ)
      add_disjunct_T  no_succ & id_of(V(tsn)), tsn;
  End
End -- To add_idle tsn;


----------------------------------------------------------------------
-- Finding successors or predecessors of transition systems.

-- s : set of states
Func pred1(s, tsn := _s.cur); 
  Local result := 0;

  For (i in 1..._s[tsn].tn)
    Let result := result | pred(Ti(i, tsn), s);
  End
  Return result;
End

-- s : set of states
Func succ1(s, tsn := _s.cur);
  Local result := 0;
  For (i in 1..._s[tsn].tn)
    Let result := result | succ(Ti(i, tsn), s);
  End
  Return result;
End

-- Return the subset of "state" which has no successors.
Func no_successors(state, tsn := _s.cur);
  Local has_succs := (state & T(tsn)) forsome prime(V(tsn));
  Return state & ! has_succs;
End

-- Return the subset of "state" which has successors to "to".
Func has_successors_to(state, to, tsn := _s.cur);
  Local result := 0;
  Local state_and_primed_to := state & prime(to);

  For (i in 1..._s[tsn].tn)
    Let result := result | 
      ((state_and_primed_to & Ti(i, tsn)) forsome prime(V(tsn)));
  End
  Return result;
End

-- Compute multiple-step succecessors
Func successors(set, tsn := _s.cur);
  Local closure := set;
  Local front := set;

  Fix (closure)
    Let front := succ1(front, tsn) & !closure ;
    Let closure := closure | front;
  End
  Return closure;
End

-- Compute multiple-step predecessors
Func predecessors(set, tsn := _s.cur);
  Local closure := set;
  Local front := set;

  Fix (closure)
    Let front := pred1(front, tsn) & !closure ;
    Let closure := closure | front;
  End
  Return closure;
End

Func reachable(tsn := _s.cur);
  Return successors(I(tsn), tsn);
End


----------------------------------------------------------------------

-- Return a satisfying assignment of the conjunction of the parameter,
-- and the transition of the transition system.
-- The meaning of the word "refute" is to prove to be false by
-- argument or evidence

Func refute_T(conj, tsn := _s.cur);
  Local temp;
  For (i in 1...nT(tsn))
    Let temp := conj &&& Ti(i, tsn);
      If (temp)
        Return temp;
      End
  End
  -- No refutation found.
  Return FALSE;
End

Func refute_T2(conja, conjb, tsn := _s.cur);
  Local temp;
  For (i in 1...nT(tsn))
    Let temp1 := conja & Ti(i,tsn);
    Let temp := temp1 &&& conjb;
    If (temp)
      Return temp;
    End
  End
  -- No refutation found.
  Return FALSE;
End

----------------------------------------------------------------------
-- Composing two systems into one.


--To compose_all_but_trans ts1, ts2, ts3;
--End

-- Compose synchronously and return new transition system.
Func sync (ts2, ts3);
  -- Allocate new transition system.
  Local new_ts := new_ts(DISJUNCT);

  -- Determine which system has more components. We want the 
  -- new system to be based on that system so it will contain
  -- the most components. We will use the total of the other system 
  -- to conjunct the transition relation.
  If (nT(ts2) < nT(ts3))
    Local total_system := ts2;
    Local nontotal_system := ts3; 
  Else
    Local total_system := ts3;
    Local nontotal_system := ts2;
  End

  -- Make the new system based on the non total system, for
  -- performance considerations.
  rcopy _s[new_ts], _s[nontotal_system];
  
  -- Conjunct transition.
  add_conjunct_T T(total_system), new_ts;

  -- Set variable set and initial condition.
  add_V V(total_system), new_ts;
  set_I I(new_ts) & I(total_system), new_ts;

  -- Append fairness requirements from the system which is left to compose.
  append_fairness new_ts, total_system;

  Return new_ts;  
End


-- Compose synchronously and return new transition system.
Func async(ts1,ts2);

  Local new_ts := copy_ts(ts1);  

  --
  -- Calculate transition:
  --  T_1 & pres(V_2 - V_1)  | T_2 & pres(V_1 - V_2)
  --

  -- Make the transition of new_ts be:   T_1 & pres(V_2 - V_1) . 
  add_conjunct_T  id_of( set_minus( V(ts2),V(ts1) ) ), new_ts  ;

  -- Add dijuncts of :    T_2 & pres(V_1 - V_2)
  Local pres2 := id_of( set_minus( V(ts1),V(ts2) ) );
  For (i in 1...nT(ts2))
      add_disjunct_T Ti(i, ts2) & pres2, new_ts;
  End


  -- Set variable set and initial condition.
  add_V  V(ts2), new_ts ;
  set_I  I(new_ts) & I(ts2), new_ts;

  -- Append fairness requirements from the system which is left to compose.
  append_fairness new_ts, ts2;

  Return new_ts;
End

----------------------------------------------------------------------
-- Temporarily restricts the transition relation.
--
-- We mark a transition relation which is restricted by creating
-- a dynamic variable inside the transition system, named "restrict".
-- The original transition system is copied to the array "restrict".
-- NOTE: Restrictions should not be nested. A call to unrestrict restores the
--   TS to how it was prior to the last performed restriction. So 2 consecutive
--   calls to 'unrestrict' are meaningless.

-- Perform Rel & res(V,V').  Restrict with a relation.
To restrict_rel res, tsn := _s.cur;
  If (! exist(_s[tsn].restrict) )
    -- If this is the first time we are performing restriction,
    -- then copy the original transition system elsewhere.
    rcopy _restrict[tsn].t, _s[tsn].t;
    If (_s[tsn].type = DSPLIT)
       rcopy _restrict[tsn].t_comb, _s[tsn].t_comb;
       rcopy _restrict[tsn].t_pres, _s[tsn].t_pres;
    End

    Let _s[tsn].restrict := 1;
  End

  -- Perform restriction.
  Call add_conjunct_T(res, tsn);
End -- To restrict_rel res, tsn := _s.cur;

-- Perform Rel & (U X V).  Restrict with pre and post states.
To restrict pre, post, tsn := _s.cur;
  restrict_rel pre & next(post), tsn;
End -- To restrict pre, post, tsn := _s.cur;

-- Restore original transition.
To unrestrict tsn := _s.cur;
  If (exist(_s[tsn].restrict) )

      -- Copy transition back.
      rcopy _s[tsn].t, _restrict[tsn].t;
      If (_s[tsn].type = DSPLIT)
          rcopy _s[tsn].t_comb, _restrict[tsn].t_comb ;
          rcopy _s[tsn].t_pres, _restrict[tsn].t_pres ;
      End

      delvar _s[tsn].restrict;
  Else
--      Print "Error: no need to unrestrict unrestricted transition system\n";
      Let tsn := tsn;
  End
End

----------------------------------------------------------------------

----------------------------------------------------------------------
-- INTERNAL procedure
-- Add state to path in array, but only if transition to new state
-- isn't idling. 
To add_state_if_non_idling_path &arr, state;
    If (length(arr) = 0 | top(arr) != state)
      push arr, state;
    End
End

----------------------------------------------------------------------
--  Compute the shortest path from source to destination using tsn as
--  the transition system. The result is appended to array
--  arr starting from item no arr[0] .
--
-- Algorithm from: Yonit Kesten, Amir Pnueli, Li-on Raviv, Elad Shahar,
-- "Model Checking with Strong Fairness".
-- 
Proc path(source, destination, & arr, tsn);

  Local pos := 1;
  Local bp[1] := destination;
 
  While ( is_false(bp[pos] & source) )
    Local bp[pos + 1] := bp[pos] | pred1(bp[pos],tsn);

    If ( is_equal(bp[pos], bp[pos + 1]) )
       Print "There is no path from source to destination for system ", tsn,"\n";
       Print "Check the global variables src, dest\n";
       Let src := source;
       Let dest := destination;
       Return;
    End

    Let pos := pos + 1;
  End

  Local s := fsat(bp[pos] & source, V(tsn));
 
  add_state_if_non_idling_path arr, s;

  While (pos > 1)
    Let pos := pos - 1;
    Let s := fsat( succ1(s,tsn) & bp[pos], V(tsn));

    add_state_if_non_idling_path arr, s;
  End

End -- path

----------------------------------------------------------------------

-- FOR INTERNAL use.
-- Iterate over systems and check whether there
-- were any ltl formulas which were defined for the systems. 
-- Create testers for them and compose with the system.
To compose_defined_ltl;

  -- Loop over the systems
  For ( sn in 1..._sn )

    If ( exist(_ltl_n[sn]) )
        If ( _ltl_n[sn] > 0 )
          Print "Composing defined for system ", sn, "\n";

          -- Compute conjunction of all ltl defined formulas into the
          -- dynamic variable "andresult".
          Let 'andresult := _ltl_exp[sn][1];
          For ( i in 2..._ltl_n[sn] )
              Let 'andresult := and(andresult, _ltl_exp[sn][i]);
          End

          -- Create tester for the ltl formulas. The tester should use
          -- the auxiliary variables, which correspond to ltl
          -- formulas, which appear in system sn, and should create a
          -- weak initial condition (as indicated by third parameter.
          Local tester :=  create_tester(andresult , 1, sn);     
                         
          -- Compose tester with system.
          Local new_ts := sync(sn, tester);
          Call copy_ts(sn, new_ts);

          delete_last_ts; -- Delete transition system "new_ts".
          delete_last_ts; -- Delete transition system "tester".
        End
    End

  End  -- End loop over systems.
End

----------------------------------------------------------------------
-- Converting dynamic variables to work with TS.tlv
-- For INTERNAL use.
To convert_old_tlv_to_TS type ;

  Local _curr_t := 0;
  Local _curr_just := 0;
  Local _curr_comp := 0;

  Local new_ts;

  -- Loop over all systems.
  For (si in 1..._sn )
    
    Let new_ts := new_ts(type);  -- NEW transition system.

    -- Copy initial condition, and additional constants.
    Call set_I(_i[si], new_ts);
    Call set_V(_vars[si], new_ts);
   
    -- Copy transition relation
    For (i in 1..._tn[si])
      If (type = DSPLIT)
        Call add_split_T(_t[_curr_t + i], _d[_curr_t + i], _pres[_curr_t + i],
                         new_ts);
      Else
        Call add_disjunct_T(_t[_curr_t + i] & _d[_curr_t + i] &
                            _pres[_curr_t + i], new_ts);
      End
    End 

    -- Copy justice
    For (i in 1..._jn[si])
      Call add_J(_j[_curr_just + i], new_ts);
    End

    -- Copy compassion
    For (i in 1..._cn[si])
      Call add_C(_cp[_curr_comp + i], _cq[_curr_comp + i], new_ts);
    End

    -- Keep track of where the next justice, compassion and transitions are.
    Let _curr_t    := _curr_t    + _tn[si];
    Let _curr_just := _curr_just + _jn[si];
    Let _curr_comp := _curr_comp + _cn[si];

    If (exist(own[si]))
      Let _s[si].o := own[si];
    End
  End

End
----------------------------------------------------------------------


-- Call this from Rules.tlv, to initialize TS.
To init_TS;

   -- If the structure used by this file does not exists, then create it.
  If ( ! exist(_s.n) )
     Let _s.n := _sn;   -- Number of last system.
     Let _s.top := 0;   -- The TS package only changes _s.top, and never _s.n .   

     -- The parameter is the type the new systems will be: DISJUNCT or DSPLIT
     convert_old_tlv_to_TS(DISJUNCT);  
  Else
     Let _s.top := _s.n; 
  End

  Let _s.cur := 1;   -- Current system.

  -- Compose defined ltl expressions into the transition systems.
  compose_defined_ltl;
End
