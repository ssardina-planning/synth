-- Rules for checking CTL with fairness based on Li-On's algorithm.
-- These have been checked on the dining philosophers problem for various
-- number of philosiphers (up to 9).
-- 
-- No fairness:
--        Future:
--              cex(p), cef(p), ceg(p), ceu(p,q), cew(p,q)
--              cax(p), caf(p), cag(p), cau(p,q), caw(p,q)
--        Past:
--              cey(p), cep(p) 
--
--    Where a suffix "u" is for Until, and a suffix "w" is
--    for While, where :      p While q == (p Until q) | eg(p) )
--
--    cep is Like cef, but for past
--
-- Fairness: 
--        ce_fair_g(p): handles both justice and compassion using Lions algorithm
--
--        EfX(p), EfU(,q), EfG(p), EfF(p), AfX(p), AfU(p,q), AfG(p), AfF(p) ( justice only )
--
--        agptoafq(p,q): states satisfying AG(p --> AF q) over fair paths
--
--
--
-- mcctl(): function to wrap around calls to ctl. For example to verify that
--          EfG(!error) holds for the program one could do:
--          Run mcctl(EfG(!error));
--         




-- The set of all states which are the start of some fair
-- computation
To clear_ctlfair;
   Let ctlfair := -1;
End

To calc_ctlfair tsn := _s.cur ;
  If (ctlfair = -1)
    Let ctlfair := ce_fair_g(TRUE, tsn);
  End
End



--
--
-- Model checking (no fairness)
--
--

Func cex(arg_cex, tsn := _s.cur);
  Return pred1(arg_cex, tsn);
End -- function cex.

Func cef(arg_cef, tsn := _s.cur);
  Return predecessors(arg_cef, tsn);
End -- cef

Func ceg(arg_ceg, tsn := _s.cur);

  Local new := arg_ceg;
  Fix ( new )
    Let new := new & cex(new, tsn);
  End 

  Return new;
End -- ceg

Func ceu(p_ceu,q_ceu, tsn := _s.cur);

  Local new := q_ceu;
  Fix ( new )
    Let new := new | (p_ceu & cex(new, tsn));
  End

  Return new;
End -- ceu

Func cew(p_cew,q_cew, tsn := _s.cur);
  Return ceu(p_cew,q_cew, tsn) | ceg(p_cew, tsn);
End -- cew

Func cax(p_cax, tsn := _s.cur);
  Return !cex(!p_cax, tsn);
End -- cax

Func caf(p_caf, tsn := _s.cur);
  Return !ceg(!p_caf, tsn);
End -- caf

Func cag(p_cag, tsn := _s.cur);
  Return !cef(!p_cag, tsn);
End -- cag

Func cau(p_cau,q_cau, tsn := _s.cur);
  Return !cew(!q_cau,(!p_cau) & !(q_cau), tsn);
End -- cau

Func caw(p_caw,q_caw, tsn := _s.cur);
  Return !ceu(!q_caw,(!p_caw) & (!q_caw), tsn);
End -- caw

Func cey(arg_cey, tsn := _s.cur);
  Return succ1(arg_cey);
End -- function cey.

Func cep(arg_cep, tsn := _s.cur);
  Return successors(arg_cep, tsn);
End -- cep


--
--
--  Dealing with FAIRNESS
--
--

-- Standard model-checking function ce_fair_gj(p) for check \E_fair\G p
--           using only justice.

Func ce_fair_gj(p_ce_fair_gj, tsn := _s.cur);
  Local old_z := FALSE;
  Local new_z := TRUE;

  While (!(old_z = new_z))
    Let old_z := new_z;
    Let new_z := p_ce_fair_gj;

    For (counter in reverse 1...nJ(tsn))
      Let new_z := new_z & cex(ceu(p_ce_fair_gj, Ji(counter, tsn) & old_z, tsn), tsn);
    End 

  End -- while (!(old_z = new_z))

  Return new_z;

End -- ce_fair_gj




--- Li-on's ce_lfair_g package

-- Compute all accessible states satisfying e_fair_g p

Func ce_fair_g(p_ce_lfair_g, tsn := _s.cur);

  Local new := reachable(tsn) & p_ce_lfair_g;
  Local old := FALSE;
  Local counter;

  restrict new, new, tsn ;

  While (!(new = old))

    Let old := new;

    Let counter := nJ(tsn);
    While (counter)
      Let new := new & Ji(counter);
      Let new := predecessors(new, tsn) & successors(new, tsn);
      Print "justice No. ", counter,"\n";

      restrict new,new, tsn;

      Let counter := counter - 1;
    End -- while(counter)

    Let counter := nC(tsn);
    While (counter)
      Let temp := new & Cqi(counter);    
      Let temp := predecessors(temp, tsn) & successors(temp, tsn);
      Let new := temp | (new & !Cpi(counter));
      Print "compassion No. ", counter,"\n";

      restrict new,new, tsn;

      Let counter := counter - 1;
    End -- while(counter);

    unrestrict tsn;

    Let new := new & succ(new, tsn) & pred(new, tsn);

    restrict new,new, tsn;  
 
  End -- While

  unrestrict tsn;

  Return ceu(p_ce_lfair_g, new, tsn);

End -- ce_fair_g


--------------------

Func EfG(p, tsn := _s.cur);
  Return ce_fair_gj(p, tsn);
End

Func EfX(p, tsn := _s.cur);
  Run calc_ctlfair;
  Return cex(p & ctlfair, tsn);
End

Func EfF(p, tsn := _s.cur);
  Return EfU(TRUE,p, tsn);
End

Func EfU(p,q, tsn := _s.cur);
  Run calc_ctlfair;
  Return ceu(p, q & ctlfair, tsn);
End


Func AfX(p, tsn := _s.cur);
  Return !EfX(!p, tsn);
End 

Func AfF(p, tsn := _s.cur);
  Return !EfG(!p, tsn);
End 

Func AfG(p, tsn := _s.cur);
  Return !EfF(!p, tsn);
End 

Func AfU(p,q, tsn := _s.cur);
  Return !EfU(!q,!p & !q, tsn) &
         !EfG(!q, tsn);
End 


--------------------

-- Return all (accessible) states satisfying AG(p --> AF q) over fair paths
Func agptoafq(p,q, tsn := _s.cur);
  Return cag(!p | AfF(q, tsn), tsn);
End 


----------------------------------------------------------------------
-- Wraparound for ctl model checking routines.
To mcctl_old p, tsn := _s.cur;
  If ( !(_i -> p))
    Print "The formula is NOT valid\n";
  Else
    Print "The formula is valid!!\n";  
  End
End


-- Recursively evaluate the set of states for which the ctl
-- formula holds.
Func mcctl_aux('p, tsn);

  -- Recursively evaluate subformulas.
  Case (root(p))
  "!",  
  "EX",   "AX",   "EF",   "AF",   "EG",   "AG": 
     -- Unary opertors.
     Local res1 := mcctl_aux(op(1,p),tsn);

  "&" ,  "|"  ,  "->" ,  "<->",  "AU" ,  "EU" :
     -- Binary opertors.
     Local res1 := mcctl_aux(op(1,p),tsn);
     Local res2 := mcctl_aux(op(2,p),tsn);     
  End


  -- Combine results of subformulas.
  Case (root(p))
  "!"  : Return ! res1;
  "EX" : Return EfX(res1, tsn);
  "AX" : Return AfX(res1, tsn);
  "EF" : Return EfF(res1, tsn);
  "AF" : Return AfF(res1, tsn);
  "EG" : Return EfG(res1, tsn);
  "AG" : Return AfG(res1, tsn);

  "&"  : Return res1 & res2; 
  "|"  : Return res1 | res2; 
  "->" : Return res1 -> res2; 
  "<->": Return res1 <-> res2; 
  "EU" : Return EfU(res1, res2, tsn);
  "AU" : Return AfU(res1, res2, tsn);
  End

  -- If we have reached here then p is probably an indentifier.
  -- We just evaluate it and return it.
  Return p;

End


To mcctl 'p, tsn := _s.cur;

  clear_ctlfair;
  Local result := mcctl_aux(p, tsn);

  If ( !(_i -> result))
    Print "The formula is NOT valid\n";
  Else
    Print "The formula is valid!!\n";  
  End
End
