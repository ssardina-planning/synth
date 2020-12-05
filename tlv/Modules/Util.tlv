Print "Loading Util.tlv $Revision: 4.3 $\n";


-- Test whether a given assertion is empty 
Func empty(set, vars);
  Return !(set forsome vars);
End -- function empty


----------------------------------------------------------------------
-- Functions which return information about Temporal Formulas
--

-- Returns true if the root of the parse tree is a temporal operator.
Func principle_temporal('__p);
 
  Case (root(__p))
   "()","<>","[]","(~)","(_)","<_>","[_]",
   "Since", "Until", "Awaits", "Backto":  Return 1;
  End
 
  Return 0;
End


-- Try to find out whether the formula is ctl.
-- We do this by finding if any of the ctl operators exist.
Func is_ctl('p);
    Case (root(p))
    "EX",   "AX",   "EF",   "AF",   "EG",   "AG",  "AU" ,  "EU" : 
         Return 1;
    "!": Return is_ctl(op(1,p));

    "|", "&", "->", "<->" :
         If (is_ctl(op(1,p)))
             Return 1;
         Else
             Return is_ctl(op(2,p));
         End
    End

    Return 0;
End


----------------------------------------------------------------------
-- DEBUGGING routines


-- Print all satifsying assignments.
To print_sat e;
  Local s;
 
  While(e)
    Let s := sat(e);
    Print s;
    Let e := e & !s;
--    Let e := case
--               !s =0 : 0;
--               1     : e;
--             esac;
  End
End

To print_fsat e;
   Local s;
   While(e)
    Let s := fsat(e);
    Print s;
    Let e := e & !s;
  End
End


----------------------------------------------------------------------
-- Array functions
--
-- The array is implemented by recording its length at position 0.
-- Arrays handled by using these functions are consider to have length
-- of 1 till arr[0]


-- Clears array.
To new &arr;
   If ( exist(arr[0]) )
       delarr arr;
   End

   Let arr[0] := 0;
End

-- Delete an array.
To delarr &arr;
   For (i in 1...arr[0])
      delvar arr[i];
   End

   delvar arr[0];
End

To push &arr, val;
   If ( ! exist(arr[0]) )
     Let arr[0] := 0;
   End

   Let arr[0] := arr[0] + 1;
   Let arr[arr[0]] := val;
End


Func pop(&arr);
   If ( arr[0] )
     Local result := top(arr);
     delvar arr[arr[0]];
     Let arr[0] := arr[0] - 1;

     Return result;
   Else
     Print "Warning: stack is empty\n";
     Return -1;
   End
End

Func top(&arr);
   Return arr[arr[0]];
End

Func length(&arr);
   Return arr[0];
End


-- Append arr2 to arr1
To append &arr1, &arr2;
  Local len := length(arr2);
  For (i in 1...len) 
    push arr1, arr2[i];
  End
End

-- copy arr2 to arr1
To copy &arr1, &arr2;
  new arr1 ;
  For (i in 1...length(arr2)) 
    push arr1, arr2[i];
  End
End

-- Print the array
To printarr &arr;
  For (i in 1...length(arr)) 
    Print arr[i], "\n";
  End
End


----------------------------------------------------------------------
-- Hash functions
--
-- These functions associate a bdd to a parse tree expression.
-- It is implemented as two arrays, one with the parse tree expressions,
-- and the other with the corresponding bdds.

To new_hash &hash;
  Let hash.top := 0;
  Let hash.success := 0;
End


To insert_hash &hash, 'key, bddval;
  Let hash.top := hash.top + 1;
  Let 'hash.key[hash.top] := key;
  Let hash.val[hash.top] := bddval;
End


Func value_of_hash(&hash, 'key);

  For (i in 1...hash.top)
    If (hash.key[i] == key) 
      Let hash.success := 1;
      Return hash.val[i];
    End
  End

  Let hash.success := 0;
  Return 0;
End


-- Returns true if last "value_of_hash" succeded.
Func success_hash(&hash);

  If ( exist(hash.success) )
      Return hash.success;
  Else
      Return 0;
  End
End


-- Delete hash.   You cannot insert into a hash after it is deleted.
To delhash &hash;
  For (i in 1...hash.top)
    delvar hash.key[i];
    delvar hash.val[i];
  End

  delvar hash.success;
  delvar hash.top;
End

