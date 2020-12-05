#$Id: Synthesizer.pm,v 1.27 2007/04/13 09:19:01 rbloem Exp $
package Synthesizer;

return 1;

use Cudd;
use CFGParser; # our parser
use BDDModule;
use strict;
use POSIX; # qw(ceil floor);

#----------------------------------------------------------------------
# Constructor
sub new
{
  my $class = shift;
  
  my $object = {
    parser_module => CFGParser->new(),
    bdd_module => BDDModule->new(),
    bdds => {},
    reachable_states => 0,
    winning_states => 0
  };

  bless $object, $class;
  return $object;
}

#----------------------------------------------------------------------
# Run the whole program. This will invoke the parser, and hand over
# the result to the bdd.
#
# @param The name of the configuration file
sub readConfiguration {
  my $this = shift;
  my $cfg_file_name = shift;
  my $use_configured = shift || 0;
  
  my $parser_module = $$this{parser_module};
  $parser_module->setConfigFile($cfg_file_name);
  $parser_module->parse();

  my $var_ordering;
  if($use_configured) {
    $var_ordering = $parser_module->getOrdering();
  }

  $$this{bdd_module}->initialize($parser_module->getInputVariables(),
                                 $parser_module->getOutputVariables(),
				 {},
                                 $var_ordering);

  my @all_keys = keys (%{$$parser_module{parse_trees}});
  foreach my $key (@all_keys)
  {
    print "Generated Bdds for $key\n";
    foreach my $syntax_tree (@{$$parser_module{parse_trees}->{$key}})
    {
      my $bdd = $$this{bdd_module}->createBDD($syntax_tree);
      if($$this{parser_module}->needsConcatenation($key)) {
        my $old_bdd = pop(@{$$this{bdds}->{$key}});
        if(defined($old_bdd)) {
          $bdd = $old_bdd * $bdd;
        }
      }
      push(@{$$this{bdds}->{$key}}, $bdd);
    }
  }

  $$this{bdd_module}->extractInitValuesFromInitialBDDs($$this{bdds}->{ENV_INITIAL},
						       $$this{bdds}->{SYS_INITIAL});
}

#----------------------------------------------------------------------
# returns a hash to the BDDs
sub getBDDs {
  my $this = shift;
  return $$this{bdds};
}

#----------------------------------------------------------------------
# returns the interal bdd manager
sub getManager {
  my $this = shift;
  return $$this{bdd_module};
}

#----------------------------------------------------------------------
# calculates the states, from which the current state can be reached in
# one step.
sub coax {
  my $this = shift;
  my $states = shift;

  my $manager = $$this{bdd_module}->getBDDManager();

  my $env_transitions = $$this{bdds}->{ENV_TRANSITIONS};
  my $sys_transitions = $$this{bdds}->{SYS_TRANSITIONS};
  my $input_vars = $$this{parser_module}->getInputVariables();
  my $output_vars = $$this{parser_module}->getOutputVariables();
  my $var_table = $$this{bdd_module}->getTableOfVars();
  my $input_product = $manager->BddOne;
  my $output_product = $input_product; #$manager->BddOne;
  my $substituted_states = $input_product; #$manager->BddOne;

  #
  foreach my $input_var (@$input_vars) {
    if(exists $$var_table{$input_var}) {
      $input_product = $input_product * @{$$var_table{$input_var}}[1];
    }
  }

  foreach my $output_var (@$output_vars) {
    if(exists $$var_table{$output_var}) {
      $output_product = $output_product * @{$$var_table{$output_var}}[1];
    }
  }

  my $swapped_states = $this->swapPresentNext($states);
#  my $result = Forall $input_product ((!@$env_transitions[0]) + (Exists $output_product (@$sys_transitions[0] * $swapped_states)));
  my $result = Forall $input_product ((!@$env_transitions[0]) + 
                                      Cudd::BDD::AndExists($output_product, @$sys_transitions[0], $swapped_states));

  return $result;
}

#----------------------------------------------------------------------
# swap present state variables and next state variables
sub swapPresentNext {
  my $this = shift;
  my $states = shift;
  my $var_table = $$this{bdd_module}->getTableOfVars();
  my $jx_vars = $this->{bdd_module}->{jx_vars};
  
  my @all_present = ();
  my @all_next    = ();
  
  while( my ($key, $vars) = each %$var_table) {
    push(@all_present, @$vars[0]);
    push(@all_next, @$vars[1]);
  }
  foreach my $vars (values %$jx_vars) {
    push(@all_present, @$vars[0]);
    push(@all_next, @$vars[1]);
  }
  return $states->SwapVariables(\@all_present, \@all_next);
}


#----------------------------------------------------------------------
# Creates a bdd which does "j=(j+1) mod k". So the bdd will do
# 0, 1, 2, ... k, 0, 1, ... k
# param k the modulo value
# returns a new bdd which holds the transition relation for (j=(j+1) mod k) and the zero value as bdd
sub moduloInc {
  my $this = shift;
  my $k = shift;

  my $manager = $$this{bdd_module}->getBDDManager();
  my $bdd_one = $manager->BddOne;
  

  if($k >= 1)
  {
    my $num_of_bits = ceil((log $k)/(log 2));
    if($num_of_bits == 0) {
      $num_of_bits = 1;
    }

    my @present_vars = ();
    my @next_vars = ();

    for(my $i = 0; $i < $num_of_bits; ++$i)
    {
      my ($present, $next) = $$this{bdd_module}->generateJXVar();
      push(@present_vars, $present);
      push(@next_vars, $next);
    }

    my $trans_relation = ((!$next_vars[0]) + ($bdd_one ^ $present_vars[0])) * 
      ((!($bdd_one ^ $present_vars[0])) + $next_vars[0]);


    my $carry = $bdd_one * $present_vars[0];

    for(my $i = 1; $i < $num_of_bits; ++$i)
    {
      $trans_relation = $trans_relation * 
        ((!$next_vars[$i] + ($carry ^ $present_vars[$i])) *
         (!($carry ^ $present_vars[$i]) + $next_vars[$i]));

      $carry = $carry * $present_vars[$i];
    }

    my $reset_condition = $bdd_one;
    my $reset_state = $bdd_one;
    my $start_state = $bdd_one;
    my $bit_selector = $k - 1;
    for(my $i = 0; $i < $num_of_bits; ++$i)
    {
      if(($bit_selector & 0x1) == 1) {
        $reset_condition = $reset_condition * $present_vars[$i];
      }
      else {
        $reset_condition = $reset_condition * !($present_vars[$i]);
      }

      $bit_selector = $bit_selector >> 1;
      $reset_state = $reset_state * !($next_vars[$i]);
      $start_state = $start_state * !($present_vars[$i]);
    }

    my $case_increase = $reset_condition + $trans_relation;
    my $case_reset = (!($reset_condition)) + $reset_state;

    $trans_relation = $case_increase * $case_reset;

    return($trans_relation, $start_state, \@present_vars, \@next_vars, $bdd_one);
  }
  else
  {
    #FIXXXME: is this correct? What shall we do if someone requests transition relation for mod 0 or mod 1?
    return(!($bdd_one), !($bdd_one), !($bdd_one), !($bdd_one), $bdd_one); 
  }
}

#----------------------------------------------------------------------
sub getTableOfVars {
  my $this = shift;
  
  return $$this{bdd_module}->getTableOfVars();
}

#----------------------------------------------------------------------
# implementation of figure 1
sub winm {
  my $this = shift;
  my $env_fairness = $$this{bdds}->{ENV_FAIRNESS};
  my $sys_fairness = $$this{bdds}->{SYS_FAIRNESS};
  my $env_transition = $$this{bdds}->{ENV_TRANSITIONS}[0];
  my $sys_transition = $$this{bdds}->{SYS_TRANSITIONS}[0];

  my $m = 0;
  if(defined(@$env_fairness)) {
    $m = @$env_fairness;
  }

  my $n = 0;
  if(defined(@$sys_fairness)) {
    $n = @$sys_fairness;
  }

#  print "CALCULATE winm for m = ".$m." and n = ".$n."\n";

  my $manager = $$this{bdd_module}->getBDDManager();
  my $onebdd = $manager->BddOne;
  my $zerobdd = !($onebdd);

  my @x_array = ();
  my @y_array = ();
  my @maxr = ();

  my $old_z = $zerobdd;
  my $z = $onebdd;
  while($z != $old_z) # GreatestFixpoint(z)
  {
    $old_z = $z;
#    print "Z=\n";
#    $z->Print(5,2);
    
#    my ($trans_n, $zero_n, $present_vars_n, $next_vars_n, $bddone_n) = $this->moduloInc($n);
    for(my $j = 0; $j < $n; ++$j)
    {
      my $r = 0;

      my $old_y = $onebdd;
      my $y = $zerobdd;
      my $iteration = 0;
      while($y != $old_y) # LeastFixpoint(y)
      {
        $old_y = $y;
#        print "Y" . $iteration++ . "\n";
#        $y->Print(5,2);



        my $start = (@$sys_fairness[$j] * $this->coax($z)) + $this->coax($y);

#         print "sys fairness $j\n";
#         @$sys_fairness[$j]->Print(5,2);
#         print "z: \n";
#         $z->Print(5,2);
#          print "COAX Z\n";
#          $this->coax($z)->Print(5,2);
#          print "COAX Y\n";
#          $this->coax($y)->Print(5,2);
#          print "END COAX\n";
#             print "start\n";
#            $start->Print(6,2);

        $y = $zerobdd;
#        my ($trans_m, $zero_m, $present_vars_m, $next_vars_m, $bddone_m) = $this->moduloInc($m);
        for(my $i = 0; $i < $m; ++$i)
        {
          my $old_x = $zerobdd;
          my $x = $z;
          my $x_counter = 0;
          while($x != $old_x) # GreatestFixpoint(x)
          {
            $old_x = $x;
#            print "X" . $i . "-" . $x_counter++ . "\n" ;
#            $x->Print(5,2);

#            print "env cond $i\n";
#            (@$env_fairness[$i])->Print(6,2);
            $x = $start + ((!(@$env_fairness[$i])) * $this->coax($x));
          } # End -- GreatestFixpoint(x)
          $x_array[$j][$r][$i] = $x;
          $y = $y + $x;
        } # End - For (i in 1...m)
        $y_array[$j][$r] = $y;
        ++$r;
      } # End -- LeastFixpoint(y)
      $z = $y;
      $maxr[$j] = $r - 1;
    } # End -- For (j in 1...n)
  } # End -- GreatestFixpoint(z)

  return ($z, \@x_array, \@y_array, \@maxr);
}


#----------------------------------------------------------------------
# implementation of strategy
sub strategy {
  my $this = shift;
  my $z = shift;
  my $x_array = shift;
  my $y_array = shift;
  my $maxr = shift;

  my $manager = $$this{bdd_module}->getBDDManager();
  my $onebdd = $manager->BddOne;
  my $zerobdd = !($onebdd);

  my $reachable_states = $$this{reachable_states} || $onebdd;

  my $env_fairness = $$this{bdds}->{ENV_FAIRNESS};
  my $sys_fairness = $$this{bdds}->{SYS_FAIRNESS};
  my $env_transition = $$this{bdds}->{ENV_TRANSITIONS}[0];
  my $sys_transition = $$this{bdds}->{SYS_TRANSITIONS}[0];

  my $m = 0;
  if(defined(@$env_fairness)) {
    $m = @$env_fairness;
  }

  my $n = 0;
  if(defined(@$sys_fairness)) {
    $n = @$sys_fairness;
  }

  my $trans12 = $env_transition * $sys_transition;

  my ($mod_trans, $zero, $jx_present_vars, $jx_next_vars) = $this->moduloInc($n);
  my $jp1 = $zero;
  my $orig_mod_trans = $mod_trans;

  my $trans = $zerobdd;

  my $starttime =  (times)[0];
  ##################################
  # Build strategy rho1: everytime system fairness condition i is fulfilled search
  # for the next system fairness condition (i+1 mod n)
  my @rho_list;
  my $rho1 = $zerobdd;
  for(my $j = 0; $j < $n; ++$j)
  {
    my $z_next = $this->swapPresentNext($z);
    my $jx_equal_j = $jp1;    #present state vars of jx = $j
    
    $jp1 = $mod_trans / $jp1; #compute jx+1 mod n
    my $tmp_rho1 = ($jx_equal_j * $z * @$sys_fairness[$j] * $trans12 * $z_next * $jp1);
    
    push(@rho_list, $tmp_rho1);
    $rho1 = $rho1 + $tmp_rho1;
    
    $jp1 = $jp1->SwapVariables($jx_present_vars, $jx_next_vars);
  }
  $trans = $trans + $rho1;


  my $endtime =  (times)[0];
  printf "   Time of Rho1 \t\t%10.2f seconds\n", ($endtime - $starttime);
  $starttime =  (times)[0];
  
  ##################################
  # Build startegy rho2: if we search for system fairness condition i, we go one
  # step close (according to the onionrings)
  $jp1 = $zero;
  my $rho2 = $zerobdd;
  for(my $j = 0; $j < $n; ++$j)
  {
    my $low = $$y_array[$j][0];
    
    my $jx_equal_j = $jp1; #present state vars equal j
    #next state vars equal j:
    $jp1 = $jp1->SwapVariables($jx_present_vars, $jx_next_vars); 

    for(my $r = 1; $r < @$maxr[$j]; ++$r)
    {
      my $next_low = $this->swapPresentNext($low);

      my $tmp_rho2 = ($jx_equal_j * ($$y_array[$j][$r]->Restrict($reachable_states)) * 
                    ((!$low)->Restrict($reachable_states)) * $trans12 * $next_low * $jp1);
      push(@rho_list, $tmp_rho2);
      $rho2 = $rho2 + $tmp_rho2;

      $low = $low + $$y_array[$j][$r];
    }

    #increase jp1 by 1 (mod n)
    $jp1 = $jp1->SwapVariables($jx_next_vars, $jx_present_vars);
    $jp1 = $mod_trans / $jp1;
    $jp1 = $jp1->SwapVariables($jx_present_vars, $jx_next_vars);
   }
  $trans = $trans + $rho2;

  $endtime =  (times)[0];
  printf "   Time of Rho2 \t\t%10.2f seconds\n", ($endtime - $starttime);
  $starttime =  (times)[0];

  ##################################
  # Build strategy rho3: add moves in which the environment violates its fairness
  # condition
  $jp1 = $zero;
  my $rho3 = $zerobdd;
  for(my $j = 0; $j < $n; ++$j)
  {
    my $low = $zerobdd;
    my $jx_equal_j = $jp1;
    $jp1 = $jp1->SwapVariables($jx_next_vars, $jx_present_vars);

    for(my $r = 0; $r < @$maxr[$j]; ++$r)
    {
      for(my $i = 0; $i < $m; $i++)
      {
        my $next_x = $this->swapPresentNext($$x_array[$j][$r][$i]);

        my $tmp_rho3 = ($jx_equal_j * ($$x_array[$j][$r][$i]->Restrict($reachable_states))
                        * ((!$low)->Restrict($reachable_states)) *
                        (!@$env_fairness[$i]) * $trans12 * $next_x * $jp1);
        push(@rho_list, $tmp_rho3);
        $rho3 = $rho3 + $tmp_rho3;
        $low = $low + $$x_array[$j][$r][$i];
      }
    }

    $jp1 = $jp1->SwapVariables($jx_next_vars, $jx_present_vars);
    $jp1 = $mod_trans / $jp1;
    $jp1 = $jp1->SwapVariables($jx_present_vars, $jx_next_vars);
  }
  $trans = $trans + $rho3;

  $endtime =  (times)[0];
  printf "   Time of Rho3 \t\t%10.2f seconds\n", ($endtime - $starttime);

#   my @tmp_array;
#   for(my $j = 0; $j < $n; ++$j) {      
#       for(my $r = 0; $r < @$maxr[$j]; ++$r) {
# 	  push(@tmp_array, $$y_array[$j][$r]);
# 	  for(my $i = 0; $i < $m; $i++) {
# 	      push(@tmp_array, $$x_array[$j][$r][$i]);
# 	  }
#       }
#   }

#   print "======================================================================\n";
#   print " RHO1             :\t" . $rho1->Size() . "\n";
#   print " RHO2             :\t" . $rho2->Size() . "\n";
#   print " RHO3             :\t" . $rho3->Size() . "\n";
#   print " SHARING SUB-RHOS :\t" . Cudd::BDD::Size([$rho1, $rho2, $rho3]) . "\n";
#   print " TRANS            :\t" . $trans->Size() ."\n";
#   print " TRANS_RELATION   :\t" . $trans12->Size() . "\n";
#   print " Z                :\t" . $z->Size() . "\n";
#   print " SHARING SIZE     :\t" . Cudd::BDD::Size([$rho1, $rho2, $rho3]) . "\n";
#   print " SHARING SIZE X,Y :\t" . Cudd::BDD::Size(\@tmp_array) . "\n";
#   print @tmp_array,"\n";
#   print "======================================================================\n";

  return $trans;
}

#----------------------------------------------------------------------
# Use the given generator to produce some VHDL code
sub synthesize {
  my $this = shift;
  my $zero = $$this{bdd_module}->{bdd_zero};
  my $strategy =  $zero;
  my $time = (times)[0];
  
  my $env_transition = $$this{bdds}->{ENV_TRANSITIONS}[0];
  my $sys_transition = $$this{bdds}->{SYS_TRANSITIONS}[0];
  my $env_initial    = $$this{bdds}->{ENV_INITIAL}[0];
  my $sys_initial    = $$this{bdds}->{SYS_INITIAL}[0];
  
  my $initial = $env_initial * $sys_initial;
  my $trans12 = $env_transition * $sys_transition;

  my $reachable_states = $this->calculateReachability($trans12);
  $$this{reachable_states} = $reachable_states;
  

  my ($result, $x_array, $y_array, $maxr) = $this->winm();
  $$this{winning_states} = $result;
  printf "   Compute Winning Region \t\t%10.2f seconds\n", ((times)[0] - $time);
  $time = (times)[0];
  
  if ($initial <= $result) { #initial states are winning (I subset of W)
      $strategy = $this->strategy($result, $x_array, $y_array, $maxr);
  } else {
      my $tmp = $result * $initial;
      if ($tmp <= $zero) { #$strategy=zero
	  print "   None of the initial states is winning     \t------\n";
      } else {
	  print "   Some of the initial states aren't winning \t------\n";
      }
  }
  printf "   Compute Winning Strategy \t\t%10.2f seconds\n", ((times)[0] - $time);

  return $strategy;
}


#----------------------------------------------------------------------
# Minimize the strategy 
#
# in: this is a synthesize
# strategy is the strategy
# remove_dbw is a Boolean flag stating whether the variables that are
# described by DBW should be quantified out or not.
#
# returns a triple: 
# 1. strategy
# 2. comb functions for dependent variables
# 3. hashmap mapping comb outputs to functions in terms of comb inputs (bdds)
sub minimize {
  my ($this, $strategy, $remove_dbw, 
      $extract_superfluousy, $dep_var_analysis, $gen_funcs, $date_version) = @_;

  my $winning = $$this{winning_states};
  my $manager = $this->{bdd_module}->getBDDManager;
  my $reachable_states = $$this{reachable_states};
  $strategy = $strategy->Restrict($reachable_states);

  #--- REACHABLE STATE OPTIMIZATION ---
  my $time = (times)[0];
  
  my $strat_reachable_states = $this->calculateReachability($strategy);

  #---STRATEGY OPTIMIZATION ---
  my $new_strategy = $strategy; 
  my %g;
  my ($sub_functions, $unneeded_vars);
  if($gen_funcs eq 1) {
    my $var_table = $$this{bdd_module}->getTableOfVars();

    # build arrays of combinational output and  comb. input vars
    # FIXXME: Build array in bdd_module
    my @output_array;
    my @input_array;

    my %output_vars = ();
    foreach my $key (keys %$var_table) {
      my $var_array = $$var_table{$key};
      my $var = @$var_array[1];
      my ($is_input, $is_next, $is_environment) = $$this{bdd_module}->getVarClassification($var);
      if((!defined $is_input) || (!$is_input eq 1)) {
        push(@output_array, $var);
        $output_vars{$key} = $var; 
      } else {
        push(@input_array, $var);
      }
    }

    foreach my $jx_key (keys %{$$this{bdd_module}->{jx_vars}}) {
      my $tmp = @{$$this{bdd_module}->{jx_vars}{$jx_key}}[1];
      $output_vars{$jx_key} = $tmp;
      push(@output_array, $tmp);
    }
    # done building the arrays of out and in vars

    # generate a function for each comb output in terms of comb inputs.
    # see paper for the algorithm
    # The result is a hashmap g that maps comb output names to their function.
    $new_strategy = $manager->BddOne;
    my $careset = $strat_reachable_states * $winning;
    my @output_keys = (keys %output_vars);
#    my @output_keys = ("start", "hgrant1", "hlocked", "stateG2_0", "stateA1_0", "hmastlock",
#                       "stateA1_1", "decide", "hmaster0", "stateG2_1", "stateG3_1",
#                       "stateG3_0", "stateG10_1", "stateG3_2", "jx0", "hgrant0");
#    @output_keys = reverse(@output_keys);

    foreach my $output_key (@output_keys) {
      my $strategy_prime = $strategy;

      # quantify out all other output variables
      foreach my $output2_key (@output_keys) {
        if(!($output_key eq $output2_key)) {
          my $var = $output_vars{$output2_key};
          $strategy_prime = Exists $var $strategy_prime;
        }
      }
      
      my $var = $output_vars{$output_key};
      my $positive_cofactor = $strategy_prime / $var;
      my $negative_cofactor = $strategy_prime / (!$var);
      my $p = $positive_cofactor * !$negative_cofactor;
      my $n = $negative_cofactor * !$positive_cofactor;

      if($date_version eq 0) {
        foreach my $input (@input_array) {
        my $p_prime = Exists $input $p;
        my $n_prime = Exists $input $n;
        if(($p_prime * $n_prime) == (!$manager->BddOne)) {
          $p = $p_prime; 
          $n = $n_prime;
        }
      }
    }

      my $xor = $p + $n; #$p*!$n + !$p*$n; #$positive_cofactor ^ $negative_cofactor;
      my $func = $p->Restrict($xor * $careset); #$positive_cofactor->Restrict($xor * $careset);
 
      if(!(($remove_dbw eq 1) && (substr($output_key,0,5) eq "state"))) {
        $g{$output_key} = $func;
        $strategy = $strategy->Compose($var, $func);
        $new_strategy = $new_strategy * (!$var + $func) * ($var + !$func); #=($var <-> $func)
      }
    }

    $new_strategy = $new_strategy  * $strategy;

    if($dep_var_analysis eq 1) {
      ($sub_functions, $unneeded_vars) = $this->extractBDDFunctions($strat_reachable_states);
      
      foreach my $sub_var (keys %$sub_functions) {
        delete $g{$sub_var};
      }

      foreach my $var (@$unneeded_vars) {
        $new_strategy = Exists $var $new_strategy;
#        foreach my $output_key (keys %g) {
#          my $func = Exists $var $g{$output_key};
#          $g{$output_key} = $func;
#        }
      }
      printf "   Dependent variables \t\t\t%10.2f seconds\n", ((times)[0] - $time);
      $time = (times)[0];
    }
    printf "   Combinational Output Fcts \t\t%10.2f seconds\n", ((times)[0] - $time);
  }

  my $vars;
  if($extract_superfluousy eq 1) {
    $vars = $this->calculateSuperfluousVariables($new_strategy);
    foreach my $var_name (keys %$vars) {
      my $var = $vars->{$var_name};
      $new_strategy = Exists $var $new_strategy;
    }
  }

  return ($new_strategy, $sub_functions,\%g, $vars);
}

#----------------------------------------------------------------------
sub getConfiguredOrdering {
  my $this = shift;

  my $ordering = $$this{parser_module}->{formulas}->{FORCE_ORDERING}[0];
  if(!(defined $ordering)) {
    $ordering = "<not configured>";
  } else {
    $ordering =~ s/\*/ -> /g;
  }
  return $ordering;
}

#----------------------------------------------------------------------
# this: synthesizer 
#
# bdd:reachable states wrt strategy 
#
# returns a triple (subfunctions, unneededvars), where 
# 
# subfunctions is a hashmap that maps variables to functions: for every
# dependent variable there is an entry that states how it can be computed
# from the value of the other variables.
#
# unneeded vars: array bdd variables of dependent variables (both ps and ns)

sub extractBDDFunctions {
  my ($this, $bdd) = @_;

  my $var_table = $$this{bdd_module}->getTableOfVars();

  my %variables;

  foreach my $key (keys %$var_table) {
    $variables{$key} = @{$$var_table{$key}}[0];
  }

  foreach my $jx_key (keys %{$$this{bdd_module}->{jx_vars}}) {
    $variables{$jx_key} = @{$$this{bdd_module}->{jx_vars}->{$jx_key}}[0];
  }

  my %sub_functions;
  my @unneeded_vars;
  my $rest_bdd = $bdd;
  foreach my $key (keys %variables) {
    my $var = $variables{$key};

#    print "Check $key\n";
    if($rest_bdd->bddVarIsDependent($var) eq 1) {
      my $positive_cofactor = $rest_bdd / $var;
      my $negative_cofactor = $rest_bdd / !$var;
	
#      print "cofactors $key: \n";
#      $positive_cofactor->Print(5,2);
#      print " neg:\n";
#      $negative_cofactor->Print(5,2);

      my $func = $positive_cofactor->Restrict($positive_cofactor + $negative_cofactor);
      # Since this variable is only a combination of other state variables, we do not need
      # to store the value.  Therefore, we only define the next state variable in terms of
      # the next states variables of the others.
      # Since dependence analysis is done over present state variables, we have to swap
      # the variables.
      $func = $this->swapPresentNext($func);
      $sub_functions{$key} = $func;
	
      $rest_bdd = Exists $var $rest_bdd;
#      print "pushing " . @{$$var_table{$key}}[1] . "\n"; # FIXXXME pushing only next state variable
	
      my $var_lst;
      if (exists $$var_table{$key}) {
        $var_lst = $$var_table{$key};
      } elsif (exists $$this{bdd_module}{jx_vars}->{$key}) {
        $var_lst = $$this{bdd_module}{jx_vars}->{$key};
      }
      push(@unneeded_vars, @{$var_lst}[0]);
      push(@unneeded_vars, @{$var_lst}[1]);
      #print "Push $key", @{$var_lst}[0], @{$var_lst}[1],"\n";
    }
  }

  
  return (\%sub_functions, \@unneeded_vars);
}

#----------------------------------------------------------------------
sub calculateReachability {
  my $this = shift;
  my $trans_relation = shift;

  my $bdd_module = $$this{bdd_module};
  my $manager = $bdd_module->getBDDManager();

  my $var_table = $bdd_module->getTableOfVars();
  my $jx_vars = $$bdd_module{jx_vars};
  my $present_vars = $manager->BddOne;
  
  my $env_initial    = $$this{bdds}->{ENV_INITIAL}[0];
  my $sys_initial    = $$this{bdds}->{SYS_INITIAL}[0];
  my $jx_initial = $manager->BddOne;

  while( my ($key, $vars) = each %$var_table) {
      $present_vars = $present_vars * @$vars[0];
  }

  #Build initial BDD for the jx variables
  foreach my $jx_var (values %$jx_vars) {
    my $var = @$jx_var[0];
    $present_vars = $present_vars * $var;
    my $name  = $bdd_module->getVariableName($var);
    my $value = $bdd_module->getVarInitValue($name);
    if ($value) {
	$jx_initial = $jx_initial * @$jx_var[0];
    } else {
	$jx_initial = $jx_initial * !@$jx_var[0];
    }
  }

  #cube of initial states
  my $reach = $env_initial * $sys_initial * $jx_initial;
  
  my $old_reach = !($manager->BddOne);
  while($old_reach != $reach) {
    $old_reach = $reach;
#    my $tmp = $reach * $trans_relation;
#    my $tmp2 = Exists $present_vars $tmp;
    my $tmp2 = Cudd::BDD::AndExists($present_vars, $reach, $trans_relation);
    $reach = $reach + $this->swapPresentNext($tmp2);
  }

   return $reach;
}

#----------------------------------------------------------------------
#Calculate variables which are not needed according to following
#algorithm:
#  Let p'(y) = p(y) * !n(y), n'(y) = n(y) * !p(y)
#  Let x be a combinational input
#  Let d(y,x) = (exists x. p'(y)) * (exists x. n'(y)) * winning * reachable
#  if d(y,x)=false, then y does not depend on x.
#  If for all y, d(y,x)=false, then we can remove input x. 
#
# Params: States (strategy)
# Returns: Superfluousy Vars (hash mapping variable name to bdd var)
sub calculateSuperfluousVariables 
{
  my $time = (times)[0];

  my ($this, $states) = @_;
  my $winning = $$this{winning_states};
  my $bdd_module = $$this{bdd_module};
  my $var_table = $bdd_module->getTableOfVars();

  my %output_vars = ();
  my %input_vars = ();
  foreach my $key (keys %$var_table) {
    my $var_array = $$var_table{$key};
    my $var = @$var_array[1];
    my ($is_input, $is_next, $is_environment) = $$this{bdd_module}->getVarClassification($var);
    if((!defined $is_input) || (!$is_input eq 1)) {
      $output_vars{$key} = $var; 
    } else {
      $input_vars{$key} = $var;
    }
  }

  foreach my $jx_key (keys %{$$this{bdd_module}->{jx_vars}}) {
    my $tmp = @{$$this{bdd_module}->{jx_vars}{$jx_key}}[1];
    $output_vars{$jx_key} = $tmp;
  }
  # done building the arrays of out and in vars

  # calculate superfluous variables
  my %g;
  my $reachable = $this->calculateReachability($states);
  my $tmp = $reachable * $winning;
  my $bdd_zero = !($bdd_module->getBDDManager()->BddOne);

  my %superfluousy_vars;
  my $num_output_vars = scalar (keys %output_vars);
  foreach my $input_key (keys %input_vars) {
    my $input_var = $input_vars{$input_key};

    my $num_independent = 0;
    foreach my $output_key (keys %output_vars) {
      my $states_prime = $states;

      # quantify out all other output variables
      foreach my $output2_key (keys %output_vars) {
        if(!($output_key eq $output2_key)) {
          my $var = $output_vars{$output2_key};
          $states_prime = Exists $var $states_prime;
        }
      }
    
      my $var = $output_vars{$output_key};
      my $positive_cofactor = $states_prime / $var;
      my $negative_cofactor = $states_prime / (!$var);
      my $pprime = $positive_cofactor * (!$negative_cofactor);
      my $nprime = $negative_cofactor * (!$positive_cofactor);

      my $d = (Exists $input_var $pprime) * (Exists $input_var $nprime) * $tmp;
#      print "   d($input_key,$output_key): ".($d == $bdd_zero)."\n";
      if($d == $bdd_zero) {
        $num_independent++;
      }
    }
#    print "Var $input_key: $num_independent eq $num_output_vars\n";
    if($num_independent eq $num_output_vars) {
      $superfluousy_vars{$input_key} = $input_var;
    }
  }

  printf "   Calculation of superflously vars \t%10.2f seconds\n", ((times)[0] - $time);
  return(\%superfluousy_vars);
}
