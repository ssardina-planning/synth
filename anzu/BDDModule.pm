#$Id: BDDModule.pm,v 1.16 2007/04/13 09:22:15 rbloem Exp $

package BDDModule;

use Cudd;
use LTL;
use POSIX; # qw(ceil floor);

return 1;

#----------------------------------------------------------------------
# constructor
sub new
{
    my $class = shift;
    
    my $objref = {
	manager => new Cudd,
	manager_initialized => 0,
	bdd_one => 0,
	bdd_zero => 0,
	ordered_vars => {},
	tableOfVars => {},
	num_input_vars => 0,
	num_output_vars => 0,
	printDebug => 0,
	variable_names => [],
	present_next_var_names => [],
	initial_values => {},
	parents => {},          #2D hash of array
	siblings => {},
	processed_nodes => {},
	right_siblings => {},
	left_siblings => {},
#    then_right_parent => {},
	then_left_parent => {},
#    else_right_parent => {},
	else_left_parent => {},
  jx_vars => {},                  #FIXXXXME: this should be merged with tableOfVars
  jx_var_names => [],
  jx_num => 0
  };

	bless $objref,$class;
	return $objref;
}

#----------------------------------------------------------------------
# initialize BDDModule. Creates for every variable 
# @param input_variables array of available input variables for the BDD
# @param output_variables array of available output variables for the BDD
sub initialize {
  my $this = shift;
  my $input_variables = shift;
  my $output_variables = shift;
  my $initial_values = shift;
  my $var_ordering = shift;

  my @variables = @$input_variables;
  push(@variables, @$output_variables);

  $$this{num_input_vars} = @$input_variables;
  $$this{num_output_vars} = @$output_variables;
  $$this{variable_names} = \@variables;

  $$this{initial_values} = $initial_values;
  my $num = 0;
  my @all_var_names;
  foreach my $var (@variables) {
    my $psBddVar = $$this{manager}->BddVar;
    print $var,"_p: ",$num++,"\n";
    my $nsBddVar = $$this{manager}->BddVar;
    print $var,"_n: ",$num++,"\n";
#    my $nsBddVar = $psBddVar->NewAdjVar();

    push(@all_var_names, $var.'_p'); #FIXXXXME: present next is encoded somewhere else in this module but using getVariableName does not work
    push(@all_var_names, $var.'_n');

    my @tableOfVarsEntry = ($psBddVar, $nsBddVar);
    push(@{$$this{tableOfVars}->{$var}}, @tableOfVarsEntry);
  }
  $$this{bdd_one} = $$this{manager}->BddOne;
  $$this{bdd_zero} = $$this{manager}->BddZero;
  $$this{manager_initialized} = 1;
  $$this{present_next_var_names} = \@all_var_names;

  if(defined $var_ordering) {
    my @ordered_vars;
    foreach my $var_name (@$var_ordering) {
      my $index = 0;
      if(substr($var_name, length($var_name)-1, 1) eq "'") {
        $var_name = substr($var_name, 0, length($var_name)-1);
        $index = 1;
      }
      
      if(!defined @{$$this{tableOfVars}->{$var_name}}) {
        my $psBddVar = $$this{manager}->BddVar;
	print $var_name,"_p: ",$num++,"\n";
        my $nsBddVar = $$this{manager}->BddVar;
	print $var_name,"_n: ",$num++,"\n";
        my @tableOfVarsEntry = ($psBddVar, $nsBddVar);
        push(@{$$this{tableOfVars}->{$var_name}}, @tableOfVarsEntry);
      }

      push(@ordered_vars, @{$$this{tableOfVars}->{$var_name}}[$index]);
    }

    if(@ordered_vars != 0) {
      Cudd::BDD::Shuffle(\@ordered_vars); 
    }
    
    #FIXXXME: This will break internal assumption of variable ordering in $$this{variable_names}
    #         Therefore any use of Cudd::NodeReadIndex must be checked.
    #         getVarClassification does not work correctly anymore
  }
}

#----------------------------------------------------------------------
sub extractInitValuesFromInitialBDDs {
    my $this = shift;
    my $env_initial = shift;
    my $sys_initial = shift;
    my $init =  $$this{manager}->BddOne;
    my $zero = !$init;
    my $variable_names = $$this{variable_names};
    my $num_variables = $$this{num_input_vars} + $$this{num_output_vars};

    $init = @$env_initial[0];
    $init = $init * @$sys_initial[0];

    my $num_minterms = $init->Minterms($num_variables);
    if ($num_minterms > 1) {
	print "Specification has $num_minterms initial states:\n";
    }
    my ($var, $var_one, $var_zero);
    foreach my $name (@$variable_names) {
	$var = @{$$this{tableOfVars}->{$name}}[0]; #present state
 	$var_one  = $init * $var;
 	$var_zero = $init * !$var;
	if ($var_one  == $zero) {
	    if ($var_zero != $zero) {
		$$this{initial_values}{$name} = 0;
	    } else {
		die "no valid initial value\n";
	    }
	} else {
	    if ($var_zero == $zero) {
		$$this{initial_values}{$name} = 1;
	    } else {
		print "   Initial value of variable '$name' is free - set it to 0\n";
		$$this{initial_values}{$name} = 0;
		$init = $init / !$var;
	    }
	}
    }
}

#----------------------------------------------------------------------
sub generateJXVar {
  my $this = shift;

  my $manager = $$this{manager};
  my $var_name = "jx" . ($$this{jx_num}++);
  my $present;
  my $next;
  if(!defined $$this{jx_vars}->{$var_name}) {
    $present = $manager->BddVar;
    print $var_name,"_p:\n";
    $next = $manager->BddVar;
    print $var_name,"_n:\n";

    my @jx_entry = ($present, $next);
    push(@{$$this{jx_vars}->{$var_name}}, @jx_entry); #FIXXXME: This should be stored inside the BDDModule !!!
    push(@{$$this{jx_var_names}}, $var_name."_p"); #FIXXXME: This should be stored inside the BDDModule !!!
    push(@{$$this{jx_var_names}}, $var_name."_n"); #FIXXXME: This should be stored inside the BDDModule !!!
  } else {
    my $jx_entry = $$this{var_name};
    $present = @$jx_entry[0];
    $next = @$jx_entry[1];
  }

  return ($present, $next);
}

#----------------------------------------------------------------------
sub buildBdd {
    my $this = shift;
    my $formula = shift;
    my $state = shift;

    my $manager = $$this{manager};
    my $tableOfVars = $$this{tableOfVars};
    my $finalBdd;

    if ($formula->Type eq 'binaryop') {
	my $finalBddLeft = $this->buildBdd($formula->Left, $state);
	my $finalBddRight = $this->buildBdd($formula->Right, $state);
	if ($formula->Value eq '+') {
	    $finalBdd = $finalBddLeft + $finalBddRight;
	    #print "found a +\n";
	    #$numberOfVars = @tableOfVars;
	    #$finalBdd->Print($numberOfVars,2);
	}
	elsif ($formula->Value eq '*') {
	    $finalBdd = $finalBddLeft * $finalBddRight;
	    #print "found a * \n";
	    #$numberOfVars = @tableOfVars;
	    #$finalBdd->Print($numberOfVars,2);
	}
	elsif ($formula->Value eq 'R' || $formula->Value eq 'U') {
	    # print "found a " . $formula->Value . ": left side ignored, continue with right side\n";
	    $finalBdd = $finalBddRight;
	}
	else {
	    print $formula->Value . "is not implemented \n";
	}
    }
    elsif ($formula->Type eq 'unaryop') {
	my $finalBddLeft = $this->buildBdd($formula->Left, $state);
	if ($formula->Value eq '!') {
	    $finalBdd = !$finalBddLeft;
	    #print "found a !\n";
	    #$numberOfVars = @tableOfVars;
	    #$finalBdd->Print($numberOfVars,2);
	}
	else {
	    print "! is the only alowed unary operator \n";
	}
    }
    elsif ($formula->Type eq 'temporalop') {
	if ($formula->Value eq 'X') {
	    #print "found a X\n";
	    $state = 1;
	    $finalBdd = $this->buildBdd($formula->Left, $state);                
	}
	elsif ($formula->Value eq 'G' || $formula->Value eq 'F') {
	    #print "found a G or F -> just ignored!\n";
	    $finalBdd = $this->buildBdd($formula->Left, $state);
	}
	else {
	    print "only X, G and F implemented \n";
	}
    }
    elsif ($formula->Type eq 'atom') {
	if ($formula->Value eq 'TRUE') {
	    #print "found a TRUE \n";
	    $finalBdd = $$this{bdd_one};
	    #print "finalBdd is now: $finalBdd \n";
	    #$numberOfVars = @tableOfVars;
	    #$finalBdd->Print($numberOfVars,2);
	}
	elsif ($formula->Value eq 'FALSE') {
	    #print "found a FALSE \n";
	    $finalBdd = !($$this{bdd_one});
	    #print "finalBdd is now: $finalBdd \n";
	    #$numberOfVars = @tableOfVars;
	    #$finalBdd->Print($numberOfVars,2);
	}
	else {		
	    foreach my $key_name (keys %$tableOfVars) {
		my @var = split(/=/, $formula->Value);  
		if ($key_name eq $var[0]) {
		    if ($var[1] eq 1) {
			$finalBdd = @{$$tableOfVars{$key_name}}[$state];
			#print "finalBdd is now: $finalBdd \n";
			#$numberOfVars = @tableOfVars;
			#$finalBdd->Print($numberOfVars,2);
		    }
		    elsif ($var[1] eq 0) {
			$finalBdd = !@{$$tableOfVars{$key_name}}[$state];
			#print "finalBdd is now: $finalBdd \n";
			#$numberOfVars = @tableOfVars;
			#$finalBdd->Print($numberOfVars,2);
		    }
		    else {
			print "Fatal Error in buildBdd: a Variable mus be 0 or 1 \n";
		    }
		    last;
		}			
	    }
	    #TODO check if we found a match
	}
    }
    return $finalBdd;	
}

#----------------------------------------------------------------------
# creates the BDD for the given formula and returns it
# @param formula the formula represented as a parse tree
sub createBDD {
	my $this = shift;
	my $formula = shift;

  if($$this{manager_initialized} == 0) {
    print "WARNING: manager not initialized\n";
  }

	my $state=0;
	my $finalBdd = $this->buildBdd($formula, $state);

	#$numberOfVars = $$this{@tableOfVars};
	#$finalBdd->Print($numberOfVars,3);
	#$finalBdd->Print($numberOfVars,2);

	return $finalBdd;
}

#----------------------------------------------------------------------
# returns the BDD manager of the module
sub getBDDManager {
  my $this = shift;

  if($$this{manager_initialized} == 0) {
    print "WARNING: manager not initialized\n";
  }
  return $$this{manager};
}

#----------------------------------------------------------------------
# returns the table with all specified variables (present and next)
sub getTableOfVars {
  my $this = shift;

  if($$this{manager_initialized} == 0) {
    print "WARNING: manager not initialized\n";
  }
  return $$this{tableOfVars};
}


#----------------------------------------------------------------------
# returns an array (of an array) of all input variables (present and next)
sub getTableOfOutputVars {
  my $this = shift;

  if($$this{manager_initialized} == 0) {
    print "WARNING: manager not initialized\n";
  }

  my $var_table = $$this{bdd_module}->getTableOfVars();
  my %output_vars = ();
  foreach my $key (keys %$var_table) {
    my $var_array = $$var_table{$key};
    my $var = @$var_array[1];
    my ($is_input, $is_next, $is_environment) = $$this{bdd_module}->getVarClassification($var);
    if((!defined $is_input) || (!$is_input eq 1)) {
#      print "key=" . $key . "\n";
      $output_vars{$key} = $var; 
    }
  }

  return \$output_vars;
}


#----------------------------------------------------------------------
# returns wether the given variable is an input variable or not and
# wether the variable is a present state variable or a next state variable
# param BDD The first node of the bdd will be classified
# return is_inputvar (true/false), is_next (true/false), is_envionment (true/false)
sub getVarClassification {
  my $this = shift;
  my $bdd = shift;

  my $var_index = Cudd::NodeReadIndex($bdd->{'node'});
  return $this->getLayerClassification($var_index);
}


#----------------------------------------------------------------------
#params: $var_index: layer index of variable
#returns: $is_input, $is_next, $is_environment
sub getLayerClassification {
  my $this = shift;
  my $var_index = shift;

  my $is_env = ($var_index < 2*($$this{num_input_vars}));
  if ($is_env eq "") {
    $is_env = 0;
  }
  return(($var_index < 2*($$this{num_input_vars})) || !($var_index % 2), ($var_index % 2), $is_env);
}

#----------------------------------------------------------------------
sub isEnvironmentVar {
  my $this = shift;
  my $variable = shift;

  $variable = substr($variable, 0, length($variable)-2);

  my $var_index = 0;
  my $result_index = @{$$this{variable_names}} - 1;
  foreach my $var (@{$$this{variable_names}}) {
    if($var eq $variable) {
      $result_index = $var_index;
    }
    $var_index++;
  }

  my $is_env = ($result_index < ($$this{num_input_vars}));
  if ($is_env eq "") {
    $is_env = 0;
  }

  return($is_env);
}


#----------------------------------------------------------------------
# get list of all parents of the given node
# param node the given node
sub getParentList {
  my ($this, $node) = @_;

  if(defined $node) {
    my $node_name = $node->{node_name};
#    my @parents = ();
    
#    push(@parents, $$this{parents}{$node_name});
    
#    print "getParentList=" . @{$$this{parents}{$node_name}} . "\n";
    return $$this{parents}{$node_name};
  } else {
    print "Error: undefined node passed";
    return undef;
  }
}

#----------------------------------------------------------------------
# returns the true child
# param node the given node
sub getThenChild {
  my $this = shift;
  my $node = shift;

  if(defined $node && ($node != $$this{bdd_one}) && ($node != (!$$this{bdd_one}))) {
    return $node->T();
  } else {
    return undef;
  }
}

#----------------------------------------------------------------------
# returns the false child
# param node the given node
sub getElseChild {
  my $this = shift;
  my $node = shift;

  if(defined $node && ($node != $$this{bdd_one}) && ($node != (!$$this{bdd_one}))) {
    return $node->E();
  } else {
    return undef;
  }
}

#----------------------------------------------------------------------
# returns the left sibling of the given node
# param node the given node
sub getLeftSibling {
  my $this = shift;
  my $node = shift;

  my $node_name = $this->getNodeName($node);
  return $$this{left_siblings}{$node_name};
#  my $node_read_index = Cudd::NodeReadIndex($node->{node});
#  return $this->getPreviousElement($node, $$this{siblings}{$node_read_index});
}

#----------------------------------------------------------------------
# returns the right sibling of the given node
# param node the given node
sub getRightSibling {
  my $this = shift;
  my $node = shift;

  my $node_name = $this->getNodeName($node);
  return $$this{right_siblings}{$node_name};

#  my $node_read_index = Cudd::NodeReadIndex($node->{node});
#  my @reversed_array = reverse(@{$$this{siblings}{$node_read_index}});
#  return $this->getPreviousElement($node, \@reversed_array);
}

#----------------------------------------------------------------------
# returns the element previous to the given node in the given array
sub getPreviousElement {
  my ($this, $node, $current_siblings) = @_;
  
  my $previous_node = undef;
  if(defined $current_siblings) {
    my $node_name = $this->getNodeName($node);
    if(!($node_name eq "undef")) {
      foreach my $item (@$current_siblings) {
        if($item->{node_name} == $node_name) {
          return $previous_node;
        }
        $previous_node = $item;
      }
    }
  }
  return undef;
}


#----------------------------------------------------------------------
sub listGetPrevious {
  my ($this, $list, $node) = @_;
  
  my $node_name = $this->getNodeName($node);
  my $previous_node = undef;
  if(!($node_name eq "undef")) {
    my $length = @$list;
#      for(my $index=0; $index < $length; ++$index) {
#        if((@{$list}[$index]->{node_name}) == $node_name) {
#          return @$list[$index - 1];
#        }
#      }
    foreach my $item (@$list) {
      if($item->{node_name} == $node_name) {
        return $previous_node;
      }
      $previous_node = $item;
    }
  }
  return undef;  
}

#----------------------------------------------------------------------
# returns 1 if the given node exists in the given array, otherwise 0
sub nodeExists {
  my ($this, $node, $array) = @_;

  my $node_name = $this->getNodeName($node); 
  if(!($node_name eq "undef")) {
    foreach my $item (@$array) {
      if($node_name == $item->{node_name}) {
        return 1;
      }
    }
  }
  
  return 0;
}

#----------------------------------------------------------------------
# returns the unique name of the node: returns the integer value of the
# pointer address.
# param node the given node
sub getNodeName {
  my ($this, $node) = @_;

  if(defined $node) {
    return $node->{'node_name'};
  } else {
    return "undef";
  }
}


#----------------------------------------------------------------------
# recursive method which prepares all data structures needed for returning the
# -> checks if children t/e does exist, add $node to their list of parents
#    and call generateNodeDependencies() recursivly with the t/e child.
# the correct node in the getParentList(), getThenChild(), getElseChild(),
# getLeftSibling() and getRightSibling() methods.
sub generateNodeDependencies {
  my $this = shift;
  my $node = shift;

  if(not defined $node) {
    print "Error -> this message should never appear";
    return;
  }

  if($node == $$this{bdd_one}) {
    return;
  }

  if($node == $$this{bdd_zero}) {
    return;
  }


  my @pending_nodes = ();
  push(@pending_nodes, $node);
  for(my $i = 0; $i < (scalar @pending_nodes); $i++) {
    $node = $pending_nodes[$i];

    #siblings
    my $node_name = $node->{node_name};
    my $node_read_index = Cudd::NodeReadIndex($node->{node});
    
    if(defined $$this{siblings}{$node_read_index}) {
      my $left_node = $$this{siblings}{$node_read_index};
      my $left_node_name = $this->getNodeName($left_node);
      
      $$this{left_siblings}{$node_name} = $left_node;
      $$this{right_siblings}{$left_node_name} = $node;
    }
    $$this{siblings}{$node_read_index} = $node;
    
    
    #parents
    my $then_child = $this->getThenChild($node);
    
    if(defined $then_child) {
      my $then_child_name = $then_child->{node_name};
      
      my $num_parents = 0;
      if(defined $$this{parents}{$then_child_name}) {
        $num_parents = (scalar @{$$this{parents}{$then_child_name}});
      }
      
      if($num_parents != 0) {
        my $left_node = @{$$this{parents}{$then_child_name}}[$num_parents-1];
#      my $left_node_name = $this->getNodeName($left_node);
        
        $$this{then_left_parent}{$node_name} = $left_node;
#      $$this{then_right_parent}{$left_node_name} = $node;
      }
      
      push(@{$$this{parents}{$then_child_name}}, $node);
      
      if(!(defined $$this{processed_nodes}{$then_child_name})) {
        $$this{processed_nodes}{$then_child_name} = 1;
        if(($then_child != $$this{bdd_one}) && ($then_child != $$this{bdd_zero})) {
#        $this->generateNodeDependencies($then_child);
          push(@pending_nodes, $then_child);
        }
      }
    }
    
    
    
    
    my $else_child = $this->getElseChild($node);
    
    if(defined $else_child) {
      my $else_child_name = $else_child->{node_name};
      
      my $num_parents = 0;
      if(defined $$this{parents}{$else_child_name}) {
        $num_parents = (scalar @{$$this{parents}{$else_child_name}});
      }
      
      if($num_parents != 0) {
        my $left_node = @{$$this{parents}{$else_child_name}}[$num_parents-1];
#      my $left_node_name = $this->getNodeName($left_node);
        
        $$this{else_left_parent}{$node_name} = $left_node;
#      $$this{else_right_parent}{$left_node_name} = $node;
      }
      
      push(@{$$this{parents}{$else_child_name}}, $node);
      
      if(!(defined $$this{processed_nodes}{$else_child_name})) {
        $$this{processed_nodes}{$else_child_name} = 1;
        if(($else_child != $$this{bdd_one}) && ($else_child != $$this{bdd_zero})) {
#        $this->generateNodeDependencies($else_child);
          push(@pending_nodes, $else_child);
        }
      }
    } # else-child

  } #for-loop 
}

#----------------------------------------------------------------------
sub getAccordingPresentVar {
  my $this = shift;
  my $node = shift;

  return $this->getVariableName($node, "p");
}

#----------------------------------------------------------------------
sub getAccordingNextVar {
  my $this = shift;
  my $node = shift;

  return $this->getVariableName($node, "n");
}


#----------------------------------------------------------------------
sub getVariableName {
  my $this = shift;
  my $node = shift;
  my $present_next = shift;

  my $var_index = Cudd::NodeReadIndex($node->{'node'});
  
  my $real_var_index = floor($var_index / 2);

  my $var_name = "jx" . ($real_var_index - ($$this{num_input_vars} + $$this{num_output_vars}));

  if($real_var_index < @{$$this{variable_names}}) {
    $var_name = $$this{variable_names}[$real_var_index];
  }

  my $appendix = "_p";
  
  if (($var_index % 2) == 1) {
    $appendix = "_n";
  }

  if(defined $present_next) {
    $appendix = "_".$present_next;
  }

  
  return($var_name . $appendix);
}

#----------------------------------------------------------------------
# returns all variables
sub getAllVarNames {
  my $this = shift;
  return $$this{variable_names};
}

#----------------------------------------------------------------------
# returns all variables
sub getAllPresentNextVarNames {
  my $this = shift;
  return $$this{present_next_var_names};
}

#----------------------------------------------------------------------
# returns wether the specified bdd is equal to bdd one or not
# param bdd the bdd 
sub isBddOne {
  my $this = shift;
  my $node = shift;

  return($node == $$this{bdd_one});
}


#----------------------------------------------------------------------
# returns wether the specified bdd is equal to bdd zero or not
# param bdd the bdd 
sub isBddZero {
  my $this = shift;
  my $node = shift;

  return($node == $$this{bdd_zero});
}

#----------------------------------------------------------------------
sub getThenLeftParent {
  my ($this, $node_name) = @_;
  return $$this{then_left_parent}{$node_name};
}

#----------------------------------------------------------------------
# sub getThenRightParent {
#   my ($this, $node_name) = @_;
#   return $$this{then_right_parent}{$node_name};
# }

#----------------------------------------------------------------------
sub getElseLeftParent {
  my ($this, $node_name) = @_;
  return $$this{else_left_parent}{$node_name};
}

#----------------------------------------------------------------------
# sub getElseRightParent {
#   my ($this, $node_name) = @_;
#   return $$this{else_right_parent}{$node_name};
# }

#----------------------------------------------------------------------
sub getVarInitValue {
  my ($this, $var) = @_;

  $var =~ s/_p//; 
  my $var_value = $$this{initial_values}{$var};
  if(!(defined $var_value)) {
      print "   Initial value of variable '$var' is free - set it to 0\n";
      $var_value = 0;
      $$this{initial_values}{$var} = 0;
  }

  return $var_value;
}

#----------------------------------------------------------------------
sub printOrdering {
  my $this = shift;
  my $cfg  = shift;
  my $ordering = "";
  
  my $bdd_manager = $$this{manager};
  my $level = 0;
  my $i = 0;
  do {
    $level = Cudd::ReadPerm($$bdd_manager,$i);
    $i += 1;
    
    my $var_name = "";
    if($level != -1) {
      my $var_ext = "";
      if(($level % 2) == 1) {
        $var_ext = "'";
      }

      my $num_vars = $$this{variable_names};
      $num_vars = scalar @$num_vars;
      if($level / 2 >= $num_vars) {
        $var_name = "j" . floor(($level / 2) - $num_vars);
      } else {
        $var_name = $$this{variable_names}[$level / 2];
      }
      $var_name .= $var_ext;
    }

    if (defined $cfg) {
	$ordering .= ";\n" unless $i == 1;
    } else {
	$ordering .= " -> " unless $i == 1 || $level == -1;
    }
    $ordering .= $var_name unless $level == -1;
  } until($level == -1);

  return $ordering;
}


#----------------------------------------------------------------------
sub getOrdering {
  my ($this) = @_;

  my @ordering = ();

  my $bdd_manager = $$this{manager};
  my $level = 0;
  my $i = 0;
  do {
      $level = Cudd::ReadPerm($$bdd_manager,$i);
      $i++;
      
      push(@ordering, $level);
  } until($level == -1);

  return @ordering;
}

#----------------------------------------------------------------------
sub convertBddToAdd {
  my $this = shift;
  my $bdd = shift;

  return $bdd->BddToAdd();
}

return 1;
