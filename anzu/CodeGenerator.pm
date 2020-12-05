#$Id: CodeGenerator.pm,v 1.16 2007/04/13 09:22:15 rbloem Exp $
package CodeGenerator;

return 1;

use Cudd;
use strict;

use constant OM_VERILOG                       => 0x00001;
use constant OM_FUNCTIONAL_VERILOG            => 0x00002;
use constant OM_OPTIMIZED_FUNCTIONAL_VERILOG  => 0x00004;
use constant OM_MULTIPLEXER_VERILOG           => 0x00008;

#----------------------------------------------------------------------
# Constructor
# param bdd-module bdd-module which is able to answer some questions about bdds
# param output-writer module which is able to produce some useful output
sub new
{
  my $class = shift;
  my $bdd_module = shift;
  my $output_writer = shift;

  my $object = {
    bdd_module => $bdd_module,        #O(1)
    output_writer => $output_writer,  #O(1)
    visited_nodes => {},              #O(n) n...nodes
    generated_inputs => {},           #O(k) k...variables
    generated_input_params => {},
    parents_sum => 0,
    parents_amount => 0,
    parents_max => 0,
    bdd_one => $$bdd_module{bdd_one},
    bdd_zero => $$bdd_module{bdd_zero},
    warnings => "",
    output_mode => OM_MULTIPLEXER_VERILOG
    };

  bless $object, $class;
  return $object;
}


#----------------------------------------------------------------------
sub printStatistic {
  my $this = shift;

  print "Sum=" . $$this{parents_sum} ."\n";
  print "Amount=" . $$this{parents_amount} . "\n";
  print "average parents=" . $$this{parents_sum} / $$this{parents_amount} . "\n";
  print "max=" . $$this{parents_max} . "\n";
}

#----------------------------------------------------------------------
sub printWarnings {
  my $this = shift;
  
  if (defined $$this{warnings}) {
    print $$this{warnings};
  }
}

#----------------------------------------------------------------------
# Select the method which should be used to generate the output
sub selectOutputMode() {
  my ($this, $omode) = @_;
  $$this{output_mode} = $omode;
}

#-------------------------------------------------------------------------------
sub generate {
  my ($this, $strategy, $g, $sub_functions) = @_;

  my $bdd_module = $$this{bdd_module};
  my $sharing_size = 0;
  my $output = $$this{output_writer};

  if($$this{output_mode} eq OM_VERILOG) {
#    $strategy = $bdd_module->convertBddToAdd($strategy);
    $this->generateVerilog($strategy);
  } elsif(($$this{output_mode} eq OM_FUNCTIONAL_VERILOG) ||
          ($$this{output_mode} eq OM_OPTIMIZED_FUNCTIONAL_VERILOG)) {
    $this->generateFunctionalVerilog($g, $sub_functions);
  } elsif($$this{output_mode} eq OM_MULTIPLEXER_VERILOG) {
    my @func_list;
    my @oname_list;
    foreach my $key (keys %$g) {
      my $func = $$g{$key};
      push(@func_list, $func);
      push(@oname_list, $key . "_n");
    }

    $this->generateMultiplexerVerilog(\@func_list, \@oname_list, $sub_functions);
    $sharing_size = Cudd::BDD::Size(\@func_list);
  }

  #generated functions for dependent variables, since those variables
  #are already quantified out in sub minimize
  foreach my $key (keys %$sub_functions) {
      my $func = $$sub_functions{$key};
      $func = $bdd_module->convertBddToAdd($func);
      my $assign = $this->generateSubFunctionsOptimized($func);
      my $wire = $output->generateNewWire($key."_n"); #FIXME
      $output->assignFixedValue($wire, $assign);
  }

  return $sharing_size;
}

#----------------------------------------------------------------------
sub convertBlifToVerilog {
  my ($this, $file_name) = @_;

  my @wire_decls;
  my %assign_stmts;
  
  open(BLIFFILE, "< $file_name");
  my @names;
  my $line_num = 0;
  my $state_strings = "";
  my $verilog_stmt = "";

  while(<BLIFFILE>) 
  {
    $line_num++;
    next if s/\.model.*//;
    next if s/\.inputs.*//;
    next if s/\.outputs.*//;
    chop; #REMOVE the \n character

   if((/.names.*/) || (/.end.*/)) {
     if(!($verilog_stmt eq '')) {
       push(@wire_decls, @names[@names-1]);
       $assign_stmts{@names[@names-1]} = $verilog_stmt;
     }
     
     my $name_line = $_;
     $name_line =~ s/.names //; 
     @names = split(/ /, $name_line);
     my @new_names;
     foreach my $name (@names) {
       if($name =~ /^[0-9]/) {
         push(@new_names, "v".$name);
       } else {
         push(@new_names, $name);
       }
     }
     @names = @new_names;
     $verilog_stmt = "";
   } elsif(/^(1|0)$/) {
     $verilog_stmt = $_;
   } elsif(/[10\- ]+/) {
     s/ //;
     chop; #REMOVE the one character for the output
     my @values = split(//,$_);
     my $value_index = 0;
     my $sub_stmt = "";
     foreach my $value (@values) {
       my $operator = "";
       if(!($sub_stmt eq '')) {
         $operator = " & ";
       }

       if($value eq '1') {
         $sub_stmt .= $operator . $names[$value_index];
       } elsif($value eq '0') {
         $sub_stmt .= $operator . "!".$names[$value_index];
       }	 

       $value_index++;
     }
     if(!($verilog_stmt eq '')) {
       $verilog_stmt .= ' | ';
     }
     $verilog_stmt .= $sub_stmt;

   } else {
     print "[ERROR: Parse error in blif file at line ".$line_num."]\n";
   }
  }
  close(BLIFFILE);

  return(\@wire_decls, \%assign_stmts);
}

#----------------------------------------------------------------------
# Generate verilog code using internal functions of cudd and blif 
# "intermediate" code
#
# this: CodeGenerator
# func_list: list of functions for comb outputs in terms of comb inputs (bdds)
# oname_list: list of names of comb outputs
sub generateMultiplexerVerilog {
  my ($this, $func_list, $oname_list, $sub_functions) = @_;

  
  my $blif_file_name = "cudd.blif";
  
  my $var_list_ref = $$this{bdd_module}->getAllPresentNextVarNames();
  my $var_jx = $$this{bdd_module}->{jx_var_names};
  my @var_list;
  push(@var_list, @$var_list_ref);
  push(@var_list, @$var_jx);
  
  Cudd::BDD::DumpBlif($func_list, \@var_list, $oname_list); 

  my $output = $$this{output_writer};
  my ($wire_decls, $assign_stmts) = $this->convertBlifToVerilog($blif_file_name);

  foreach my $wire (@$wire_decls) {
    if($wire =~ /^[0-9a-z]+[^(_p)|(_n)]$/) {
      $output->generateNewWire($wire);
    } 
  }

  foreach my $key (keys %$assign_stmts) {
    $output->assignFixedValue($key, $$assign_stmts{$key});
  }

  my $bdd_module = $$this{bdd_module};
  my %generated_params;
  foreach my $var (@var_list) {
    my $next_var = $var;
    $next_var =~ s/_p$/_n/;
    
    my $varname = $var;
    $varname =~ s/_p$//;
    if (($var =~ /.*_p$/)) # && (not exists $sub_functions->{$varname})) 
    {#FIXXXME: present next encoding
       my $init_value = $bdd_module->getVarInitValue($var);
       $output->generateFlipFlopConnections($var, $next_var, $init_value);
    }

    if(!defined $generated_params{$next_var}) {
      if($$this{bdd_module}->isEnvironmentVar($next_var)) {
        $output->generateInputParameter($next_var);
      } else {
        $output->generateOutputParameter($next_var);
      }
      $generated_params{$next_var} = 1;
    }

  }
}

#----------------------------------------------------------------------
# Generate functional verilog
sub generateFunctionalVerilog {
  my ($this, $g, $sub_functions) = @_;
  
  my $bdd_module = $$this{bdd_module};
  my $output = $$this{output_writer};

  my @func_list;
  my @oname_list;
  foreach my $key (keys %$g) {
    my $func = $$g{$key};
    push(@func_list, $func);
    push(@oname_list, $key . "_n");

    $func = $bdd_module->convertBddToAdd($func);

    my $next_var = $key;
    $next_var .= "_n";
    my $present_var = $key;
    $present_var .= "_p";
    
    if(not exists $sub_functions->{$key})
    {
      #FIXXXME: present next encoding
      my $init_value = $bdd_module->getVarInitValue($present_var);
      $output->generateFlipFlopConnections($present_var, $next_var, $init_value);

      if($$this{bdd_module}->isEnvironmentVar($next_var)) {
        $output->generateInputParameter($next_var);
      } else {
        $output->generateOutputParameter($next_var);
      }
    }
      
    my $tmp;
    if($$this{output_mode} eq OM_FUNCTIONAL_VERILOG) {
      my $array = $this->generateSubFunctions($func);
      $tmp = "(".join(") | (", @$array).")";
    } elsif($$this{output_mode} eq OM_OPTIMIZED_FUNCTIONAL_VERILOG) {
      $tmp = $this->generateSubFunctionsOptimized($func);
    }

    my $wire = $output->generateNewWire($key."_n"); 
    $output->assignFixedValue($wire, $tmp);
  }
}

#----------------------------------------------------------------------
# Given a part of a bdd, this function will iterate through the
# bdd and generate 
# param bdd Strategy in form of a bdd
sub generateVerilog {
  my $this = shift;
  my $strategy = shift;

  my $output = $$this{output_writer};
  $output->generateKukulaModuleCode();

  $this->generateInputOutputModules($strategy);

  foreach my $key (keys %{$$this{generated_input_params}}) {
    my $value = $$this{generated_input_params}->{$key};
    if ($value eq 0) {
      $$this{warnings} .= "[WARNING] Variable ".$key." is not restricted by any constraint! Please check your specs!\n";
      $output->assignFixedValue($key);
    }
  }
  
}
#----------------------------------------------------------------------
# Given a part of a bdd, this function will iterate through the
# bdd and generate the verilog modules. 
sub generateInputOutputModules {
  my $this = shift;
  my $strategy = shift;

  if(!defined $strategy) {
    return;
  }
  
  my @pending_nodes = ();
  push(@pending_nodes, $strategy);

  my $bdd_module = $$this{bdd_module};
  my $choose_out_0 = ""; 
  my $choose_out_1 = "";
  my $choose_out_chain_0 = ""; 
  my $choose_out_chain_1 = ""; 
  my $choose_in = "";
  my $drive = ""; 
  my $drive_chain = ""; 
  my $find_in_0 = ""; 
  my $find_in_1 = ""; 
  my $find_out = ""; 
  my $output = $$this{output_writer};
  my $val_in = ""; 
  my $val_out = ""; 
  my $var_val = "";
  my $val_out_chain = ""; 

  for(my $i = 0; $i < (scalar @pending_nodes); $i++) {
    $strategy = $pending_nodes[$i];
    
    my $strategy_name = $strategy->{node_name};
    if(defined $$this{visited_nodes}{$strategy_name}) {
      next;
    }
    
    $$this{visited_nodes}{$strategy_name} = 1; #mark node as visited
    
# some static stuff
    my $node_parents = $bdd_module->getParentList($strategy);
    if(defined $node_parents) {
      $$this{parents_sum} = $$this{parents_sum} + @$node_parents;
      $$this{parents_amount} = $$this{parents_amount} + 1;
      if(@$node_parents > $$this{parents_max}) {
        $$this{parents_max} = @$node_parents;
      }
    }
    
        
    my ($is_input, $is_next, $is_environment) = $bdd_module->getVarClassification($strategy);
    my $node_index = Cudd::NodeReadIndex($strategy->{'node'});

    my $code_generated = 0;
#   foreach my $item (@{$$this{generated_inputs}}) {
#     if($item == $node_index) {
#       $code_generated = 1;
#     }
#   }
    if(defined $$this{generated_inputs}{$node_index}) {
      $code_generated = 1;
    }

#    print "Var: ", $node_index, " Env ", $is_environment , " NXT ", $is_next,"\n";
#    if(($code_generated == 0) && $is_environment && !$is_next) {
    my $in_wire = $bdd_module->getAccordingNextVar($strategy);
    
    if(($code_generated == 0)) {	
#    push(@{$$this{generated_inputs}}, $node_index);

      $$this{generated_inputs}{$node_index} = 1;
      
      my $register_out_wire = $bdd_module->getAccordingPresentVar($strategy);
      my $init_value = $bdd_module->getVarInitValue($bdd_module->getVariableName($strategy));
      

      if (!$is_next) {
#        $output->generateNewWire($register_out_wire);
        $output->generateFlipFlopConnections($register_out_wire, $in_wire, $init_value);	  
      }
      
      if (defined $$this{generated_input_params}{$in_wire}) {
        if ($$this{generated_input_params}{$in_wire} eq 0) {
          $$this{generated_input_params}{$in_wire}=1;
        } 
      }
      
      if (((!defined $$this{generated_input_params}{$in_wire}))) {
        $$this{generated_input_params}{$in_wire}=1;
        if($is_environment) {      
          $output->generateInputParameter($in_wire);
        } else {
          $output->generateOutputParameter($in_wire);
          if (!$is_next) {
            $$this{generated_input_params}{$in_wire}=0;	  
          }
        }
      }
    }

#    if(($code_generated == 0) && $is_environment && $is_next &&
#       (!defined $$this{generated_input_params}{$in_wire})) {
#	my $in_wire = $bdd_module->getAccordingNextVar($strategy);
#	$$this{generated_input_params}{$in_wire}=1;
#	$output->generateInputParameter($in_wire);
#    }
    
    if($is_input) {
      ($find_out, $choose_out_0, $choose_out_1, $choose_out_chain_0,
       $choose_out_chain_1, $find_in_0, $find_in_1, $choose_in, $var_val) = $this->generateInputWireNames($strategy, $strategy_name);
      
      if(defined $find_out) {
        $find_out = $output->generateNewWire($find_out);
        $choose_out_0 = $output->generateNewWire($choose_out_0);
        $choose_out_1 = $output->generateNewWire($choose_out_1);
        
        $output->generateInputNodeConnections($find_out, $choose_out_0, $choose_out_1, $choose_out_chain_0,
                                              $choose_out_chain_1, $find_in_0, $find_in_1, $choose_in, $var_val);
      }
    } else {
      
      ($find_out, $drive, $val_out, $choose_out_0, $choose_out_1, 
       $choose_out_chain_0, $choose_out_chain_1, $find_in_0, 
       $find_in_1, $val_in, $val_out_chain, $drive_chain, $choose_in) = $this->generateOutputWireNames($strategy, $strategy_name);
      
      if(defined $find_out) {
        $find_out = $output->generateNewWire($find_out);
        $drive = $output->generateNewWire($drive);
        $val_out = $output->generateNewWire($val_out);
        $choose_out_0 = $output->generateNewWire($choose_out_0);
        $choose_out_1 = $output->generateNewWire($choose_out_1);
        
        $output->generateOutputNodeConnections($find_out, $drive, $val_out, $choose_out_0, $choose_out_1, 
                                               $choose_out_chain_0, $choose_out_chain_1, $find_in_0, 
                                               $find_in_1, $val_in, $val_out_chain, $drive_chain, $choose_in);
      }
    }
    
    my $t = $bdd_module->getThenChild($strategy);
    
#  if((!$bdd_module->isBddOne($t)) && (!$bdd_module->isBddZero($t))) {
    if(( $$this{bdd_one} != $t) && ( $$this{bdd_zero} != $t)) {
#      $this->generateInputOutputModules($t);
      push(@pending_nodes, $t);
    }
    
    my $e = $bdd_module->getElseChild($strategy);
    
#  if((!$bdd_module->isBddOne($e)) && (!$bdd_module->isBddZero($e))) {
    if(( $$this{bdd_one} != $e) && ( $$this{bdd_zero} != $e)) {
#      $this->generateInputOutputModules($e);
      push(@pending_nodes, $e);
    }
    
  }
}

#----------------------------------------------------------------------
# generate the names of the wires for an input module
sub generateInputWireNames {
  my ($this, $node, $node_name) = @_;

  my $bdd_module = $$this{bdd_module};
  my $output = $$this{output_writer};

#    input find_in_0, find_in_1, choose_in, var_val, choose_out_chain_0, choose_out_chain_1
#    output find_out, choose_out_0, choose_out_1


  my $node_parents = $bdd_module->getParentList($node);

  my $then_child = $bdd_module->getThenChild($node);
  my $else_child = $bdd_module->getElseChild($node);

  my $find_in_0 = "find_out_" . $else_child->{node_name};

#  if($bdd_module->isBddOne($else_child)) {
  if($else_child == $$this{bdd_one}) {
    $find_in_0 = $output->getOneWire();
#  } elsif($bdd_module->isBddZero($else_child)) {
  } elsif($else_child == $$this{bdd_zero}) {
    $find_in_0 = $output->getZeroWire();
  }

  my $find_in_1 = "find_out_" . $then_child->{node_name};
#  if($bdd_module->isBddOne($then_child)) {
  if($then_child == $$this{bdd_one}) {
    $find_in_1 = $output->getOneWire();
#  } elsif($bdd_module->isBddZero($then_child)) {
  } elsif($then_child == $$this{bdd_zero}) {
    $find_in_1 = $output->getZeroWire();
  }

  my $choose_in = "choose_out_X_123456789";
  if((!defined $node_parents) || (@$node_parents == 0)) {
    $choose_in = "find_out_" . $node_name;
  } else {
    my $num_parents = @$node_parents;
    my $last_parent = @$node_parents[$num_parents - 1];
    if($bdd_module->getElseChild($last_parent) == $node) {
      $choose_in = "choose_out_0_" . $last_parent->{node_name};
    } else {
      $choose_in = "choose_out_1_" . $last_parent->{node_name};
    }
  }

  my $var_val = $bdd_module->getVariableName($node);
#  print "Var ",$var_val,"\n";
  
  my $choose_out_chain_0 = $output->getZeroWire();
  my $else_child_parents = $bdd_module->getParentList($else_child);

  if(((scalar @$else_child_parents) > 1) && (@$else_child_parents[0] != $node)) {
#    print "else_child_parents=" . @$else_child_parents . "\n";
#    my $sibling_parent_of_else_child = $bdd_module->listGetPrevious($else_child_parents, $node);
    my $sibling_parent_of_else_child = $bdd_module->getElseLeftParent($node_name);
    if($bdd_module->getElseChild($sibling_parent_of_else_child) == $else_child) {
      $choose_out_chain_0 = "choose_out_0_" . $sibling_parent_of_else_child->{node_name};
    } else {
      $choose_out_chain_0 = "choose_out_1_" . $sibling_parent_of_else_child->{node_name};
    }
  }

  my $choose_out_chain_1 = $output->getZeroWire();
  my $then_child_parents = $bdd_module->getParentList($then_child);

  if(((scalar @$then_child_parents) > 1) && (@$then_child_parents[0] != $node)) {
#    my $sibling_parent_of_then_child = $bdd_module->listGetPrevious($then_child_parents, $node);
    my $sibling_parent_of_then_child = $bdd_module->getThenLeftParent($node_name);
    if($bdd_module->getThenChild($sibling_parent_of_then_child) == $then_child) {
      $choose_out_chain_1 = "choose_out_1_" . $sibling_parent_of_then_child->{node_name};
    } else {
      $choose_out_chain_1 = "choose_out_0_" . $sibling_parent_of_then_child->{node_name};
    }
  }

  my $find_out = "find_out_" . $node_name;
  my $choose_out_0 = "choose_out_0_" . $node_name;
  my $choose_out_1 = "choose_out_1_" . $node_name;

  return($find_out, $choose_out_0, $choose_out_1, $choose_out_chain_0,
         $choose_out_chain_1, $find_in_0, $find_in_1, $choose_in, $var_val);
}


#----------------------------------------------------------------------
# generate the names of the wires for an input module
sub generateOutputWireNames {
  my $this = shift;
  my $node = shift;
  my $node_name = shift;

  my $bdd_module = $$this{bdd_module};
  my $output = $$this{output_writer};

# input find_in_0, find_in_1, choose_in, choose_out_chain_0, choose_out_chain_1, val_in, val_out_chain, drive_chain, 
# output find_out, drive, val_out, choose_out_0, choose_out_1

  my ($find_out, $choose_out_0, $choose_out_1, $choose_out_chain_0,
      $choose_out_chain_1, $find_in_0, $find_in_1, $choose_in) = $this->generateInputWireNames($node, $node_name);

  my $val_in = $output->getZeroWire();

  my $left_sibling = $bdd_module->getLeftSibling($node);
  my $val_out_chain = $output->getZeroWire();
  my $drive_chain = $output->getZeroWire();
  if(defined $left_sibling) {
    $val_out_chain = "val_out_" . $left_sibling->{node_name};
    $drive_chain = "drive_" . $left_sibling->{node_name};
  }

  my $right_sibling = $bdd_module->getRightSibling($node);
  if(! defined $right_sibling) {
    my $out_wire = $bdd_module->getAccordingNextVar($node);
    my $in0 = $output->getZeroWire();
    my $in1 = "val_out_" . $node_name;
    my $select = "drive_" . $node_name;

    my $register_out_wire = $bdd_module->getAccordingPresentVar($node);
    my $init_value = $bdd_module->getVarInitValue($bdd_module->getVariableName($node));

    $output->generateMultiplexerConnections($out_wire, $in0, $in1, $select);

    
    if((!(defined $$this{generated_input_params}{$out_wire}))) {
#      $output->generateNewWire($register_out_wire);
      $$this{generated_input_params}{$out_wire} = 1;
      $output->generateFlipFlopConnections($register_out_wire, $out_wire, $init_value);
      $output->generateOutputParameter($out_wire);
    }
  }

  my $drive = "drive_" . $node_name;
  my $val_out = "val_out_" . $node_name;

  return($find_out, $drive, $val_out, $choose_out_0, $choose_out_1, 
         $choose_out_chain_0, $choose_out_chain_1, $find_in_0, 
         $find_in_1, $val_in, $val_out_chain, $drive_chain, $choose_in);
}

#----------------------------------------------------------------------
# takes a bdd and walks down recursivle. on the way up in generates an
# array of strings. each string defines a path from the current node to
# the BDDOne node. the current node will be "and'ed" in front of each string
# in the array.
sub generateSubFunctions {
  my ($this, $bdd) = @_;
  
  if($bdd == $$this{bdd_one}) {
    my @result = ("");
    return \@result;
  }
  if($bdd == $$this{bdd_zero}) {
    return undef;
  }
  
  my $then_list = $this->generateSubFunctions($$this{bdd_module}->getThenChild($bdd));
  my $else_list = $this->generateSubFunctions($$this{bdd_module}->getElseChild($bdd));
  
  my @result = ();
  my $var = $$this{bdd_module}->getVariableName($bdd);
#  if((scalar @then_list) >= 1) {
    foreach my $element (@$then_list) {
#      print "Element=" . $element . "\n";
      if($element eq "") {
        push(@result, $var);
      } else {
        push(@result, $var . " & " . $element);
      }
    }
#  }
#  if((scalar @else_list) >= 1) {
    foreach my $element (@$else_list) {
#      print "Element=" . $element . "\n";
      if($element eq "") {
        push(@result, "!" . $var);
      } else {
        push(@result, "!" . $var . " & " . $element);
      }
    }
#  }

  return \@result;
}


#----------------------------------------------------------------------
# takes a bdd and walks down recursivle. on the way up in generates a
# string holding the path from the current node to the one node. 
# this method is an optimization of generateSubFunctions, because it
# generates a smaller string. 
sub generateSubFunctionsOptimized {
  my ($this, $bdd) = @_;
  
  if($bdd == $$this{bdd_one}) {
    return "";
  }
  if($bdd == $$this{bdd_zero}) {
    return undef;
  }
  
  my $then_path = $this->generateSubFunctionsOptimized($$this{bdd_module}->getThenChild($bdd));
  my $else_path = $this->generateSubFunctionsOptimized($$this{bdd_module}->getElseChild($bdd));
  
  my $var = $$this{bdd_module}->getVariableName($bdd);



  my $result = undef;
  if(defined $then_path) {
    if(!($then_path eq "")) {
      $then_path = " & (" . $then_path . ")";
    }
    $result = "(" . $var . $then_path . ")";
  }
  
  if(defined $else_path) {
    if(!($else_path eq "")) {
      $else_path = " & (" . $else_path . ")";
    }
    if(defined $result) {
      $result = $result . " | ";
    } else {
      $result = "";
    }
	
    $result = $result . "(!" . $var . $else_path . ")";
  }
  
  return $result;
}
