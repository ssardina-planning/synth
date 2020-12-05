#$Id: CFGParser.pm,v 1.4 2007/04/13 09:22:15 rbloem Exp $
#----------------------------------------------------------------------
# Encapsulation of the configuration file parsing
#----------------------------------------------------------------------

package CFGParser;

use LTL;
use Cudd;
use strict; #encapsulates our data so nobody can take away them
use POSIX; # qw(ceil floor);


use constant PARAM_REQUIRED                 => 0x00001;
use constant PARAM_PARSE_WITH_LTL           => 0x00002;
use constant PARAM_INPUT_VARS_ALLOWED       => 0x00004;
use constant PARAM_OUTPUT_VARS_ALLOWED      => 0x00008;
use constant PARAM_ONLY_INPUT_IN_NEXT_STATE => 0x00010;
use constant PARAM_NO_TEMPORAL_OPERATORS    => 0x00020;
use constant PARAM_NO_DOUBLE_X              => 0x00040;
use constant PARAM_SUBNODES_ONLY_X          => 0x00080;
use constant PARAM_CHECK_ROOT_G             => 0x00100;
use constant PARAM_SUBSUBNODES_NO_TEMP_OP   => 0x00200;
use constant PARAM_CHECK_ROOT_GF            => 0x00400;

use constant PARAM_MULTIPLE_FORMULAS        => 0x00800;
use constant PARAM_SUBSTITUTE_FORMULA       => 0x01000;
use constant PARAM_ORDERING_RELATION        => 0x02000;
use constant PARAM_ALLOW_SPECIAL_NEXT_OP    => 0x04000;
use constant PARAM_JX_VARS_ALLOWD           => 0x08000;

use constant PARAM_IS_INITIAL_VALUE         => 0x10000;
use constant PARAM_NEEDS_CONCATENATION      => 0x20000;
return 1;


#----------------------------------------------------------------------
#constructor
sub new
{
  my $class_name = shift; #the first parameter is always the class name
  my $config_file = shift;
  my $object = {
                config_file => $config_file,
                parse_error => 0,
#                initial_values => {},
                formulas => {},               # hash of lists
                parse_trees => {},            # hash of lists
                # this hash tells what todo with which section (bitwise)
                required => {ENV_INITIAL      => PARAM_REQUIRED | PARAM_PARSE_WITH_LTL | PARAM_INPUT_VARS_ALLOWED |
                                                 PARAM_NO_TEMPORAL_OPERATORS | PARAM_IS_INITIAL_VALUE,

                             SYS_INITIAL      => PARAM_REQUIRED | PARAM_PARSE_WITH_LTL | PARAM_OUTPUT_VARS_ALLOWED |
                                                 PARAM_INPUT_VARS_ALLOWED | PARAM_NO_TEMPORAL_OPERATORS |
                                                 PARAM_IS_INITIAL_VALUE,

                             ENV_TRANSITIONS  => PARAM_REQUIRED | PARAM_PARSE_WITH_LTL | 
                                                 PARAM_INPUT_VARS_ALLOWED | PARAM_OUTPUT_VARS_ALLOWED |
                                                 PARAM_ONLY_INPUT_IN_NEXT_STATE | #PARAM_CHECK_ROOT_G | 
                                                 PARAM_NO_DOUBLE_X | PARAM_SUBNODES_ONLY_X | PARAM_MULTIPLE_FORMULAS |
                                                 PARAM_NEEDS_CONCATENATION,

                             SYS_TRANSITIONS  => PARAM_REQUIRED | PARAM_PARSE_WITH_LTL | 
                                                 PARAM_INPUT_VARS_ALLOWED | PARAM_OUTPUT_VARS_ALLOWED |
                                                 # PARAM_CHECK_ROOT_G | 
                                                 PARAM_NO_DOUBLE_X | PARAM_SUBNODES_ONLY_X | 
                                                 PARAM_SUBSTITUTE_FORMULA | PARAM_MULTIPLE_FORMULAS | 
                                                 PARAM_NEEDS_CONCATENATION,

                             ENV_FAIRNESS     => PARAM_REQUIRED | PARAM_PARSE_WITH_LTL | 
                                                 PARAM_OUTPUT_VARS_ALLOWED |
                                                 PARAM_SUBSUBNODES_NO_TEMP_OP | PARAM_INPUT_VARS_ALLOWED |
                                                 PARAM_MULTIPLE_FORMULAS |
                                                 PARAM_CHECK_ROOT_GF,

                             SYS_FAIRNESS     => PARAM_REQUIRED | PARAM_PARSE_WITH_LTL | 
                                                 PARAM_INPUT_VARS_ALLOWED | PARAM_OUTPUT_VARS_ALLOWED | 
                                                 PARAM_SUBSUBNODES_NO_TEMP_OP |
                                                 PARAM_MULTIPLE_FORMULAS |
                                                 PARAM_CHECK_ROOT_GF,

                             INPUT_VARIABLES  => PARAM_REQUIRED | PARAM_MULTIPLE_FORMULAS,

                             OUTPUT_VARIABLES => PARAM_REQUIRED | PARAM_MULTIPLE_FORMULAS,
                             
                             FORCE_ORDERING   => PARAM_ORDERING_RELATION | PARAM_INPUT_VARS_ALLOWED | 
                                                 PARAM_OUTPUT_VARS_ALLOWED | PARAM_JX_VARS_ALLOWD |
                                                 PARAM_ALLOW_SPECIAL_NEXT_OP
                           }
               };
  bless $object, $class_name;
  return $object;
}


#----------------------------------------------------------------------
#sets the path-string for the config file
sub setConfigFile {
  my $this = shift;
  my $config_file = shift;

  $$this{config_file} = $config_file;
}

#----------------------------------------------------------------------
# read in the config file
sub readConfigFile {
  my $this = shift;
  
  open(CF, $$this{config_file}) or die("I could not open the config-file ".$$this{config_file});
  my $formula = "";
  my $section_name = "";

  while(<CF>) 
  {
    chop;
    s/\#.*//;			# discard comments
    s/\s+$//;			# discard trailing blanks

    if(/^\s*\[.*\]\s*$/)
    {
      $this->addFormulaToSection(\$formula, $section_name);
      $section_name = $_;
      $section_name =~ s/\[//;
      $section_name =~ s/\]//;
    }
    elsif(/;/)
    {
      $formula .= $_;
      $formula =~ s/\s+$//; 
    }
    elsif(! /^$/)
    {
      $formula .= $_;
    }
  }

  $this->addFormulaToSection(\$formula, $section_name);
  close (CF);
};

# sub getInitialValues {
#   my $this = shift;

#   if ($$this{initial_values} eq {}) {
#       print "Non initial values set yet\n";
#   }
#   return $$this{initial_values};
# }

#----------------------------------------------------------------------
# add a formula for a section to the internal variables. If 
# a section with the given name was already specified, a warning
# will be raised. Anyway the new definition will be used.
#
# @param The formula which should be added
# @param The section name for which the formula was specified
sub addFormulaToSection {
  my $this = shift;
  my $formula = shift;
  my $section_name = shift;

  my @result = ();
  my $required = $$this{required};

  if($$formula ne "")
  {
    $$formula =~ s/\s*;\s*$//;  # remove the trailing semicolon

    if(($$required{$section_name} & PARAM_MULTIPLE_FORMULAS) != 0)
    {
      @result = split(";", $$formula);
    }
    else
    {
      $$formula =~ s/;/\*/g;
      push(@result, $$formula);
    }

  }
  
  if($section_name ne "")
  {
    if(defined($$this{formulas}->{$section_name}) && !(($$required{$section_name} & PARAM_MULTIPLE_FORMULAS) != 0))
    {
      print "[WARNING]: Multiple definition of section " . $section_name . "\n";
    }
    push(@{$$this{formulas}->{$section_name}},@result);
    $$formula = "";
  }
  else
  {
    if($$formula ne "")
    {
      print "[ERROR]: formula " . $$formula . " can not be associated with a section\n";
    }
  }
}
 
#----------------------------------------------------------------------
# check if variables are alphanumeric characters only
#
# param variable strin
sub checkVariableSyntax {
  my $this = shift;
  my $variables = shift;
  my $special_next_allowed = shift || 0;

  my @vars = @$variables;

  while(@vars)
  {
    my $variable = pop(@vars);
    my $tmp_var = $variable;
    if($special_next_allowed) {
      $tmp_var =~ s/[a-zA-Z\']+[\'\w\*]*//;
    } else {
      $tmp_var =~ s/[a-zA-Z]+\w*//;
    }

    if($tmp_var ne "")
    {
      $$this{parse_error}++;
      print "[ERROR]: illegal variable name " . $variable . "\n";
    }
  }
}

#----------------------------------------------------------------------
# Check if there are two X in scope of one variable (recursive!)
# param current node of the syntax tree
# param currently encountered num_of_x (optional)
sub check4XX {
  my $this = shift;
  my $node = shift;
  my $num_of_x = shift;
  if(!defined($num_of_x)) 
  {
    $num_of_x = 0;
  }

  if(($node->Type eq 'temporalop') && ($node->Value eq 'X'))
  {
    $num_of_x++;
  }

  if($num_of_x > 1)
  {
    return $num_of_x;
  }

  my $result = 0;
  if(defined($node->Left)) 
  {
    $result += $this->check4XX($node->Left, $num_of_x);
  }

  if(defined($node->Right)) 
  {
    $result += $this->check4XX($node->Right, $num_of_x);
  }

  return $result;
}


#----------------------------------------------------------------------
# Check if only specified variables (and not other varibles) written after 
# a next operator (X).
# param current node of the syntax tree
# param space seperated list of allowed variables
# return 0 ... ok, otherwise ... not ok
sub check4AllowedVarsAfterX {
  my $this = shift;
  my $node = shift;
  my $allowed_vars = shift;

  my $unallowed_count = shift;
  if(!defined($unallowed_count))
  {
    $unallowed_count = 0;
  }

  if(!defined($node))
  {
    return 0;
  }

  if(($node->Type eq 'temporalop') && ($node->Value eq 'X'))
  {
    my @empty_array = ("TRUE", "FALSE");
    my @undeclared_vars = $this->getUndeclaredVariables($node->Left, \@empty_array, $allowed_vars);
    push(@undeclared_vars, $this->getUndeclaredVariables($node->Right, \@empty_array, $allowed_vars));

    return scalar @undeclared_vars;
  }
  else
  {
    $this->check4AllowedVarsAfterX($node->Left, $allowed_vars);
    $this->check4AllowedVarsAfterX($node->Right, $allowed_vars);
  }
}


#----------------------------------------------------------------------
# Check if there are two X in scope of one variable (recursive!)
# param current node of the syntax tree
# param allowed temporal operators (e.g. "FGX", only F,G,X is allowed)
# return 0 ... ok, otherwise ... not ok
sub check4AllowedTemporalOps {
  my $this = shift;
  my $node = shift;
  my $allowed_ops = shift;
  
  if(!defined($node))
  {
    return 0;
 }

  if(!defined($allowed_ops)) 
  {
    $allowed_ops = "";
  }

  if(($node->Type eq 'temporalop') && (index($allowed_ops, $node->Value) == -1) )
  {
    return 1;
  }

  my $result = 0;
  if(defined($node->Left)) 
  {
    $result += $this->check4AllowedTemporalOps($node->Left, $allowed_ops);
  }

  if(defined($node->Right)) 
  {
    $result += $this->check4AllowedTemporalOps($node->Right, $allowed_ops);
  }

  return $result;
}


#----------------------------------------------------------------------
# Check if the given formula is a valid transition formula
# param the root node of the parse tree
# param the formula as string (for error handling)
# param the section in which the formula is defined
sub check4GF {
  my $this = shift;
  my $root_node = shift;
  my $formula = shift;
  my $key = shift;

  if(($root_node->Type eq 'atom') && (!defined($root_node->Right)) && (!defined($root_node->Left)) &&
     (($root_node->Value eq 'TRUE') || ($root_node->Value eq 'FALSE')))
  {
    return 0;
  }

  if(($root_node->Type eq 'temporal') && ($root_node->Value eq 'X'))
  {
    $root_node = $root_node->Right;
  }

  if (!defined($root_node))
  {
    return 1;
  }
  
#  print $formula . " ( " . $root_node->ToString() . ") : " . $root_node->Value . "\n";
#  print $formula . " ( " . $root_node->ToString() . ") : " . $root_node->Left->Value . " <--L-- " . $root_node->Value . "[" . $root_node->Type . "]" . " --R--> " . $root_node->Right->Value . "\n";
  if(!(($root_node->Type eq 'binaryop') && ($root_node->Value eq 'R')))
  {
    return 1;
  }
  
  if(!defined($root_node->Left) || !(($root_node->Left->Type eq 'atom') && !($root_node->Value eq 'FALSE')))
  {
    return 1;
  }

  if(!defined($root_node->Right))
  {
    return 1;
  }

  my $sub_tree = $root_node->Right;

  if(!(($sub_tree->Type eq 'binaryop') && ($sub_tree->Value eq 'U')))
  {
    return 1;
  }

  if(!defined($root_node->Left) || !(($sub_tree->Left->Type eq 'atom') && !($sub_tree->Value eq 'TRUE')))
  {
    return 1;
  }

  return 0;
}


#----------------------------------------------------------------------
# Check if the given formula has g as its root node
# 0 root node is g, 1 root node is not the temporal op g
sub check4RootNodeG {
  my $this = shift;
  my $root_node = shift;

#  print "check4RootNodeG: " . $root_node->ToString() . " : " . $root_node->Value . "\n";

  if(($root_node->Type eq 'temporalop') && ($root_node->Value eq 'X'))
  {
    $root_node = $root_node->Left;
  }

  if(!defined($root_node))
  {
    return 1;
  }

  if(!(($root_node->Type eq 'binaryop') && ($root_node->Value eq 'R')))
  {
    return 1;
  }
  elsif(!(($root_node->Left->Type eq 'atom') && !($root_node->Value eq 'FALSE')))
  {
    return 1;
  }

  return 0;
}

#----------------------------------------------------------------------
# Check if the given nodes do not contain other temporal operators
# except X
# param root_node
# 0 ok, otherwise there are other temporal ops than X
sub check4SubNodesOnlyX {
  my $this = shift;
  my $root_node = shift;

  my $wrong_node_count = 0;
  $wrong_node_count += $this->check4AllowedTemporalOps($root_node->Left, "X");
  $wrong_node_count += $this->check4AllowedTemporalOps($root_node->Right, "X");

  return $wrong_node_count;
}


#----------------------------------------------------------------------
# Check if there are any temporal operators in the given syntax tree.
# Return the number of temporal ops found
# param a node of the parse tree
# return 0 ... no temp ops found, else ... there is at least 1 tmp op
sub check4NoTemporalOps
{
  my $this = shift;
  my $node = shift;

  if(!defined($node))
  {
    return 0;
  }

  my $num_of_tmp_ops = shift;   #optional parameter

  if(!defined($node))
  {
    return 0;
  }
  
  if(!defined($num_of_tmp_ops)) 
  {
    $num_of_tmp_ops = 0;
  }

  if(($node->Type eq 'temporalop'))
  {
    $num_of_tmp_ops++;
  }

  if($num_of_tmp_ops > 1)
  {
    return $num_of_tmp_ops;
  }

  my $result = 0;
  if(defined($node->Left)) 
  {
    $result += $this->check4NoTemporalOps($node->Left, $num_of_tmp_ops);
  }

  if(defined($node->Right)) 
  {
    $result += $this->check4NoTemporalOps($node->Right, $num_of_tmp_ops);
  }

  return $result;
}


#----------------------------------------------------------------------
# Collect variables used in a syntax tree
# param current node of the syntax tree
# return list of variables
sub collectUsedVariables {
  my $this = shift;
  my $node = shift;
  
  my $merged = {};

  if(!defined($node))
  {
    return {};
  }

  if(($node->Type eq 'atom') )
  {
    my $variable = $node->Value;
    $variable =~ s/=[0|1]\s*$//;

    $$merged{$variable} = 0;
  }

  my $result_left = {};
  my $result_right = {};
  if(defined($node->Left)) 
  {
    $result_left = $this->collectUsedVariables($node->Left);
  }

  if(defined($node->Right)) 
  {
    $result_right = $this->collectUsedVariables($node->Right);
  }


  # add found variable and merge hashes


  while ( (my $k,my $v) = each(%$result_left) ) {
    $$merged{$k} = $v;
  }
  while ( (my $k,my $v) = each(%$result_right) ) {
    $$merged{$k} = $v;
  }


  return $merged;
}


#----------------------------------------------------------------------
# Find all variables in a syntax tree, which are not member of a
# given set of variables
# param root node of syntax tree
# param array ref containing variables, which should be ignored 
# param string containing space separated list of allowed variables
sub getUndeclaredVariables {
  my $this = shift;
  my $node = shift;
  my $ignored_vars = shift;
  my $allowed_var_array = shift;

  my $allowed_variables = {};

  foreach my $var (@$allowed_var_array) {
    $$allowed_variables{$var} = 0;
  }

  my $variables = $this->collectUsedVariables($node);
  
  foreach (@$ignored_vars)
  {
    delete($$variables{$_});
  }


  my @this_not_that = ();
  foreach (keys %$variables) {
    push(@this_not_that, $_) unless exists $$allowed_variables{$_};
  }

  return @this_not_that;
}


#----------------------------------------------------------------------
# Check if all variables used have actually been declared
# and if only allowed variables have been used
# param root node of syntax tree
# param section name (for error msgs)
# param list of declared variables
# param list of allowed variables
sub check4Variables {
  my $this = shift;
  my $node = shift;
  my $section_name = shift;
  my $existing_variables = shift;
  my $allowed_variables = shift;

  my @ignore = ("TRUE", "FALSE");

  my @undeclared_vars =  $this->getUndeclaredVariables($node, \@ignore, $existing_variables);
  if (scalar @undeclared_vars > 0)
  {
    $$this{parse_error}++;
    print "[ERROR]: found undeclared variable(s)"  . " in section [" . $section_name . "]: " . join(",", sort(@undeclared_vars)) . "\n";
  }

  push(@ignore, @undeclared_vars);


  my @disallowed_vars = $this->getUndeclaredVariables($node, \@ignore, $allowed_variables);
  if (scalar @disallowed_vars > 0)
  {
    $$this{parse_error}++;
    print "[ERROR]: variable(s)"  . " not allowed in section [" . $section_name . "]: " . join(",", sort(@disallowed_vars)) . "\n";
  }
}


#----------------------------------------------------------------------
# Check if all needed sections of the configuration file do exist.
# Examine if there are no unknown sections defined.
sub checkDefinedSections {
  my $this = shift;

  my @elements;
  my $formulas = $$this{formulas};

  while ( my ($key, $value) = each %$formulas)
  {
    if(($key ne "ENV_INITIAL") &&
       ($key ne "SYS_INITIAL") &&
       ($key ne "ENV_TRANSITIONS") &&
       ($key ne "SYS_TRANSITIONS") &&
       ($key ne "ENV_FAIRNESS") &&
       ($key ne "SYS_FAIRNESS") &&
       ($key ne "INPUT_VARIABLES") &&
       ($key ne "OUTPUT_VARIABLES") &&
       ($key ne "FORCE_ORDERING"))
    {
      print "[WARNING]: illegal section " . $key . " will be ignored\n";
    }
    else
    {
      push(@elements, $key);
    }
  }

  my $num_elements = @elements; 

  my $hash_ref = $$this{required};
  my %tmp_hash = %$hash_ref;
  my $tmp_required = \%tmp_hash;

  for(my $i=0; $i<$num_elements; $i++)
  {
    my $prev_size = keys(%$tmp_required);
    delete $tmp_required->{$elements[$i]};
    my $act_size = keys(%$tmp_required);
    if(($prev_size != $act_size) && ($$formulas{$elements[$i]} eq ""))
    {
      print "[WARNING] mandatory section " . $elements[$i] . " is empty\n";
    }
  }

  my @missing_elements = keys(%$tmp_required);
  while(@missing_elements)
  {
    my $key_name = pop(@missing_elements);
    if(($$tmp_required{$key_name} & PARAM_REQUIRED) == 0)
    {
      $$this{$key_name} = "";
    }
    else
    {
      $$this{parse_error}++;
      print "[ERROR]: specification of section " . $key_name . " is mandatory\n";
    }
  }
}

#----------------------------------------------------------------------
# params formula
# returns root-node of the parse-tree or "die" if an error occurs
sub createParseTree {
  my $this = shift;
  my $formula = shift;

  my $parsed_formula = LTL->new($formula);
  my $normalized_formula = $parsed_formula->Normalize;
  my $simplified_formula = $normalized_formula->Simplify;
  return $simplified_formula;
}

#----------------------------------------------------------------------
# check if there are two elements in the array which have the same name
sub checkVariableUniqueness {
  my $this = shift;
  my $vars = shift;

  my $prev = "";
  my @sorted_array = sort(@$vars);
  my @out = grep($_ ne $prev && ($prev = $_), @sorted_array); # make @out unique

  return(scalar @sorted_array -  scalar @out); # are vars and out identical?
}

#----------------------------------------------------------------------
# triggers the parsing process
sub parse {
  my $this = shift;

  $this->readConfigFile();

  $this->checkDefinedSections();
  $this->checkVariableSyntax($$this{formulas}->{INPUT_VARIABLES});
  $this->checkVariableSyntax($$this{formulas}->{OUTPUT_VARIABLES});
  if(defined $$this{formulas}->{FORCE_ORDERING}) {
    $this->checkVariableSyntax($$this{formulas}->{FORCE_ORDERING}, 1);
  }

  if($this->checkVariableUniqueness($this->getVariableList()) != 0)
  {
    $$this{parse_error}++;
    print "[ERROR]: Duplicate variables in input/output section!\n";
  }

  my $required = $$this{required};
  my @keys = keys (%$required);

  foreach my $key (@keys)
  {
    print "Parse $key\n";
# Extract value from initial BDD
#     if(($$required{$key} & PARAM_IS_INITIAL_VALUE) != 0) {
#       foreach my $var_list (@{$$this{formulas}->{$key}}) {
# 	#FIXMEE: what if (a=1)*(b=0)
#         my @vars = split('\*', $var_list);
#         for my $var (@vars) {
#           my $var_name = $var;
#           $var_name =~ s/=.*$//;
#           my $var_value = $var;
#           $var_value =~ s/^.*=//;
#           $$this{initial_values}{$var_name} = $var_value;
#         }
#       }
#     }
    if(($$required{$key} & PARAM_PARSE_WITH_LTL) != 0)    # parse
    {
      for my $formula (@{$$this{formulas}->{$key}})
      {
        my $parse_tree = eval { $this->createParseTree($formula); };
        if($@)
        {
          $$this{parse_error}++;
          chop($@);
          print "[ERROR]: ". $@ . " in section " . $key. "\n";
        }
        else
        {
          push(@{$$this{parse_trees}->{$key}}, $parse_tree);
          $this->doParseTreeChecks($key, $parse_tree, $formula);

#generate state automata for new variable if there are other temporal ops than GF in system transitions

        }
      }
    } else {
      for my $formula (@{$$this{formulas}->{$key}}) {
        $this->doNonParseTreeChecks($key, $formula);
      }
    }
  }

  if($$this{parse_error} != 0)
  {
    print "[TERMINATE]: Too many errors (" . $$this{parse_error} . ") in config file! I give up ;-)\n";
    exit;
  }
}

#----------------------------------------------------------------------
# according to the configured options above this method will do all
# activated checks on the formula
# param the section key
# param the resulting parse tree
# param the formula (for error reporting)
sub doNonParseTreeChecks
{
  my ($this, $key, $formula) = @_;

  my $required = $$this{required};

  my $input_vars = $$this{formulas}->{INPUT_VARIABLES};
  my $output_vars = $$this{formulas}->{OUTPUT_VARIABLES};

  my @result = split('\*', $formula);
  foreach my $var (@result) {
    my $orig_var_name = $var;
    if(($$required{$key} & PARAM_ALLOW_SPECIAL_NEXT_OP) != 0) {

      if(substr($var, length($var)-1,1) eq "'") {
        $var = substr($var, 0, length($var)-1);
      }

      my $all_vars = join("", @$input_vars, @$output_vars);
      my $count = 0;
      while ($all_vars =~ /$var/g) { $count++ }

      if($count != 1) {
        if(($$required{$key} & PARAM_JX_VARS_ALLOWD) != 0) {

          if(!(substr($var, 0, 1) eq "j")) {
            $$this{parse_error}++;
            print "[ERROR]: Invalid variable name " . $orig_var_name . " in section " . $key. "\n";
          }

          my $num = substr($var, 1, length($var));
          my $sys_fairness = $$this{formulas}->{SYS_FAIRNESS};
          my $max_jx = scalar @$sys_fairness;
          my $num_of_bits = ceil((log $max_jx)/(log 2));
          if($num_of_bits == 0) {
            $num_of_bits = 1;
          }

          if($num > $num_of_bits) {
            $$this{parse_error}++;
            print "[ERROR]: Maximum allowed number of jx is  " . $num_of_bits . " in section " . $key. "\n";
          }

        } else {
          $$this{parse_error}++;
          print "[ERROR]: Invalid variable name " . $orig_var_name . " in section " . $key. "\n";
        }
      }
    }
  }
}

#----------------------------------------------------------------------
# according to the configured options above this method will do all
# activated checks on the parse tree
# param the section key
# param the resulting parse tree
# param the formula (for error reporting)
sub doParseTreeChecks
{
  my $this = shift;
  my $key = shift;
  my $parse_tree = shift;
  my $formula = shift;

  my $required = $$this{required};

  my @existing_vars = (@{$$this{formulas}->{INPUT_VARIABLES}}, @{$$this{formulas}->{OUTPUT_VARIABLES}});
  my @allowed_vars = ();
  
  if (($$required{$key} & PARAM_INPUT_VARS_ALLOWED) != 0)
  {
    push(@allowed_vars, @{$$this{formulas}->{INPUT_VARIABLES}});
  }
  if (($$required{$key} & PARAM_OUTPUT_VARS_ALLOWED) != 0)
  {
    push(@allowed_vars, @{$$this{formulas}->{OUTPUT_VARIABLES}});
  }
  $this->check4Variables($parse_tree, $key, \@existing_vars, \@allowed_vars);

  if(($$required{$key} & PARAM_SUBNODES_ONLY_X) != 0)
  {
    if($this->check4SubNodesOnlyX($parse_tree) > 0)
    {
      $$this{parse_error}++;
      print "[ERROR]:". $formula . " of section " . $key. 
        " must not contain any temporal ops except X and G (or equivalent) as root-node\n";
    }
  } 
  
  if(($$required{$key} & PARAM_CHECK_ROOT_G) != 0)
  {
    if($this->check4RootNodeG($parse_tree) > 0)
    {
      $$this{parse_error}++;
      print "[ERROR]:". $formula . " of section " . $key. " is not valid because root node must be G or equivalent\n";
    }
  }


  if(($$required{$key} & PARAM_CHECK_ROOT_GF) != 0)
  {
    if($this->check4GF($parse_tree) > 0)
    {
      $$this{parse_error}++;
      print "[ERROR]:". $formula . " of section " . $key. " is not valid because root node must be G(F(...)) or equivalent\n";
    }
  }

  if(($$required{$key} & PARAM_NO_DOUBLE_X) != 0)
  {
    if($this->check4XX($parse_tree) > 0)
    {
      $$this{parse_error}++;
      print "[ERROR]: X(...X(...)...) in " . $formula . " of section " . $key. " is not valid \n";
    }
  }

  if(($$required{$key} & PARAM_ONLY_INPUT_IN_NEXT_STATE) != 0)
  {
    if($this->check4AllowedVarsAfterX($parse_tree, \@{$$this{formulas}->{INPUT_VARIABLES}}) > 0)
    {
      $$this{parse_error}++;
      print "[ERROR]: The element " . $formula . " in section " . $key. " is only allowed to talk about inputs in next states\n";
    }
  }

  if(($$required{$key} & PARAM_NO_TEMPORAL_OPERATORS) != 0)
  {
    if($this->check4NoTemporalOps($parse_tree) > 0)
    {
      $$this{parse_error}++;
      print "[ERROR]: Temporal operators are not allowed for formula " . $formula . " in section " . $key. "\n";
    }
  }

  if(($$required{$key} & PARAM_SUBSUBNODES_NO_TEMP_OP) != 0)
  {
    my $tmp_op_count = defined($parse_tree->Left) ? $this->check4NoTemporalOps($parse_tree->Left->Left) : 0 + 
      defined($parse_tree->Left) ? $this->check4NoTemporalOps($parse_tree->Left->Right)  : 0 + 
      defined($parse_tree->Right) ? $this->check4NoTemporalOps($parse_tree->Right->Left) : 0 +
      defined($parse_tree->Right) ? $this->check4NoTemporalOps($parse_tree->Right->Right): 0;
    if($tmp_op_count > 0)
    {
      $$this{parse_error}++;
      print "[ERROR]: Temporal operators are not allowed for formula " . $formula . " in section " . $key. "\n";
    }
  }
}

#----------------------------------------------------------------------
# returns the last result of the parsing process
sub getResult {
  my $this = shift;

  return $$this{parse_trees};
}

#----------------------------------------------------------------------
sub getVariableList {
  my $this = shift;
  my @vars = @{$$this{formulas}->{INPUT_VARIABLES}};
  push(@vars, @{$$this{formulas}->{OUTPUT_VARIABLES}});

  return \@vars;
}

#----------------------------------------------------------------------
sub getInputVariables {
  my $this = shift;
  my @vars = @{$$this{formulas}->{INPUT_VARIABLES}};

  return \@vars;
}

#----------------------------------------------------------------------
sub getOutputVariables {
  my $this = shift;
  my @vars = @{$$this{formulas}->{OUTPUT_VARIABLES}};

  return \@vars;
}

#----------------------------------------------------------------------
sub getOrdering {
  my $this = shift;

  my $vars = $$this{formulas}->{FORCE_ORDERING};

  my @var_array = ();
  if(defined $vars && defined @$vars[0]) {
    @var_array = split('\*',@$vars[0]);
  }

  return \@var_array;
}

#----------------------------------------------------------------------
sub needsConcatenation {
  my ($this, $key) = @_;
  
  my $required = $$this{required};
  return(($$required{$key} & PARAM_NEEDS_CONCATENATION));
}
