#$Id: BDD2Verilog.pm,v 1.6 2007/04/13 09:22:15 rbloem Exp $
package BDD2Verilog;


return 1;

use Cudd;
use BDDModule;
use strict;

use constant ZERO_WIRE_NAME    => "zero_value";
use constant ONE_WIRE_NAME     => "one_value";
use constant CLOCK_WIRE_NAME   => "clock";

#MAIN_VAR_HANDLER;
#MAIN_CODE_HANDLER;

#----------------------------------------------------------------------
# Constructor
sub new
{
  my $class = shift;

  my $object = {
    write2file => 0,
    main_header => "",
    main_parameters => "",
    main_var => "",
    main_var_handler => 0,
    main_code => "",
    main_code_handler => 0,
    main_footer =>"",
    module_code => "",
    assign_code => "",
    initial_code => "",
    always_code => "",
    wire_counter => "",
    input_node_counter => 0,
    output_node_counter => 0,
    multiplexer_counter => 0,
    flip_flop_counter => 0
    };

  bless $object, $class;
  return $object;
}

#----------------------------------------------------------------------
sub generateKukulaModuleCode {
  my $this = shift;

  $$this{module_code} .= 
    "module input_node(find_out, choose_out_0, choose_out_1, " 
    . "  choose_out_chain_0, choose_out_chain_1, find_in_0, find_in_1, choose_in, var_val);\n"
    . "  input find_in_0, find_in_1, choose_in, var_val, choose_out_chain_0, choose_out_chain_1;\n"
    . "  output find_out, choose_out_0, choose_out_1;\n"
    . "  wire find_in_0, find_in_1, choose_in, var_val, choose_out_chain_0, choose_out_chain_1;\n"
    . "  wire find_out, choose_out_0, choose_out_1;\n"
    . "  wire not_var_val, and_nvv_0, and_vv_1;\n"
    . "  wire and_nvv_ci, and_vv_ci;\n"
    . "\n"
    . "  assign not_var_val = ! var_val;\n"
    . "  assign and_nvv_0 = not_var_val & find_in_0;\n"
    . "  assign and_vv_1 = var_val & find_in_1;\n"
    . "  assign find_out = and_nvv_0 | and_vv_1;\n"
    . "//  not(not_var_val, var_val);\n"
    . "//  and(and_nvv_0, not_var_val, find_in_0);\n"
    . "//  and(and_vv_1, var_val, find_in_1);\n"
    . "//  or(find_out, and_nvv_0, and_vv_1);\n"
    . "\n"
    . "  assign and_nvv_ci = not_var_val & choose_in;\n"
    . "  assign and_vv_ci = var_val & choose_in;\n"
    . "  assign choose_out_0 = choose_out_chain_0 | and_nvv_ci;\n"
    . "  assign choose_out_1 = choose_out_chain_1 | and_vv_ci;\n"
    . "//  and(and_nvv_ci, not_var_val, choose_in);\n"
    . "//  and(and_vv_ci, var_val, choose_in);\n"
    . "//  or(choose_out_0, choose_out_chain_0, and_nvv_ci);\n"
    . "//  or(choose_out_1, choose_out_chain_1, and_vv_ci);\n"
    . "endmodule\n\n"
    . "\n"
    . "module output_node(find_out, drive, val_out, choose_out_0, choose_out_1, "
    . "  choose_out_chain_0, choose_out_chain_1, find_in_0, find_in_1, val_in, val_out_chain, drive_chain, choose_in);\n"
    . "  input choose_out_chain_0, choose_out_chain_1, find_in_0, find_in_1, val_in, val_out_chain, drive_chain, choose_in;\n"
    . "  output find_out, drive, val_out, choose_out_0, choose_out_1;\n"
    . "  wire choose_out_chain_0, choose_out_chain_1, find_in_0, find_in_1, val_in, val_out_chain, drive_chain, choose_in;\n"
    . "  wire find_out, drive, val_out, choose_out_0, choose_out_1;\n"
    . "  wire and_vi_fi1, not_find_in_0, or_nfi0_avf1, and_ornfi0avf1_ci, not_or_nfi0_avf1;\n"
    . "  wire and_ci_nonfi0avf1;\n"
    . "\n"
    . "  assign find_out = find_in_0 | find_in_1;\n"
    . "  assign drive =  drive_chain | choose_in;\n"
    . "  assign and_vi_fi1 =  val_in & find_in_1;\n"
    . "  assign not_find_in_0 = !  find_in_0;\n"
    . "  assign or_nfi0_avf1 =  not_find_in_0 | and_vi_fi1;\n"
    . "  assign and_ornfi0avf1_ci =  or_nfi0_avf1 &choose_in;\n"
    . "  assign val_out =  and_ornfi0avf1_ci |val_out_chain;\n"
    . "  assign choose_out_1 = choose_out_chain_1 | and_ornfi0avf1_ci;\n"
    . "  assign not_or_nfi0_avf1= ! or_nfi0_avf1;\n"
    . "  assign and_ci_nonfi0avf1 = not_or_nfi0_avf1 & choose_in;\n"
    . "  assign choose_out_0 = choose_out_chain_0 | and_ci_nonfi0avf1; \n"
    . "//  or(find_out, find_in_0, find_in_1);\n"
    . "//  or(drive, drive_chain, choose_in);\n"
    . "//  and(and_vi_fi1, val_in, find_in_1);\n"
    . "//  not(not_find_in_0, find_in_0);\n"
    . "//  or(or_nfi0_avf1, not_find_in_0, and_vi_fi1);\n"
    . "//  and(and_ornfi0avf1_ci, or_nfi0_avf1, choose_in);\n"
    . "//  or(val_out, and_ornfi0avf1_ci, val_out_chain);\n"
    . "//  or(choose_out_1, choose_out_chain_1, and_ornfi0avf1_ci);\n"
    . "//  not(not_or_nfi0_avf1, or_nfi0_avf1);\n"
    . "//  and(and_ci_nonfi0avf1, not_or_nfi0_avf1, choose_in);\n"
    . "//  or(choose_out_0, choose_out_chain_0, and_ci_nonfi0avf1);\n"
    . "endmodule\n\n"
    . "\n"
    . "module multiplexer(out, in_0, in_1, select);\n"
    . "  input in_0, in_1, select;\n"
    . "  output out;\n"
    . "//  wire not_select;\n"
    . "//  wire in_1_select, in_0_select;\n"
    . "  assign out = (in_0 & !select) | (in_1 & select);\n"
    . "//  not negate_select(not_select, select);\n"
    . "//  and select_1(in_1_select, select, in_1);\n"
    . "//  and select_0(in_0_select, not_select, in_0);\n"
    . "//  or  or_out(out, in_1_select, in_0_select);\n"
    . "endmodule\n\n";
}

#----------------------------------------------------------------------
# the initialize method generates the code for the two necessary
# modules in verilog syntax.
sub initialize
{
  my $this = shift;
  my $name = shift;
  my $write2file = shift;

  if(defined $write2file) {
    if($write2file == 1) {
      $$this{write2file} = 1;
    }
  }

  $$this{main_header} = "module " . $name;
  $$this{main_parameters} = CLOCK_WIRE_NAME;

  
  my $tmp = 
      "  input " . CLOCK_WIRE_NAME . ";\n"
    . "  wire " . ZERO_WIRE_NAME . " = 0;\n"
    . "  wire " . ONE_WIRE_NAME . " = 1;\n";
  if($$this{write2file} == 1) {
    my $filename = $name . "_main_var";
    open(MAIN_VAR_HANDLER, "> $filename");
    print MAIN_VAR_HANDLER $tmp;
  } else {
    $$this{main_var} .= $tmp;
  }

  $tmp = "";

  if($$this{write2file} == 1) {
    my $filename = $name . "_main_code";
    open(MAIN_CODE_HANDLER, "> $filename");
    print MAIN_CODE_HANDLER $tmp;
  } else {
    $$this{main_code} .= $tmp;
  }

  $$this{main_footer} = "endmodule\n\n";
  $$this{input_node_counter} = 0;
  $$this{output_node_counter} = 0;
  $$this{multiplexer_counter} = 0;
  $$this{flip_flop_counter} = 0;
}


#----------------------------------------------------------------------
# clean up everything: e.g. closes all open file handler
sub deinitialize {
  my $this = shift;

  if($$this{write2file} == 1) {
    close $$this{main_var_handler};
    close $$this{main_code_handler};
  }
}


#----------------------------------------------------------------------
# create a new wire with a given name
# param wire_name the name of the wire
#FIXXME: add optional parameter for setting initial value: see generateFlipFlopConnections()
sub generateNewWire {
  my ($this, $wire_name) = @_;

  my $tmp = "  wire " . $wire_name . ";\n";
  
  if($$this{write2file} == 1) {
    print MAIN_VAR_HANDLER $tmp;
  } else {
    $$this{main_var} .= $tmp;
  }
  return $wire_name;
}

#----------------------------------------------------------------------
# Assign a fixed value for the given wire
sub assignFixedValue {
    my ($this, $wire_name, $value) = @_;
    if(!defined $value) {
      $value = 0;
    }

    $$this{assign_code} .= "assign " . $wire_name . " = " . $value . ";\n";
}

#----------------------------------------------------------------------
# returns the zero wire
sub getZeroWire {
  my $this = shift;

  return ZERO_WIRE_NAME;
}

#----------------------------------------------------------------------
# returns the zero wire
sub getOneWire {
  my $this = shift;

  return ONE_WIRE_NAME;
}

#----------------------------------------------------------------------
sub generateInputParameter {
  my $this = shift;
  my $param_name = shift;

  if(!($$this{main_parameters} eq '')) {
    $$this{main_parameters} = $$this{main_parameters} . ", ";
  }
  $$this{main_parameters} = $$this{main_parameters} . $param_name;

  my $tmp = "  input " . $param_name . ";\n";
  if($$this{write2file} == 1) {
    print MAIN_VAR_HANDLER $tmp;
  } else {
    $$this{main_var} .= $tmp;
  }
}

#----------------------------------------------------------------------
sub generateOutputParameter {
  my $this = shift;
  my $param_name = shift;

  if(!($$this{main_parameters} eq '')) {
    $$this{main_parameters} = $$this{main_parameters} . ", ";
  }
  $$this{main_parameters} = $$this{main_parameters} . $param_name;

  my $tmp = "  output " . $param_name . ";\n";
  if($$this{write2file} == 1) {
    print MAIN_VAR_HANDLER $tmp;
  } else {
    $$this{main_var} .= $tmp;
  }
}


#----------------------------------------------------------------------
# instantiate an input_node and sets the correct connections for it
# the result is an array of the newly generated output connections
sub generateInputNodeConnections {
  my ($this, $find_out, $choose_out_0 , $choose_out_1, 
      $choose_out_chain_0 , $choose_out_chain_1 , $find_in_0, 
      $find_in_1 , $choose_in , $var_val) = @_;

  $$this{input_node_counter} = $$this{input_node_counter} + 1;
  my $current_input_node_name = "input_node" . $$this{input_node_counter};

  my $code = "  input_node " . $current_input_node_name . "(";
  $code .= $find_out . ", ";
  $code .= $choose_out_0 . ", ";
  $code .= $choose_out_1 . ", ";
  $code .= $choose_out_chain_0 . ", ";
  $code .= $choose_out_chain_1 . ", ";
  $code .= $find_in_0 . ", ";
  $code .= $find_in_1 . ", ";
  $code .= $choose_in . ", ";
  $code .= $var_val . ");\n";

  if($$this{write2file} == 1) {
    print MAIN_CODE_HANDLER $code;
  } else {
    $$this{main_code} .= $code;
  }
}


#----------------------------------------------------------------------
# instantiate a multiplexer and connect it to the specified wires
sub generateFlipFlopConnections {
  my $this = shift;
  my $out = shift;
  my $data = shift;
  my $init_var = shift || 0;

  if($$this{write2file} == 1) {
    print MAIN_CODE_HANDLER ""; #FIXXXME: what todo here, does not work on writing directly
  } else {
    $$this{main_var} .= "  reg $out;\n";
    $$this{initial_code} .= "  $out = $init_var;\n";
    $$this{always_code}  .= "  $out = $data;\n";
  }

}


#----------------------------------------------------------------------
# instantiate a multiplexer and connect it to the specified wires
sub generateMultiplexerConnections {
  my $this = shift;
  my $out = shift;
  my $in0 = shift;
  my $in1 = shift;
  my $select = shift;

  $$this{multiplexer_counter} = $$this{multiplexer_counter} + 1;
  my $current_multiplexer_name = "multiplexer" . $$this{multiplexer_counter};
  
  my $code =  "  multiplexer " . $current_multiplexer_name . "(";
  $code .=  $out . ", ";
  $code .=  $in0 . ", ";
  $code .=  $in1 . ", ";
  $code .=  $select . ");\n";

  if($$this{write2file} == 1) {
    print MAIN_CODE_HANDLER $code;
  } else {
    $$this{main_code} .= $code;
  }
}

#----------------------------------------------------------------------
# instantiate an output_node and sets the correct connections for it
# the result is an array of the newly generated output connections
sub generateOutputNodeConnections {
  my ($this, $find_out, $drive, $val_out, $choose_out_0, 
      $choose_out_1, $choose_out_chain_0, $choose_out_chain_1, 
      $find_in_0, $find_in_1, $val_in, $val_out_chain, 
      $drive_chain, $choose_in) = @_;

  $$this{output_node_counter} = $$this{output_node_counter} + 1;
  my $current_output_node_name = "output_node" . $$this{output_node_counter};

  my $code = "  output_node " . $current_output_node_name . "(";
  $code .= $find_out . ", ";
  $code .= $drive . ", ";
  $code .= $val_out . ", ";
  $code .= $choose_out_0 . ", ";
  $code .= $choose_out_1 . ", ";
  $code .= $choose_out_chain_0 . ", ";
  $code .= $choose_out_chain_1 . ", ";
  $code .= $find_in_0 . ", ";
  $code .= $find_in_1 . ", ";
  $code .= $val_in . ", ";
  $code .= $val_out_chain . ", ";
  $code .= $drive_chain . ", ";
  $code .= $choose_in . ");\n";

  if($$this{write2file} == 1) {
    print MAIN_CODE_HANDLER $code;
  } else {
    $$this{main_code} .= $code;
  }
}


#----------------------------------------------------------------------
# prints the generated code to std out
sub print {
  my $this = shift;

#FIXXXME: Duplicate code
  print $$this{main_header};
  print $$this{main_var}."\n";
  print $$this{assign_code};
  print $$this{main_code};  
  print $$this{main_footer};
  print $$this{module_code};

}

#----------------------------------------------------------------------
# write the virolog code to the given filename
sub save {
  my $this = shift;
  my $filename = shift;

  open(FILEHANDLE, "> $filename");

  print FILEHANDLE $$this{main_header};
  print FILEHANDLE "(" . $$this{main_parameters} . ");\n" ;
  print FILEHANDLE $$this{main_var}."\n";
  print FILEHANDLE $$this{assign_code};
  print FILEHANDLE "    initial begin\n";
  print FILEHANDLE $$this{initial_code};
  print FILEHANDLE "    end\n";
  print FILEHANDLE "    always @(posedge " . CLOCK_WIRE_NAME . ") begin\n";
  print FILEHANDLE $$this{always_code};
  print FILEHANDLE "    end\n";
  print FILEHANDLE $$this{main_code};
  print FILEHANDLE $$this{main_footer};
  print FILEHANDLE $$this{module_code};
  
  close FILEHANDLE;
}

