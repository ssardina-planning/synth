#! /usr/bin/perl -w
#$Id: anzu.pl,v 1.22 2007/04/13 09:22:15 rbloem Exp $

no warnings "recursion";

use Cudd;
use Synthesizer;
use BDD2Verilog;
use BDD2Dummy;
use CodeGenerator;
use strict;
use BDDOptimizer;

sub printHelp {
  print "Welcome to Anzu, eagle that lives in the tree above lili\n";
  print "Usage: ./anzu -i config-file -o out-file [other options]\n";
  print "\n";
  print "Parameters: \n";
  print "    -h, --help             this message\n";
  print "    -i, --in    <file>     path to the configuration file\n";
  print "    -o, --out   <file>     where should I put the output? (default: akswt1.v)\n";
  print "    -m, --mode  <mode>     select the output type of the result file, where type is one of:\n";
  print "                             VLOG ... Standard Verilog according to [Kukula at Cav2002]\n";
  print "                             FUNC ... Verilog generated out of cubes\n";
  print "                             OFNC ... Slightly optimized Verilog generated out of cubes\n";
  print "                             MPLX ... Dump BDD-Trees as blif and reread blif and convert code to verilog (smallest result!)\n";
  print "    -b, --dbw              remove deterministic buechi word automatons from strategy\n";
  print "    -k, --kill             kill strategy and reorder bdd after that\n";
  print "    -d, --dyn              enable dynamic reordering\n";
  print "    -r1, --reorder1        reorder BDD after reading configuration\n";
  print "    -r2, --reorder2        reorder BDD after synthesizing\n";
  print "    -f, --fixed            use fixed ordering\n";
  print "    -s, --superfluousy     remove superfluousy input variables which are not needed to calculate output variables\n";
  print "    -e, --extract          extract dependent variables\n";
  print "    -u, --no_functions     Do not build functions for outputs in terms of inputs\n";
  print "    -p, --print <file>     print the strategy to the specified file (dot-format)\n";
  print "    -v, --verbose          be verbose and bdd ordering information\n";
}


#======================================================================
#                             MAIN

my $file_name;
my $out_file = "akswt1.v";
my $strategy_file;
my $enable_dyn = 0;
my $reorder1 = 0;
my $reorder2 = 0;
my $use_fixed = 0;
my $verbose = 0;
my $output_mode = CodeGenerator::OM_MULTIPLEXER_VERILOG;
my $kill_strat = 0;
my $dbw = 0;
my $extract_superfluousy = 0;
my $extract_dep_vars = 0;
my $optSimulation = 0;
my $generate_functions = 1;
my $date_version = 0;

# Parse command line and set options accordingly.
while (defined($ARGV[0]) && substr($ARGV[0], 0, 1) eq "-") 
{
  if (($ARGV[0] eq "-i") || ($ARGV[0] eq "--in")) 
  {
    shift;
    $file_name = shift;
  }
  elsif (($ARGV[0] eq "-o") || ($ARGV[0] eq "--out")) {
    shift;
    $out_file = shift;
  }
  elsif (($ARGV[0] eq "-p") || ($ARGV[0] eq "--print")) {
    shift;
    $strategy_file = shift;
  }
  elsif (($ARGV[0] eq "-d") || ($ARGV[0] eq "--dyn")) { 
    shift;
    $enable_dyn = 1;
  }
  elsif (($ARGV[0] eq "-r1") || ($ARGV[0] eq "--reorder1")) { 
    shift;
    $reorder1 = 1;
  }
  elsif (($ARGV[0] eq "-r2") || ($ARGV[0] eq "--reorder2")) { 
    shift;
    $reorder2 = 1;
  }
  elsif (($ARGV[0] eq "-f") || ($ARGV[0] eq "--fixed")) { 
    shift;
    $use_fixed = 1;
  }
  elsif (($ARGV[0] eq "-v") || ($ARGV[0] eq "--verbose")) { 
    shift;
    $verbose = 1;
  }
  elsif (($ARGV[0] eq "-k") || ($ARGV[0] eq "--kill")) { 
    shift;
    $kill_strat = 1;
  }
  elsif (($ARGV[0] eq "-b") || ($ARGV[0] eq "--dbw")) { 
    shift;
    $dbw = 1;
  }
  elsif (($ARGV[0] eq "-e") || ($ARGV[0] eq "--extract")) { 
    shift;
    $extract_dep_vars = 1;
  }
  elsif (($ARGV[0] eq "-u") || ($ARGV[0] eq "--no_functions")) { 
    shift;
    $generate_functions = 0;
  }
  elsif(($ARGV[0] eq "-a") || ($ARGV[0] eq "--a")) { 
    shift;
    $date_version = 1;
  }
  elsif (($ARGV[0] eq "-m") || ($ARGV[0] eq "--mode")) { 
    shift;
    if($ARGV[0] eq "VLOG") { $output_mode = CodeGenerator::OM_VERILOG; }
    elsif($ARGV[0] eq "FUNC") { $output_mode = CodeGenerator::OM_FUNCTIONAL_VERILOG; }
    elsif($ARGV[0] eq "OFNC") { $output_mode = CodeGenerator::OM_OPTIMIZED_FUNCTIONAL_VERILOG; }
    elsif($ARGV[0] eq "MPLX") { $output_mode = CodeGenerator::OM_MULTIPLEXER_VERILOG; }
    else { 
      print "Unsupported generation mode (-m). Use -h for more information\n"; 
      exit;
    } 
  }
  elsif (($ARGV[0] eq "-s") || ($ARGV[0] eq "--superfluousy")) { 
    shift;
    $extract_superfluousy = 1;
  }
  elsif (($ARGV[0] eq "-oS") || ($ARGV[0] eq "--simulationOptimization")) { 
    shift;
    $optSimulation = 1;
  } else {
    printHelp;
    exit;
  }
}

if(!defined($file_name))
{
  printHelp;
  exit;
}

print "----------------------------------------------------------------------\n";
print "                                ANZU                                  \n";

print "\n";
print " Synthesizing file " . $file_name . " to " . $out_file . "\n\n";

my $synthesizer = Synthesizer->new;
my $verilog_compiler = BDD2Verilog->new;
#my $verilog_compiler = BDD2Dummy->new;
my $bdd_module = $$synthesizer{bdd_module};

if($enable_dyn) {
  $$bdd_module{manager}->EnableDyn;
}

$verilog_compiler->initialize("main", 0);

print " Dynamic reordering \t\t\t\t";
if($enable_dyn) {
  $$bdd_module{manager}->EnableDyn();
  print "enabled\n";
} else {
  print "disabled\n";
}

print " Reorder BDD after reading configuration \t" . (($reorder1 == 1)?"enabled":"disabled") . "\n";
print " Reorder BDD after synthesizing \t\t" . (($reorder2 == 1)?"enabled":"disabled") . "\n";
print " Reorder after killing strategy \t\t" . (($kill_strat == 1)?"enabled":"disabled") . "\n";
print "\n";
print " Using fixed BDD ordering \t\t\t" . (($use_fixed == 1)?"enabled":"disabled") . "\n";
print " Extract superfluousy vars \t\t\t" . (($extract_superfluousy eq 1)?"enabled":"disabled") . "\n";
print " Function generation \t\t\t\t" . (($generate_functions eq 1)?"enabled":"disabled") . "\n";
print "\n";

##--- CONFIGURATION ---
my $starttime = (times)[0];
$synthesizer->readConfiguration($file_name, $use_fixed);
my $configtime = (times)[0];
print " Timing Information:\n";
printf "   Configuration read within \t\t%10.2f seconds\n", ($configtime - $starttime);
my $after_config = $bdd_module->printOrdering();

##--- REORDERING ---
if($reorder1 == 1) {
  $$bdd_module{manager}->Reorder(Cudd::REORDER_SIFT);
}
my $first_reorder_time = (times)[0];
printf "   First reordering of bdd takes \t%10.2f seconds\n", ($first_reorder_time - $configtime);
my $after_reorder1 = $bdd_module->printOrdering();

#--- SYNTHESIZE ---
my $strategy = $synthesizer->synthesize();
my $synthesize_time = (times)[0];
printf "   Synthesis takes \t\t\t%10.2f seconds\n", ($synthesize_time - $first_reorder_time);

#--- go on with code generation, other type of optimizaiton etc ---
if($strategy == $${bdd_module{bdd_zero}}) {
  print "\n";
  print "                   !SPECIFICATION IS NOT REALISABLE!\n\n";
} else {

  #--- MINIMIZE ---
  ($strategy, my $sub_functions, my $g, my $superfluousy) = 
    $synthesizer->minimize($strategy, $dbw, $extract_superfluousy, $extract_dep_vars, $generate_functions, $date_version);
  my $minimize_time = (times)[0];
  printf "   Minimization takes \t\t\t%10.2f seconds\n",
    ($minimize_time - $synthesize_time);
  
  my $after_synthesize = $bdd_module->printOrdering();

  my $strategy_size_before = $strategy->Size;

  if($reorder2 == 1) {
    $$bdd_module{manager}->Reorder(Cudd::REORDER_SIFT_CONVERGE);
  }

  my $strategy_size_after = $strategy->Size;
  my $reorder_time = (times)[0];

  my $after_reorder2 = $bdd_module->printOrdering();

  printf "   Reordering of bdd takes \t\t%10.2f seconds\n", ($reorder_time - $minimize_time);

  if($kill_strat == 1) {
    $strategy = undef;
    $$bdd_module{manager}->Reorder(Cudd::REORDER_SIFT_CONVERGE);
    my $killing_time = (times)[0];
    printf "   Killing strat and reordering takes \t%10.2f seconds\n", ($killing_time - $reorder_time);
    $reorder_time = $killing_time;
  }
  my $after_kill = $bdd_module->printOrdering();
  my $node_dep_time = $reorder_time;


  if($optSimulation == 1)
  {
      printf "Size before simulationBased optimization=" . $strategy->Size . "\n";
      $$synthesizer{bdd_module}->generateNodeDependencies($strategy);
      my $bdd_optimizer = BDDOptimizer->new($bdd_module);
      
#      select(STDOUT); $| = 1;
#      Cudd::BDD::Dot([$strategy]);
      
      $strategy = $bdd_optimizer->simulationBased($strategy);
      
#      select(STDOUT); $| = 1;
#      Cudd::BDD::Dot([$strategy]);
      
      printf "Size after simulationBased optimization=" . $strategy->Size . "\n";
  }

  if($output_mode == CodeGenerator::OM_VERILOG) {
      $strategy = $$synthesizer{bdd_module}->convertBddToAdd($strategy);
      $$synthesizer{bdd_module}->generateNodeDependencies($strategy);
      $node_dep_time = (times)[0];
      printf "   Node dependency generation takes \t%10.2f seconds\n", ($node_dep_time - $reorder_time);
  }


  my $code_generator = CodeGenerator->new($$synthesizer{bdd_module}, $verilog_compiler);
  $code_generator->selectOutputMode($output_mode);
  my $g_sharing_size = $code_generator->generate($strategy, $g, $sub_functions);

  $verilog_compiler->save($out_file);

  my $code_gen_time = (times)[0];


#my $stdout = STDOUT;

  printf "   Code generation takes \t\t%10.2f seconds\n", ($code_gen_time - $node_dep_time);
  printf "   Results in needed overall time of \t%10.2f seconds\n", ($code_gen_time - $starttime);
  print "\n";
  print " BDD-Size Information:\n";
  printf "   Size of generated strategy is \t%10d bdd-nodes\n", $strategy_size_before;
  printf "   Size of after reordering is \t\t%10d bdd-nodes\n", $strategy_size_after;
  printf "   Size of functional representation \t%10d bdd-nodes\n", $g_sharing_size;
  print "\n";
  if(($extract_superfluousy eq 1)) {
    print " Removed Superfluousy Variables:\n";
    if(scalar (keys %$superfluousy) eq 0) {
      print "   No Superfluousy Variables found!\n";
    } else {
      print "   ", join(", ", keys %$superfluousy), "\n";
    }
  }
  if(($extract_dep_vars eq 1)) {
    print " Extracted dependent variables:\n";
    if(scalar (keys %$sub_functions) eq 0) {
      print "   No dependent variables found!\n";
    } else {
      print "   ", join(", ", keys %$sub_functions), "\n";
    }
  }

  print "\n";
  if($verbose eq 1) {
    print " BDD-Ordering Information:\n";
    print "   Configured ordering:\n";
    print "     " . $synthesizer->getConfiguredOrdering() . "\n";
    print "   After reading configuration: \n";
    print "     " . $after_config . "\n";
    print "   After first reordering: \n";
    print "     " . $after_reorder1 . "\n";
    print "   After synthesizing: \n";
    print "     " . $after_synthesize . "\n";
    print "   After second reordering: \n";
    print "     " . $after_reorder2 . "\n";
    print "   After killing strategy: \n";
    print "     " . $after_kill . "\n";
    print "\n";
  }  

  $code_generator->printWarnings();
}


print "                    DONE - THANKS FOR YOUR PATIENCE                   \n";
print "----------------------------------------------------------------------\n";


#$code_generator->printStatistic();

if(defined $strategy_file) {
  open(STDOUT, "> " . $strategy_file);
  select(STDOUT); $| = 1;
  Cudd::BDD::Dot([$strategy]);
}
# close(STDOUT); # dont close this handle, otherwise the dot output for the strategy will not be complete!!!


