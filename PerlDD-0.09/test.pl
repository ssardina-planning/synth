# Before `make install' is performed this script should be runnable with
# `make test'. After `make install' it should work as `perl test.pl'

######################### We start with some black magic to print on failure.

# Change 1..1 below to 1..last_test_to_print .
# (It may become useful if the test is moved to ./t subdirectory.)

BEGIN {print "1..45\n";}
END {print "not ok 1\n" unless $loaded;}
use Cudd;
$loaded = 1;
print "ok 1\n";

######################### End of black magic.

# Insert your test code below (better if it prints "ok 13"
# (correspondingly "not ok 13") depending on the success of chunk 13
# of the test code):

my $manager = new Cudd;
my $one = $manager->BddOne;
print "1"; $retval = $one->Print(0,2);
print $retval == 1 ? "ok" : "not ok", " 2\n";

my $a = $manager->BddVar;
my $b = $manager->BddVar;
my $c = $a->Nand($b);
print "c"; $retval = $c->Print(2,2);
print $retval == 1 ? "ok" : "not ok", " 3\n";

$c = $a->And($b);
print "c"; $retval = $c->Print(2,2);
print $retval == 1 ? "ok" : "not ok", " 4\n";

my $d = $c->Not;
print "d"; $retval = $d->Print(2,2);
print $retval == 1 ? "ok" : "not ok", " 5\n";

my $v = $manager->BddVar;
my $w = $manager->BddVar;
my $x = Nand $v $w;	# implicit object notation
print "x"; $retval = $x->Print(2,2);
print $retval == 1 ? "ok" : "not ok", " 6\n";

my $r = $manager->BddVar;
my $s = $manager->BddVar;
my $y = $r->Nand($s);
print "y"; $retval = $y->Print(2,2);
print $retval == 1 ? "ok" : "not ok", " 7\n";

my $z = $x->Nand($y);
print "z"; $retval = $z->Print(4,2);
print $retval == 1 ? "ok" : "not ok", " 8\n";

# Use overloading.

$z = !($x * $one);
print "z"; $retval = $z->Print(2,2);
print $retval == 1 ? "ok" : "not ok", " 9\n";

my $f = $r + $w;
my $g = $s ^ $v;
my $h = $f * $g ^ $c * !$x;
$h = !$h;
print "h"; $retval = $h->Print(6,2);
print $retval == 1 ? "ok" : "not ok", " 10\n";

$retval = $x == !$z;
print $retval == 1 ? "ok" : "not ok", " 11\n";

$x = Exists {$v * $w} $h;
print "x"; $retval = $x->Print(4,2);
print $retval == 1 ? "ok" : "not ok", " 12\n";

# Reachability analysis.

my $x1 = $manager->BddVar;
my $x2 = $manager->BddVar;
my $x3 = $manager->BddVar;
my $y1 = $manager->BddVar;
my $y2 = $manager->BddVar;
my $y3 = $manager->BddVar;
my $w1 = $manager->BddVar;
my $T = !$x1*!$x2*!$x3*!$y1*(!$w1*!$y2*$y3+$w1*$y2*!$y3) +
        !$x1*(!$x2*$x3+$x2*!$x3)*!$y1*$y2*$y3 +
        !$x1*$x2*$x3*(!$w1*!$y1*!$y2*!$y3+$w1*$y1*$y2*$y3) +
        $x1*$x2*$x3*$y1*!$y3*(!$w1*!$y2+$w1*$y2) +
        $x1*$x2*!$x3*!$y1*$y2*!$y3 + $x1*!$x2*$x3*$y1*$y2*$y3 +
        $x1*!$x2*!$x3*$y1*$y2*!$y3;
print "T"; $retval = $T->Print(7,2);
print $retval == 1 ? "ok" : "not ok", " 13\n";

my $zero	= Not $one;
my $cube	= $x1*$x2*$x3*$w1;
my $eq		= (Xnor $y1 $x1) * (Xnor $y2 $x2) * (Xnor $y3 $x3);
my $init	= !$x1*!$x2*!$x3;		# state 000
my $reached	= $init;
my @new		= ($init);
while ($new[$#new] != $zero) {
    my $toy = Exists $cube ($T * $new[$#new]);	# image computation
    my $to  = Exists {$y1*$y2*$y3} ($toy * $eq);# swap variables
    push(@new,$to * !$reached);			# find new states
    $reached += $new[$#new];			# update reached
}
print "reached"; $retval = $reached->Print(3,2);
print $retval == 1 ? "ok" : "not ok", " 14\n";

my $target	= $x1*$x2*!$x3;			# state 110
my $depth;
for ($depth = $[; $depth <= $#new; $depth++) {
    if ($target <= $new[$depth]) { last; }
}
if ($depth > $#new) {
    print "target state is unreachable!\n";
    $retval = 0;
} else {
    print "target state reached after $depth (of $#new) iterations.\n";
    $retval = 1;
}
print $retval == 1 ? "ok" : "not ok", " 15\n";

# Compute justification sequences and state trajectories.
my @inputs = ();
my @states = ();
unshift(@states, $target);
my $states = $target;
for ($i = $depth - 1; $i >= 0; $i--) {
    my $img = Exists {$x1*$x2*$x3} ($states * $eq);# swap variables
    my $pre = Exists {$y1*$y2*$y3} ($T * $img);	# preimage computation
    $pre *= $new[$i];				# stay on shortest paths
    $pre = ShortestPath $pre;			# extract a cube
    my $inputs = Exists {$x1*$x2*$x3} $pre;	# extract input factor
    unshift(@inputs, $inputs);
    $states = Exists $w1 $pre;			# extract state factor
    unshift(@states, $states);
}

# Print out state trajectories.
$retval = 1;
for ($i = 0; $i <= $depth; $i++) {
    $states = $states[$i];
    print "\@states[$i]"; $retval *= $states->Print(3,2);
}
print $retval == 1 ? "ok" : "not ok", " 16\n";

# Print out justification sequences.
$retval = 1;
for ($i = 0; $i < $depth; $i++) {
    my $inputs = $inputs[$i];
    print "\@inputs[$i]"; $retval *= $inputs->Print(1,2);
}
print $retval == 1 ? "ok" : "not ok", " 17\n";

# Set up forward traversal.
$cube		= $x1*$x2*$x3*$w1;
$eq		= (Xnor $y1 $x1) * (Xnor $y2 $x2) * (Xnor $y3 $x3);
my $reset	= $x1*!$x2*!$x3;		# state 000
my $envelope	= $one;
my $oldenvelope;

# Do fixed point computation and print envelope states.
do {
    $oldenvelope = $envelope;
    my $toy = Exists $cube ($T * $envelope);		# image computation
    $envelope  = Exists {$y1*$y2*$y3} ($toy * $eq);	# swap variables
    $envelope += $reset;
} while ($envelope != $oldenvelope);

print "envelope"; $retval = $envelope->Print(3,2);
print $retval == 1 ? "ok" : "not ok", " 18\n";

my $z1	= $manager->BddVar;
my $z2	= $manager->BddVar;

# Specify the transition relation and print it.
$T = !$x1*!$x2*!$w*!$y1*$y2 + !$x1*!$x2*$w*$y1*!$y2 + !$x1*$x2*!$w*$y1*!$y2 +
     !$x1*$x2*$w*$y1*$y2 + $x1*!$x2*$y1*!$y2 + $x1*!$x2*!$w*!$y1*$y2 +
     $x1*$x2*!$y1*$y2;
print "T"; $retval = $T->Print(7,2);

$reset	= !$x1*!$x2;		# state 00

# Set up transitive closure.
my $cubex	= $x1*$x2;
my $cubey	= $y1*$y2;
my $cubez	= $z1*$z2;
my $eqxy	= (Xnor $y1 $x1) * (Xnor $y2 $x2);
my $eqxz	= (Xnor $z1 $x1) * (Xnor $z2 $x2);
my $eqyz	= (Xnor $y1 $z1) * (Xnor $y2 $z2);

# Abstract the primary input(s).
my $C = Exists $w $T;
my $oldC;

# Do fixed point computation and print transtive closure.
do {
    $oldC = $C;
    my $Cxz  = Exists $cubex ($C * $eqxz);
    my $Czy  = Exists $cubey ($C * $eqyz);
    $C   += Exists $cubez ($Cxz * $Czy);			# squaring
} while ($C != $oldC);

print "C(x,y)"; $retval = $C->Print(4,2);
print $retval == 1 ? "ok" : "not ok", " 19\n";

# Redo the fixed point computation using SwapVariables
my $altC = Exists $w $T;
do {
    $oldC = $altC;
    my $Cxz  = $altC->SwapVariables([$x1,$x2],[$z1,$z2]);
    my $Czy  = $Cxz->SwapVariables([$y1,$y2],[$z1,$z2]);
    $altC += Exists $cubez ($Cxz * $Czy);
} while ($altC != $oldC);
print $altC == $C ? "ok" : "not ok", " 20\n";

# Find reachable states from reset state(s).
$reached = Exists $cubex ($C * $reset);
$reached = $reset + Exists $cubey ($reached * $eqxy);
print "reached"; $retval = $reached->Print(2,2);
print $retval == 1 ? "ok" : "not ok", " 21\n";

# Test variable swapping
my $swapped = $envelope->SwapVariables([$x1,$x2,$x3],[$y1,$y2,$y3]);
print "swapped"; $retval = $swapped->Print(3,2);
print $retval == 1 ? "ok" : "not ok", " 22\n";

# Test solution of boolean equations.
my ($solref,$consist) = $T->SolveEqn([$y1,$y2]);
$retval = $consist == $zero;
if ($retval) {
    my $i = 0;
    foreach (@$solref) {
	my $sol = $_;
	print "G[$i]";
	$retval = $sol->Print(3,2);
	last if ($retval == 0);
	$i++;
    }
}
print $retval == 1 ? "ok" : "not ok", " 23\n";

# Test computation of signatures
my $sigref = $T->Signatures;
print "@$sigref\n";
print @$sigref == 16 ? "ok" : "not ok", " 24\n";

# Test computation of normalized signatures
$sigref = $T->NormSignatures;
print "@$sigref\n";
print @$sigref == 15 ? "ok" : "not ok", " 25\n";

# Test dot output
$retval = Cudd::BDD::Dot([$swapped],[],["swapped"]);
print $retval == 1 ? "ok" : "not ok", " 26\n";

# Test Essentials
my $essref = $T->Essentials;
print @$essref == () ? "ok" : "not ok", " 27\n";

my $E = $x1 * ($x2 + $y2) * !$y1;
$essref = $E->Essentials;

my $ess = $$essref[0];
$retval = $ess == $x1;
$ess = $$essref[1];
$retval = $ess == !$y1;
print $retval ? "ok" : "not ok", " 28\n";
# print @$essref == ($x1,!$y1) ? "ok" : "not ok", " 27bis\n";

# Test Size and Minterms
$retval = $E->Minterms(4) == 3.0;
$retval *= $E->Size == 6;
$retval *= Cudd::BDD::Size([$E,!$E]) == 6;
$retval *= Cudd::BDD::Size({E => $E}) == 6;
print $retval ? "ok" : "not ok", " 29\n";

# Test Compose
my $composed = $E->Compose($x2,$x3);
print "composed"; $retval = $composed->Print(4,2);
print $retval == 1 ? "ok" : "not ok", " 30\n";

# Test IsComplement
$retval = $E->IsComplement;
print $retval == 1 ? "ok" : "not ok", " 31\n";

# Test BooleanDiff
my $bdiff = $E->BooleanDiff($x1);
print "Boolean difference"; $retval = $bdiff->Print(3,2);
print $retval == 1 ? "ok" : "not ok", " 32\n";

# Test Correlation
$retval = $E->Correlation(!$E);
print $retval == 0.0 ? "ok" : "not ok", " 33\n";

# Test Decreasing and Increasing
$retval = $E->Decreasing($x1);
print $retval == 0 ? "ok" : "not ok", " 34\n";
$retval = $E->Decreasing($y1);
print $retval == 1 ? "ok" : "not ok", " 35\n";
$retval = $E->Increasing($x1);
print $retval == 1 ? "ok" : "not ok", " 36\n";
$retval = $E->Increasing($y1);
print $retval == 0 ? "ok" : "not ok", " 37\n";

# Test One and Zero
print $E == $E * $E->One + $E->Zero ? "ok" : "not ok", " 38\n";

# Test Support and LiteralSetIntersection
my $supportE = $E->Support;
my $supportC = $composed->Support;
my $common = $supportE->LiteralSetIntersection($supportC);
$retval = $common->Print(3,2);
print $retval == 1 ? "ok" : "not ok", " 39\n";

# Test Constrain Decomposition
my $decomp = $E->ConstrainDecomp;
my $verify = $E->One;
foreach (@$decomp) {
    my $sol = $_;
    $verify *= $sol;
}
print $verify == $E ? "ok" : "not ok", " 40\n";

#Test ReorderingStatus
my ($enabled,$method) = $manager->DynReorderingStatus;
print (($enabled == 0 && $method == Cudd::REORDER_SIFT) ? "ok" : "not ok");
print " 41\n";

#Test Intersect
my $intersection = $E->Intersect($bdiff);
$retval = $E * $bdiff >= $intersection;
print $retval == 1 ? "ok" : "not ok", " 42\n";

# Test PrioritySelect
my $Pi = Cudd::BDD::PiDxygtdxz([$x1,$x2],[$y1,$y2],[$z1,$z2]);
my $selection = $E->PrioritySelect($Pi,[$x1,$x2],[$y1,$y2],[$z1,$z2]);
$retval = $selection <= $E;
print $retval == 1 ? "ok" : "not ok", " 43\n";

# Test Shuffle
$retval = Cudd::BDD::Shuffle([$b,$a,$w,$v,$s,$r,$x1,$x2,$x3,$y1,$y2,$y3,$w1,$z1,$z2]);
print $retval == 1 ? "ok" : "not ok", " 44\n";

# Test CharToVect
my $ctv = $E->CharToVect;
$retval = 1;
foreach (@$ctv) {
    print "ctv"; $retval *= $_->Print(3,2);
}
print $retval == 1 ? "ok" : "not ok", " 45\n";

# print "made it to checkpoint 1\n";
