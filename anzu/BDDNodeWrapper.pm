#$Id: BDDNodeWrapper.pm,v 1.6 2007/04/13 09:22:15 rbloem Exp $

package BDDNodeWrapper;

return 1;


#----------------------------------------------------------------------
# constructor
sub new
{
    my $class = shift;
    my $bdd_module = shift;

    if(!defined $bdd_module) {
	print "ERROR: BDDModule missing in constructor of BDDNodeWrapper\n";
	exit -1;
    }
    
    my $objref = {
	bdd_module => $bdd_module, #BDDModule
	node => 0, #BDD node
	name => 0, #string
	then_child_name => 0, #string
	else_child_name => 0, #string
	parents => [], #array of BDDNodeWrapper
	new_bddnode => 0, #BDD node, equal to node, optimization algorithm may change it
    };
    
    bless $objref,$class;
    return $objref;
}


#----------------------------------------------------------------------
# the bdd node is stored and all method calls to this wrapper class, will
# be simply forwarded to the stored bdd node
sub setBDDNode
{
    my $this = shift;
    my $node = shift;

    $$this{node} = $node;
#    $$this{new_bddnode} = $node;
    $$this{name} = $$this{bdd_module}->getNodeName($node);
    $$this{then_child_name} = $$this{bdd_module}->getNodeName($$this{bdd_module}->getThenChild($node));
    $$this{else_child_name} = $$this{bdd_module}->getNodeName($$this{bdd_module}->getElseChild($node));
}

#----------------------------------------------------------------------
sub setNewBDDNode
{
    my $this = shift;
    my $node = shift;

    $$this{new_bddnode} = $node;
}

#----------------------------------------------------------------------
# the name of this node can be set directly
sub setName
{
    my $this = shift;
    my $name = shift;

    $$this{name} = $name;
}

#----------------------------------------------------------------------
# 
sub setThenChildName
{
    my $this = shift;
    my $name = shift;

    $$this{then_child_name} = $name;
}

#----------------------------------------------------------------------
# 
sub setElseChildName
{
    my $this = shift;
    my $name = shift;

    $$this{else_child_name} = $name;
}

#----------------------------------------------------------------------
sub getNode
{
    my $this = shift;
    my $tmp = $$this{node};

    return $tmp;
}

#----------------------------------------------------------------------
sub getNewNode
{
    my $this = shift;
    my $tmp = $$this{new_bddnode};

    return $tmp
}

#----------------------------------------------------------------------
# returns the node name
sub getNodeName
{
    my $this = shift;
    
    return $$this{name};
}

#----------------------------------------------------------------------
# returns the else child of the bdd node, if this WrapperClass holds a
# reference to a real bdd node, otherwise it returns the stored reference
# to a bdd node
sub getElseChildName
{
    my $this = shift;
    return $$this{else_child_name};
}

#----------------------------------------------------------------------
sub getThenChildName
{
    my $this = shift;
    return $$this{then_child_name};
}

#----------------------------------------------------------------------
sub getParentList
{
    my $this = shift;

    if((defined $$this{node})) { # && ($$this{node} != 0)) {
	return $$this{bdd_module}->getParentList($$this{node});
    }

    return $$this{parents};
}

#----------------------------------------------------------------------
sub addParent
{
    my $this = shift;
    my $parent = shift;

    push(@{$$this{parents}}, $parent);
}

#----------------------------------------------------------------------
# sub setThenChild2ZeroBDD
# {
#     my $this = shift;
#     my $bdd_module = $$this{bdd_module};
#     my $manager = $${bdd_module}{manager};

#     if((defined $$this{node}) && ($$this{node}->{'node'} != 0)) {
# 	print "then node before replacement = " . ($$this{bdd_module}->getThenChild($$this{node}))->{'node'} . "\n";
# #	print "replacement node = ". $$this{bdd_module}{bdd_zero}->{'node'} . "\n";

# 	my $return_value = Cudd::SetThenChild($$this{node}->{'node'}, $$manager);
# 	print "set returns = " . $return_value ."\n";
# 	my $tmp = $$this{bdd_module}->getThenChild($$this{node})->{'node'};

# 	print "then node after replacement = " . $tmp . "\n";

# #	print $tmp . "\n";


#     } else {
# 	print "WARNING: node not available -> if node is temp node than nothing to do? \n";
#     }
# }


# #----------------------------------------------------------------------
# sub setElseChild2ZeroBDD
# {
#     my $this = shift;

#     if((defined $$this{node}) && ($$this{node}->{'node'} != 0)) {
# 	Cudd::SetElseChild($$this{node}->{'node'}, $$this{bdd_module}{bdd_zero}->{'node'});
#     } else {
# 	print "WARNING: node not available -> if node is temp node than nothing to do? \n";
#     }
# }
