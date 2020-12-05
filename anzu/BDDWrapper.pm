#$Id: BDDWrapper.pm,v 1.2 2007/04/13 09:22:15 rbloem Exp $

package BDDWrapper;

return 1;


#----------------------------------------------------------------------
# constructor
sub new
{
    my ($class, $bdd_module) = @_;

    if(!defined $bdd_module) {
	print "ERROR: BDDNodeWrapper::BDDNodeWrapper(): bdd_module missing\n";
	exit -1;
    }

    my $objref = {
	bdd_module => $bdd_module, #BDDModule
	identifier => 0,           #string
	node => 0,                 #BDDNode
	new_node => 0,             #BDDNode
	parents => 0,              #pointer to array of BDDNode's
	enable_generation => 0,    #bool: default 0; 1 new node will be generated
	then_node => 0,            #BDDNode
	else_node => 0,            #BDDNode
	then_node_set => 0,        #bool:
	else_node_set => 0         #bool: 
    };
    
    bless $objref,$class;
    return $objref;
}


#----------------------------------------------------------------------
# param identifier string
# sub setIdentifier
# {
#     my ($this, $identifier) = @_;

#     if(!defined $identifier) {
# 	print "ERROR: BDDNodeWrapper::setIdentifier: identifier missing\n";
# 	exit -1;
#     }

#     $$this{identifier} = $identifier;
# }

#----------------------------------------------------------------------
# param bddNode BDDNode
sub setBDDNode
{
    my ($this, $bddNode) = @_;

    if(!defined $bddNode) {
	print "ERROR: BDDNodeWrapper::setBDDNode: bddNode missing\n";
	exit -1;
    }
    my $bdd_module = $$this{bdd_module};
    $$this{identifier} = $bdd_module->getNodeName($bddNode);
    $$this{parents} = $bdd_module->getParentList($bddNode);
    $$this{node} = $bddNode;
}


#----------------------------------------------------------------------
sub getNode
{
    my $this = shift;
    return $$this{node};
}

#----------------------------------------------------------------------
# @return BDDNode
sub setThenNode
{
    my ($this, $node) = @_;
    if(!defined $node) {
	print "ERROR: BDDWrapper::setThenNode(): nodesBuilding missing\n";
	exit -1;
    }
    $$this{then_node} = $node;
    $$this{then_node_set} = 1;
}

#----------------------------------------------------------------------
# @return BDDNode
sub setElseNode
{
    my ($this, $node) = @_;
    if(!defined $node) {
	print "ERROR: BDDWrapper::setElseNode(): nodesBuilding missing\n";
	exit -1;
    }

    $$this{else_node} = $node;
    $$this{else_node_set} = 1;
}

#----------------------------------------------------------------------
# @return BDDNode
sub getThenNode
{
    my $this = shift;
    my $tmp = $$this{then_node};
    if($$this{then_node_set} == 0)
    {
	$tmp = $$this{bdd_module}->getThenChild($$this{node});
    }
    return $tmp;
}

#----------------------------------------------------------------------
# @return BDDNode
sub getElseNode
{
    my $this = shift;
    my $tmp = $$this{else_node};
    if($$this{else_node_set} == 0)
    {
	$tmp = $$this{bdd_module}->getElseChild($$this{node});
    }
    return $tmp;
}

#----------------------------------------------------------------------
sub getIdentifier
{
    my $this = shift;
    return $$this{identifier};
}

#----------------------------------------------------------------------
# sets the current node to be processed during the new BDD node generation
# process
sub enableNewBDDGeneration
{
    my $this = shift;
    $$this{enable_generation} = 1;
}

#----------------------------------------------------------------------
# @returns bool if the new BDD should be generated (=1) for this node or not (=0)
sub isNewBDDGenerationEnabled
{
    my $this = shift;
    return $$this{enable_generation};
}


#----------------------------------------------------------------------
# param bddNode BDDNodeo
sub setNewBDDNode
{
    my ($this, $bddNode) = @_;
    
    if(!defined $bddNode) {
	print "ERROR: BDDNodeWrapper::setNewBDDNode: bddNode missing\n";
	exit -1;
    }

    $$this{enable_generation} = 0;
    $$this{new_node} = $bddNode;
}

#----------------------------------------------------------------------
sub getNewBDDNode
{
    my $this = shift;
    return $$this{new_node};
}


#----------------------------------------------------------------------
# param bddNode BDDNodeo
# sub setParents
# {
#     my ($this, $parents) = @_;
    
#     if(!defined $parents) {
# 	print "ERROR: BDDNodeWrapper::setParents: parents missing\n";
# 	exit -1;
#     }

#     $$this{parents} = $parents;
# }

#----------------------------------------------------------------------
# param parentName string
sub removeParent
{
    my ($this, $parentName) = @_;
    
    if(!defined $parentName) {
	print "ERROR: BDDNodeWrapper::removeParent: parentName missing\n";
	exit -1;
    }

    $newParents = ();
#    print "removeParent (" . @{$$this{parents}}  ."): ";
    foreach my $parent (@{$$this{parents}}) 
    {
#	print $parent->NodeName() . ":";
	if($$this{bdd_module}->getNodeName($parent) != $parentName) 
	{
#	    print "(add) ";
	    push(@$newParents, $parent);
	}
	else
	{
#	    print "() ";
	}
    }
#    print "\n";
#    print "number parents=" . @{$newParents} . "\n";
    $$this{parents} = $newParents;
#    print "number parents=" . scalar @{$$this{parents}} . "\n";
}


#----------------------------------------------------------------------
sub getParentList
{
    my $this = shift;

#    print "BDDNodeWrapper::getParentList()\n";

    if(!defined $$this{parents})
    {
	print "getParentList() reset parents\n";
	$$this{parents} = $$this{bdd_module}->getParentList($$this{node});
    }
    return $$this{parents};
}

