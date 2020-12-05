#$Id: BDDOptimizer.pm,v 1.11 2007/04/13 09:22:15 rbloem Exp $
package BDDOptimizer;

use Cudd;
use LTL;
use POSIX; # qw(ceil floor);
use BDDWrapper;

return 1;

#----------------------------------------------------------------------
# constructor
sub new
{
    my ($class, $bdd_module) = @_;

    if(!defined $bdd_module) {
	print "ERROR: BDDOptimizer::BDDOptimizer(): bdd_module missing\n";
	exit -1;
    }

    my $objref = {
	bdd_module => $bdd_module
    };
    
    bless $objref,$class;
    return $objref;
}



#----------------------------------------------------------------------
# implements a BDD optimization
sub simulationBased
{
    my ($this, $bdd) = @_;

    if(!defined $bdd) {
	print "ERROR: BDDOptimizer::simulationBased: BDD missing\n";
	exit -1;
    }
    my $bdd_module = $$this{bdd_module};

    #1. get bdd_one and bdd_zero
    my $bddOne = BDDWrapper->new($bdd_module);
    my $bddZero = BDDWrapper->new($bdd_module);
    my $bddOneNode = $$bdd_module{bdd_one};
    my $bddZeroNode = !$bddOneNode;
    my $nameOne = $bddOneNode->NodeName();
    my $nameZero = $bddZeroNode->NodeName();
    $bddOne->setBDDNode($bddOneNode);
    $bddZero->setBDDNode($bddZeroNode);
    $bddOne->setNewBDDNode($bddOneNode);
    $bddZero->setNewBDDNode($bddZeroNode);
    
    my @nodesFinished = ();   #array of BDDWrapper
    my @nodesBuilding = ();    #pointer to array of BDDWrapper
    my %relationFinished = (); #matrix of int, string as indexer
    my %relationBuilding = (); #matrix of int, string as indexer
    my %nodesFinishedHash = (); #hash name<string> to BDDWrapper
    my %nodesBuildingHash = ();

    #setup initial value for special nodes (zero/one bdd) 
    # const(1) > const(0)
    push(@nodesFinished, $bddOne);
    push(@nodesFinished, $bddZero);
    $relationFinished{$nameOne}{$nameOne} = 1;     # 1<=1
    $relationFinished{$nameOne}{$nameZero} = 0;    # 1>0
    $relationFinished{$nameZero}{$nameOne} = 1;    # 0<=1
    $relationFinished{$nameZero}{$nameZero} = 1;   # 0<=0
    $nodesFinishedHash{$nameOne} = $bddOne;
    $nodesFinishedHash{$nameZero} = $bddZero;

    print "One: $nameOne Zero: $nameZero\n";
    
    my @layerIndices = $bdd_module->getOrdering();
    my $nextLayer = $layerIndices[1];
    my $currentLayer = $layerIndices[0];
    my $result = 0;
    for($nextLayerIndex = (@layerIndices - 2); 
	$nextLayerIndex >= 0; 
	$nextLayerIndex--) 
    {
	$currentLayer = $layerIndices[$nextLayerIndex + 1];
	$nextLayer = $layerIndices[$nextLayerIndex];


	@nodesBuilding = $this->generateNextNodesArray(\@nodesFinished, $nextLayer, $currentLayer);
	%nodesBuildingHash = ();
	foreach my $item (@nodesBuilding)
	{
	    my $key = $item->getIdentifier();
	    $nodesBuildingHash{$key} = $item;
	}

	%relationBuilding = $this->generateNextNodesRelation(\@nodesBuilding,\%relationFinished,$nextLayer);

	$result = $this->buildNewBDD(\@nodesBuilding, \%nodesFinishedHash, \%relationFinished);
	
	@nodesFinished = @nodesBuilding;
	%relationFinished = %relationBuilding;
	%nodesFinishedHash = %nodesBuildingHash;
	@nodesBuilding = ();
	%relationBuilding = ();
	%nodesBuildingHash = ();
	
    }
    return $result;
}

#----------------------------------------------------------------------
#param nodesFinished point to array of BDDWrapper
#param nextIndex int
sub generateNextNodesArray {
    my ($this, $nodesFinished, $nextLayer, $currentLayer) = @_;

    if(!defined $nodesFinished) {
	print "ERROR: BDDOptimizer::generateNextNodesArray: nodesFinished missing\n";
	exit -1;
    }
    if(!defined $nextLayer) {
	print "ERROR: BDDOptimizer::generateNextNodesArray: nextLayer missing\n";
	exit -1;
    }
    if(!defined $currentLayer) {
	print "ERROR: BDDOptimizer::generateNextNodesArray: currentLayer missing\n";
	exit -1;
    }

    my @nodesBuilding = ();
    my %nodesBuildingHash = ();

    
    my $node = 0;
    foreach my $nodeWrapper (@$nodesFinished)
    {
	my $parents = $nodeWrapper->getParentList();
	if(defined $parents)
	{
	    my $toAdd = 0;
	    my @parents2delete = ();
	    foreach my $parent (@$parents)
	    {
		#1. parent is in next level >> generate BDDWrapper for parent
		# remove this parent from the parentslist for the temp NodeWrapper
		my $parent_index = Cudd::NodeReadIndex($parent->{'node'});
		if($parent_index == $nextLayer)
		{
		    if(!defined $nodesBuildingHash{$parent->NodeName()})
		    {
			my $parentNodeWrapper = BDDWrapper->new($$this{bdd_module});
			$parentNodeWrapper->setBDDNode($parent);
			$parentNodeWrapper->enableNewBDDGeneration();
			push(@nodesBuilding, $parentNodeWrapper);
			$nodesBuildingHash{$parentNodeWrapper->getIdentifier()} = $parentNodeWrapper;
		    }
		    push(@parents2delete, $parent);
		}else {
		    if($parent_index == $currentLayer)
		    {
			# remove this parent from the parentslist for the temp NodeWrapper
			print "\n\nthis should not happen (". $parent->NodeName() .")\n\n\n";
			exit;
		    }
		    else
		    {
			#2. parent is not in next level >> generate dummy BDDWrapper 
			#   representing the current node on the next level and remove 
			#   parents which are already handled (next level, this level or below
			$toAdd = 1;
		    }
		}

	    }
	    if(@parents2delete != 0)
	    {
		foreach my $rmParent (@parents2delete)
		{
		    $nodeWrapper->removeParent($rmParent->NodeName());
		}
	    }
	    if($toAdd == 1)
	    {
		$nodeWrapper->setThenNode($nodeWrapper->getNode());
		$nodeWrapper->setElseNode($nodeWrapper->getNode());
		push(@nodesBuilding, $nodeWrapper);
		$nodesBuildingHash{$nodeWrapper->getIdentifier()} = $nodeWrapper;
	    }
	}
    }

    return @nodesBuilding; #, %nodesBuildingHash);
}

#----------------------------------------------------------------------
# %relationFinished{node_one_name}{node_two_name} == 1 iff node_one <= node_two
#param nodesBuilding point to array of BDDWrapper
#param relationFinished matrix of int
#
# 1. if 0 and 1 are the BDD constants, we have
#    1 > 0
# 2. if v(x) = v(y) is an input variable, 
#    then x <= y if x.0 <= y.0 and x.1 <= y.1.
# 3. if v(x) = v(y) is an output variable, 
#    then x <= y if (x.0 <= y.0 or x.0 <= y.1) and (x.1 <= y.0 or x.1 <= y.1).
# with *.0 == then and *.1 == else
sub generateNextNodesRelation {
    my ($this, $nodesBuilding, $relationFinished, $nextIndex) = @_;

    if(!defined $nodesBuilding) {
	print "ERROR: BDDOptimizer::generateNextNodesRelation: nodesBuilding missing\n";
	exit -1;
    }
    if(!defined $relationFinished) {
	print "ERROR: BDDOptimizer::generateNextNodesRelation: relationFinished missing\n";
	exit -1;
    }
    if(!defined $nextIndex) {
	print "ERROR: BDDOptimizer::generateNextNodesRelation: nextIndex missing\n";
	exit -1;
    }

    my %relationBuilding = ();
    my ($is_input, $is_next, $is_environment) = $$this{bdd_module}->getLayerClassification($nextIndex);

#    print "is input: " . $is_input . "\n";

    my $bdd_module = $$this{bdd_module};
    foreach my $item1 (@$nodesBuilding)
    {
	my $item1Name = $item1->getIdentifier();
	my $item1ThenNode = $item1->getThenNode();
	my $item1ElseNode = $item1->getElseNode();
	my $item1Then = $item1ThenNode->NodeName();
	my $item1Else = $item1ElseNode->NodeName();

        foreach my $item2 (@$nodesBuilding) 
	{
	    my $item2Name = $item2->getIdentifier();
	    my $item2Then = $item2->getThenNode()->NodeName();
	    my $item2Else = $item2->getElseNode()->NodeName();

	    my $relation = 0;

	    # v(x) = v(y): x <= y
	    if($item1Name == $item2Name) 
	    {
		$relation = 1;
	    }

	    my $item1ThenHash = $relationFinished->{$item1Then};
	    my $item1ElseHash = $relationFinished->{$item1Else};
#	    print "$item1Then $item1Else $item2Then $item2Else\n";

	    if($is_input)
	    {
		if(($item1ThenHash->{$item2Then} == 1) &&
		   ($item1ElseHash->{$item2Else} == 1))
		{
		    $relation = 1;
		}
	    } else {
		if((($item1ThenHash->{$item2Then} == 1) || 
		    ($item1ThenHash->{$item2Else} == 1)) && 
		   (($item1ElseHash->{$item2Then} == 1) || 
		    ($item1ElseHash->{$item2Else} == 1))) 
		{
		    $relation = 1;
		}
	    }
#	    print "relation: $relation\n";
	    $relationBuilding{$item1Name}{$item2Name} = $relation;
	}
    }
    return %relationBuilding;
}

#----------------------------------------------------------------------
#param nodesBuilding point to array of BDDNodeWrapper
#param nodesFinished point to array of BDDNodeWrapper
#param relationBuilding matrix of int
#
# compute_b(x){
#   if x.var is an input node or x.then and x.else are incomparable in our order then
#     return ite(x.var, b(x.then), b(x.else))
#   else
#     if(x.then >= x.else)
#       return ite(x.var, b(x.then), constant_zero);
#     elsif(x.then <= x.else)
#       return ite(x.var, constant_zero, b(x.else));
#     // but perhaps if x.then <= x.else and x.else <= x.then, we should
# choose the one with the smaller bdd
# }

sub buildNewBDD {
    my ($this, $nodesBuilding, $nodesFinishedHash, $relationBuilding) = @_;

    if(!defined $nodesBuilding) {
	print "ERROR: BDDOptimizer::buildNewBDD: nodesBuilding missing\n";
	exit -1;
    }
    if(!defined $nodesFinishedHash) {
	print "ERROR: BDDOptimizer::buildNewBDD: nodesFinishedHash missing\n";
	exit -1;
    }
    if(!defined $relationBuilding) {
	print "ERROR: BDDOptimizer::buildNewBDD: relationBuilding missing\n";
	exit -1;
    }


    my $bdd_module = $$this{bdd_module};
    my $manager = $bdd_module->getBDDManager();
    my $one = $manager->BddOne;
    my $zero = !$one;
    my $zero1Name = $manager->BddZero->NodeName();
#    print "zero: " . $zero . "(" . $zero->NodeName() . ")[" . $zero->Size() . "]\n";
#    print "zero1: " . $zero1 . "(" . $zero1->NodeName() . ")[" . $zero1->Size() . "]\n";
    my $return_value = 0;
    foreach my $node (@$nodesBuilding)
    {
 	if($node->isNewBDDGenerationEnabled() == 1)
	{	
	    my $bddNode = $node->getNode();
	    my $thenNode = $bddNode->T();
	    my $elseNode = $bddNode->E();
	    my $thenNodeName = $thenNode->NodeName();
	    my $elseNodeName = $elseNode->NodeName();

	    my $thenNewNodeWrapper = $nodesFinishedHash->{$thenNodeName};
	    my $elseNewNodeWrapper = $nodesFinishedHash->{$elseNodeName};
	    my $thenNewNode = $thenNewNodeWrapper->getNewBDDNode();
	    my $elseNewNode = $elseNewNodeWrapper->getNewBDDNode();


	    
	    my $index = Cudd::NodeReadIndex($bddNode->{'node'});
	    my $singleRootNode = $bddNode->BddIthVar($index);
	    my ($is_input, $is_next, $is_environment) = 
		$bdd_module->getLayerClassification($index);

	    if($is_input == 0) 
	    {
		my $thenNodeNameHash = $relationBuilding->{$thenNodeName};
		my $elseNodeNameHash = $relationBuilding->{$elseNodeName};
		if(($thenNodeNameHash->{$elseNodeName} == 1) &&
		   ($elseNodeNameHash->{$thenNodeName} == 1))
		{
		    if($thenNewNode->Size() < $elseNewNode->Size())
		    {
			$elseNewNode = $zero;
		    }
		    else
		    {
			$thenNewNod = $zero;
		    }
		} else {
		    if($thenNodeNameHash->{$elseNodeName} == 1) 
		    {
			$thenNewNode = $zero;
		    } else {
			if($elseNodeNameHash->{$thenNodeName} == 1) 
			{
			    $elseNewNode = $zero;
			}
		    }
		}
	    }

	    if(($thenNewNode->NodeName() == $zero1Name) ||
	       ($elseNewNode->NodeName() == $zero1Name)) 
	    {
		print "looks like you called this function with a ADD! only BDD is supported!\n";
		exit();
	    }
#	    print "then size: " . $thenNewNode->Size() . "(" . $thenNode->Size() . ")\n";
#	    print "else size: " . $elseNewNode->Size() . "(" . $elseNode->Size() . ")\n";
	    
	    my $newNode = $singleRootNode->BddIte($thenNewNode, $elseNewNode);
#	    print "new size: " . $newNode->Size() . "(" . $node->getNode()->Size() .  ")\n";

	    $node->setNewBDDNode($newNode);
	}
	$return_value = $node->getNewBDDNode();
    }    
#    print "\n";
    return $return_value;
}




# #----------------------------------------------------------------------
# # implements a BDD optimization
# sub simulationBasedOld
# {
#     my $this = shift;
#     my $bdd = shift;

#     my $bdd_module = $$this{bdd_module};
#     my $removed_states = 0;
#     my $output_layers = 0;
    
#     my @current_nodes = ();
#     my @next_nodes = ();
#     my %next_nodes_hash = ();
#     my %current_nodes_hash = ();
#     my $current_nodes_relation = 0;
#     my $next_nodes_relation = 0;

#     #1. get bdd_one and bdd_zero
#     my $tmp_bdd_one = BDDNodeWrapper->new($bdd_module);
#     my $tmp_bdd_zero = BDDNodeWrapper->new($bdd_module);
#     $tmp_bdd_one->setBDDNode($$bdd_module{bdd_one});
#     $tmp_bdd_zero->setBDDNode($$bdd_module{bdd_zero});

#     #setup initial values for current_nodes and current_nodes_relation
#     # this values are for the OneBDD and ZeroBDD (layer)
#     push(@current_nodes, $tmp_bdd_one);
#     push(@current_nodes, $tmp_bdd_zero);

#     $name_bdd_one = $current_nodes[0]->getNodeName();
#     $name_bdd_zero = $current_nodes[1]->getNodeName();
#     $current_nodes_relation{$name_bdd_one}{$name_bdd_one} = 0;
#     $current_nodes_relation{$name_bdd_one}{$name_bdd_zero} = 0;
#     $current_nodes_relation{$name_bdd_zero}{$name_bdd_one} = 1;
#     $current_nodes_relation{$name_bdd_zero}{$name_bdd_zero} = 0;

#     $current_nodes_hash{$name_bdd_one} = $tmp_bdd_one;
#     $current_nodes_hash{$name_bdd_zero} = $tmp_bdd_zero;

#     # get layer_indicies to be able to handle reordering of the BDD
#     # with this optimization algorithm too
#     my @layer_indices = $bdd_module->getOrdering();
#     my $next_index = $layer_indices[1];
#     for($current_layer_index = (scalar @layer_indices - 2); 
# 	$current_layer_index >= 0; 
# 	$current_layer_index--) 
#     {
# 	print "starting with layer " . $current_layer_index ."\n";
# 	$next_index = $layer_indices[$current_layer_index];
# 	print "next index=" . $next_index . "\n";
	
# 	#2. get parents of current nodes, located in the next layer
# 	#   store them in BDDNodeWrapper in a hash table $next_nodes
# 	#input: current_nodes, $next_index, current_nodes_relation
# 	#output: next_nodes
# 	my $node = 0;
# 	my $var_index = 0;
# 	for(my $i = 0; $i < (scalar @current_nodes); $i++) {
# 	    print "i=" . $i ." of (" . (scalar @current_nodes) . ")\n";
# 	    $node = $current_nodes[$i];
# 	    my $my_parents = $node->getParentList();
# #	    print "number of parents = " . @$my_parents . "\n";
# 	    if(defined $my_parents) {
# 		print "parents defined!\n";
# 		my $tmp_parent = BDDNodeWrapper->new($bdd_module);
# 		$tmp_parent->setBDDNode($node->);

# 		my $node_name = $node->getNodeName();
# 		$tmp_parent->setName($node_name);
# 		$tmp_parent->setThenChildName($node->getNodeName()); 
# 		$tmp_parent->setElseChildName($node->getNodeName()); 
# 		my $tmp_add_object = 0;
# 		for(my $j = 0; $j < (scalar @$my_parents); $j++) {
# 		    my $parent = @$my_parents[$j];
# 		    my $parent_name = $bdd_module->getNodeName($parent);
#                     print "parent name = " . $parent_name . "\n";  
# 		    $parent_index = Cudd::NodeReadIndex($parent->{'node'});
# 		    if($parent_index == $next_index) {
# 			my $new_parent = BDDNodeWrapper->new($bdd_module);;
# 			$new_parent->setBDDNode($parent);
# 			my $exists = 0;
# 			#check if parent already in @next_nodes array
# 			for(my $k=0; $k < (scalar @next_nodes); $k++) {
# 			    if($parent_name == $next_nodes[$k]->getNodeName()) {
# 				$new_parent = $next_nodes[$k];
# 				$exists = 1;
# 				#and exit for loop
# 				$k = (scalar @next_nodes);
# 			    }
# 			}
# 			#only add new parent if it does not alreay exist
# 			if($exists == 0) {
# 			    print "write nextnodeshash " . $parent_name . "\n";
# 			    push(@next_nodes, $new_parent);
# 			    $next_nodes_hash{$parent_name} = $new_parent;
# 			}
# 		    } else {
# 			#if parent index != next index 
# 			#check if parent is in higher level or not
# 			for($tmpindex = 0; 
# 			    $tmpindex < $current_layer_index; 
# 			    $tmpindex++) 
# 			{
# 			    if($layer_indices[$tmpindex] == $parent_index)
# 			    {
# 				$tmp_add_object = 1;
# 				$tmp_parent->addParent($parent);
# 				$tmpindex = $current_layer_index;
# 			    }
# 			}
# 		    }
		    
# 		}
# 		if($tmp_add_object == 1) {
# 		    print "write nextnodeshash(tmp) " . $node_name . "\n";
# 		    push(@next_nodes, $tmp_parent);
# 		    $next_nodes_hash{$node_name} = $tmp_parent;
# 		}
# 	    } else {
# 		print "no parents found!\n";
# 	    }
# 	}
# 	#output: next_nodes

	
# 	#calculate "node relation" for next layer
# 	#input: current_nodes, next_nodes, current_nodes_relation
# 	#ouput: $next_nodes_relation
# 	my ($is_input, $is_next, $is_environment) = 
# 	    $bdd_module->getLayerClassification($next_index);
# 	print "size of next_nodes = " . @next_nodex . "\n";

# 	for(my $i = 0; $i < (scalar @next_nodes); $i++) {
# 	    $i_name = $next_nodes[$i]->getNodeName();
# 	    print $i_name .": ";
# 	    for(my $j = 0; $j < (scalar @next_nodes); $j++) {
# 		my $relation = 0;
		
# 		my $i_then = $next_nodes[$i]->getThenChildName();
# 		my $j_then = $next_nodes[$j]->getThenChildName();
# 		my $i_else = $next_nodes[$i]->getElseChildName();
# 		my $j_else = $next_nodes[$j]->getElseChildName();

# 		if($is_input) 
# 		{
# 		    if($current_nodes_relation{$i_then}{$j_then} &&
# 		       $current_nodes_relation{$i_else}{$j_else}) 
# 		    {
# 			$relation = 1;
# 		    }
# 		} else {
# 		    if(($current_nodes_relation{$i_then}{$j_then} || 
# 			$current_nodes_relation{$i_then}{$j_else}) && 
# 		       ($current_nodes_relation{$i_else}{$j_else} || 
# 			$current_nodes_relation{$i_else}{$j_then})) 
# 		    {
# 			$relation = 1;
# 		    }
# 		}
# 		$next_nodes_relation{$i_name}{$next_nodes[$j]->getNodeName()} = $relation;
# 		print $relation . " ";
# 	    }
# 	    print "\n";
# 	}
# 	#ouput: $next_nodes_relation


# 	for(my $i = 0; $i < (scalar @next_nodes); $i++){
# 	    my $node = $next_nodes[$i]->getNode();
# 	    if(defined $node) 
# 	    {
# 		# node is a non temporary one: new node has to be constructed
# 		# depending if one of the childs can be removed or not
# 		my $then_child = $next_nodes[$i]->getThenChildName();
# 		my $else_child = $next_nodes[$i]->getElseChildName();
		
# 		my $new_state_generated = 0;
# 		my $then_node = $current_nodes_hash{$then_child}->getNewNode();
# 		my $else_node = $current_nodes_hash{$else_child}->getNewNode();
# 		printf "then: $then_node else: $else_node \n";
# 		if($current_nodes_relation{$then_child}{$else_child} == 1) {
# 		    $then_node = $$bdd_module{bdd_zero};
# 		    $removed_states++;
# 		    $new_state_generated++;
# 		}
# 		if(($current_nodes_relation{$else_child}{$then_child} == 1) && 
# 		   ($new_state_generated == 0)) {
# 		    $else_node = $$bdd_module{bdd_zero};
# 		    $removed_states++;
# 		    $new_state_generated++;
# 		}
# 		printf "then: $then_node else: $else_node \n";
# 		printf "node: $node\n";
# #		$next_nodes[$i]->setNewBddNode(Cudd::BddIte($node, $then_node, $else_node));
# 		$next_nodes[$i]->setNewBDDNode($node->BddIte($then_node, $else_node));
# 		print "new_state_generated=" . $new_state_generated . "\n";
# 	    } else {
# 		#nodes is only temporary: nothing has to be done
		
# 	    }
# 	}
# 	print "this was layer index = " . $next_index . "\n";


	
# 	$current_nodes_relation = $next_nodes_relation;
# 	$current_nodes = $next_nodes;
# 	$current_nodes_hash = $next_nodes_hash;
# 	$next_nodes_relation = {};

# 	print "============== next layer (" . $next_index . ")===================\n";
#     }
#     print "removed states=" . $removed_states . "(" . $output_layers . ")\n";
# }
    

# compute_b(x){
#   if x.var is an input node or x.then and x.else are incomparable in our
# order then
#     return ite(x.var, b(x.then), b(x.else))
#   else
#     if(x.then >= x.else)
#       return ite(x.var, b(x.then), constant_zero);
#     elsif(x.then <= x.else)
#       return ite(x.var, constant_zero, b(x.else));
#     // but perhaps if x.then <= x.else and x.else <= x.then, we should
# choose the one with the smaller bdd
# }
