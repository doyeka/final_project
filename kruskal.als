open util/ordering[State]

/*
	
    create a graph F (a set of trees), where each vertex in the graph is a separate tree
    create a set S containing all the edges in the graph
    while S is nonempty and F is not yet spanning
        remove an edge with minimum weight from S
        if the removed edge connects two different trees then add it to the forest F, combining two trees into a single tree

*/

sig Node {}

sig Edge {
	node1: one Node,
	node2: one Node,
	weight: Int
}

sig State {
	remainingEdges: set Edge,
	forest: set Tree,
	--QUESTION: does this make sense or should 
	--we do a cycle-detecting algorithm instead of actually modeling trees?
}

sig Tree {
	tree_edges: set Edge,
	tree_nodes: set Node
}

sig Event {
	pre: State,
	post: State,
	add: Edge
} {
	-- Steps:
	-- Identify minimum weight edge in the graph.
	-- Remove the edge from remainingEdges.
	-- If the removed edge connectes two different trees, add the edge into the forest
-- 	   and combine the two trees into one.

}

-- preds

pred consistent[edges : set Edge, nodes: set Node] {
	all e: Edge | e in edges implies e.node1 in nodes and e.node2 in nodes
}

-- facts

-- TODO: Constraints on Nodes/Edges/Trees so they are consistent between sigs.
--		 Fill in event signature.

fact initialState {
	some first.forest
	all t: Tree | #(t.tree_nodes) = 1
	Edge in first.graph
	consistent[first.graph, Node]
}

fact trace {
	all s1: State - last | let s2 = s1.next |
		one e: Event | e.pre = s1 and e.post = s2 
}

fact finalState {
	#(last.forest) = 1
	one tree: Tree | (tree in last.forest) and (Node in tree.tree_nodes)
}





