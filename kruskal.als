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
	graph: set Edge,
	--QUESTION: does this make sense or should we do a cycle-detecting algorithm instead of actually modeling trees?
	trees: set Tree
	--tree_nodes: set Node
}

sig Tree {
	tree_edges: set Edge,
	tree_nodes: set Node
}

fact initialState {
	Edge in first.graph
	no first.tree
}

fact trace {
	all s1: State - last | let s2 = s1.next |
		one e: Event | e.pre = s1 and e.post = s2 
}

sig Event {
	pre: State,
	post: State,
	add: Edge
} {
	post.graph = pre.graph - add

	add not in pre.tree
	add in pre.graph
	post.tree = pre.tree + add

	-- add must be an edge adjacent to pre.tree and it has to be the cheapest one
	isCheapestEdge[pre, add]
}

fact finalState {
	Edge in last.tree
}





