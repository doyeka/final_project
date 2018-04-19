open util/ordering[State]

/*
	
    create a graph F (a set of trees), where each vertex in the graph is a separate tree
    create a set S containing all the edges in the graph
    while S is nonempty and F is not yet spanning
        remove an edge with minimum weight from S
        if the removed edge connects two different trees then add it to the forest F, combining two trees into a single tree

*/

sig Node {
	--edges: Int -> Node
	--edges: Node -> Int
}

sig State {
	graph: Node -> Int -> Node,
	tree: Node -> Int -> Node
}

sig Event {
	pre: State,
	post: State,
	add: Node -> Int -> Node
} {
	-- Steps:
	-- Identify minimum weight edge in the graph.
	-- Remove the edge from remainingEdges.
	-- If the removed edge connectes two different trees, add the edge into the forest
	-- and combine the two trees into one.
	add in pre.graph
	#(add) = 1
	smallestEdge[add, pre.graph]
	--post.graph = pre.graph - add - (add.Node.Node)->(~(Int.add))
	--post.tree = pre.tree + add + (add.Node.Node)->(~(Int.add)) 

}

pred smallestEdge[add: Node -> Int -> Node, g: Node -> Int -> Node] {
	all i: g.Node[Node] - add.Node[Node] | i > add.Node[Node]
}

fact positiveEdges {
	all i : State.graph.Node[Node] | i > 0
}


fact edgeProperties {
	all u,v: Node | all s: State | all i: Int | {
		s->u->i->v in graph implies s->v->i->u in graph and {		--bidirectional
			no j: Int - i | s->v->j->u in graph
		}
		
	}
}

-- TODO: Constraints on Nodes/Edges/Trees so they are consistent between sigs.
--		 Fill in event signature.
/*
pred isConnected[g: Int -> Node -> Node] {
	all u,v: Node | (u->v) in ^(g[Int])
}
*/


fact initialState {
	no first.tree
	--isConnected[first.graph]
}

fact trace {
	all s1: State - last | let s2 = s1.next |
		one e: Event | e.pre = s1 and e.post = s2 
}


fact finalState {
	Node in last.tree[Node][Int]
	--isConnected[last.tree]
}

run {} for 5 but 5 Node






