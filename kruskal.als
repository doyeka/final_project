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
	add not in pre.tree
	#(add.Node.Int) = 1 and #(add[Node][Int])	= 1   --For some reason "#" only works for unary sets
	
	cheapestEdge[add, pre.graph]

	let reverseAdd = add[Node][Int] -> (~(add.Node)) | {
		post.graph = pre.graph - add - reverseAdd
		acyclic[pre.tree + add + reverseAdd] implies {
			post.tree = pre.tree + add + reverseAdd
		}
		not acyclic[pre.tree + add + reverseAdd] implies {
			post.tree = pre.tree
		}
	}

	/*
	Issue: Change so that trees can be made with low cost self loops

	Right now, this is over-constrained to the point that the lowest
	cost tree must just *happen* to be acyclic and perfect.

	Proposed solution: We could change it so that whenever add 
	creates a cycle, we just remove the edge from the graph.
	*/
	acyclic[pre.tree] and acyclic[post.tree]

}

pred cheapestEdge[add: Node -> Int -> Node, g: Node -> Int -> Node] {
	all i: g.Node[Node] - add.Node[Node] | i > add.Node[Node]
}

pred acyclic[t:  Node -> Int -> Node] {
	let t' = unweightedEdges[t] | {
		all u, v: Node | u -> v in t' implies v not in u.^(t' - (u -> v))
	}
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

pred isConnected[g: Node -> Int -> Node] {
	all disj u,v: Node | (u->v) in ^(unweightedEdges[g])
}


-- funs
fun unweightedEdges[t: Node -> Int -> Node]: Node -> Node {
	{u, v: Node | some i: Int | u -> i -> v in t}
}

--facts

fact initialState {
	no first.tree
	isConnected[first.graph]
}

fact trace {
	all s1: State - last | let s2 = s1.next |
		one e: Event | e.pre = s1 and e.post = s2 
}


fact finalState {
	Node in last.tree[Node][Int]
	isConnected[last.tree]
}

run {} for 5 but 5 Node






