--open prim as PRIM
open util/ordering[this/State]

/*
	
    create a graph F (a set of trees), where each vertex in the graph is a separate tree
    create a set S containing all the edges in the graph
    while S is nonempty and F is not yet spanning
        remove an edge with minimum weight from S
        if the removed edge connects two different trees then add it to the forest F, combining two trees into a single tree

*/

sig Node {}

sig State {
	graph: this/Node -> Int -> this/Node,
	tree: this/Node -> Int -> this/Node
}

sig Event {
	pre: this/State,
	post: this/State,
	add: this/Node -> Int -> this/Node
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

pred cheapestEdge[add: this/Node -> Int -> this/Node, g: this/Node -> Int -> this/Node] {
	all i: g.Node[Node] - add.Node[Node] | i > add.Node[Node]
}

pred acyclic[t: this/Node -> Int -> this/Node] {
	let t' = unweightedEdges[t] | {
		all u, v: this/Node | u -> v in t' implies v not in u.^(t' - (u -> v))
	}
}

fact positiveEdges {
	
}


fact edgeProperties {
	all u,v: this/Node | all s: this/State | all i: Int | {
		s->u->i->v in graph implies s->v->i->u in graph and {		--bidirectional
			no j: Int - i | s->v->j->u in graph
		}
	}
	-- positive edges
	all i : State.graph.this/Node[this/Node] | i > 0
}

-- TODO: Constraints on Nodes/Edges/Trees so they are consistent between sigs.
--		 Fill in event signature.

pred isConnected[g: this/Node -> Int -> this/Node] {
	all disj u,v: this/Node | (u->v) in ^(unweightedEdges[g])
}


-- funs
fun unweightedEdges[t: this/Node -> Int -> this/Node]: this/Node -> this/Node {
	{u, v: this/Node | some i: Int | u -> i -> v in t}
}

--facts

fact initialState {
	no first.(this/State <: tree)
	this/isConnected[first.graph]
}

fact trace {
	all s1: this/State - last | let s2 = s1.next |
		some e: this/Event | e.pre = s1 and e.post = s2 
}


fact finalState {
	this/Node in last.tree[Node][Int]
	this/isConnected[last.tree]
}

run {} for 5 but 5 this/Node






