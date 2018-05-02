open graph_definitions as GRAPH
open util/ordering[State]

sig State {
	graph: Node -> Int -> Node,
	tree: Node -> Int -> Node
}

sig Event {
	pre: State,
	post: State,
	add: GRAPH/Node -> Int -> GRAPH/Node
} {
	add in pre.graph
	add not in pre.tree
	#(add.Node.Int) = 1 and #(add[Node][Int]) = 1

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
	acyclic[pre.tree] and acyclic[post.tree]
}

/*
Ensures the edge 'add' is the cheapest edge in the graph relation 'g'.
*/
pred cheapestEdge[add: GRAPH/Node -> Int -> GRAPH/Node, g: GRAPH/Node -> Int -> GRAPH/Node] {
	all i: g.Node[Node] - add.Node[Node] | i > add.Node[Node]
}

/*
Ensures a graph relation 't' is acyclic.
*/
pred acyclic[t: GRAPH/Node -> Int -> GRAPH/Node] {
	let t' = unweightedEdges[t] | {
		all u, v: GRAPH/Node | u -> v in t' implies v not in u.^(t' - (u -> v))
	}
}

/*
Implementation of bidriection edges.
*/
fact edgeProperties {
	all u,v: GRAPH/Node | all s: State | all i: Int | {
		s->u->i->v in graph implies s->v->i->u in graph and {
			no j: Int - i | s->v->j->u in graph
		}
	}
}

/*
Ensures the graph relation 'g' is connected.
*/
pred isConnected[g: GRAPH/Node -> Int -> GRAPH/Node] {
	all disj u,v: GRAPH/Node | (u->v) in ^(unweightedEdges[g])
}

-- funs
/*
Returns the unweighted graph relation for the weighted graph relation 'g'.
*/
fun unweightedEdges[t: GRAPH/Node -> Int -> GRAPH/Node]: GRAPH/Node -> GRAPH/Node {
	{u, v: GRAPH/Node | some i: Int | u -> i -> v in t}
}

--facts
fact initialState {
	no first.(State <: tree)
}

fact trace {
	all s1: State - last | let s2 = s1.next |
		some e: Event | e.pre = s1 and e.post = s2
}

fact finalState {
	GRAPH/Node in last.tree[Node][Int]
	this/isConnected[last.tree]
}

-- Kruskal's finds the minimum spanning tree if given a connected graph.
run {this/isConnected[first.graph]} for 5 but 5 GRAPH/Node
