open graph_definitions as GRAPH
open util/ordering[State]
-- sigs

/*


    Initialize a tree with a single vertex, chosen arbitrarily from the graph.
    Grow the tree by one edge: of the edges that connect the tree to vertices not yet in the tree, find the minimum-weight edge, and transfer it to the tree.
    Repeat step 2 (until all vertices are in the tree).


*/

sig State {
	graph: Node -> Int -> Node,
	tree: Node -> Int -> Node
}

one sig First extends GRAPH/Node {}


sig Event {
	pre: State,
	post: State,
	add: GRAPH/Node -> Int -> GRAPH/Node
} {
	/*
		Issue: In the first State, it can add whatever it wants
		because nothing is in tree.

		Additionally, adjacent doesn't
	*/
	add in pre.graph
	add not in pre.tree
	#(add.GRAPH/Node.Int) = 1 and #(add[GRAPH/Node][Int]) = 1

	let reverseAdd = add[GRAPH/Node][Int] -> (~(add.GRAPH/Node)) | {
		post.graph = pre.graph - add - reverseAdd
		post.tree = pre.tree + add + reverseAdd
	}

	-- add must be an edge adjacent to pre.tree and it has to be the cheapest one
	isAdjacent[pre, add.GRAPH/Node.Int, add[GRAPH/Node][Int]]
	isCheapestEdge[pre, add]
}

-- preds
/*
pred isAdjacent[s: State, e: GRAPH/Node -> Int -> GRAPH/Node] {
	let tree_GRAPH/Nodes = s.tree[GRAPH/Node][Int] | {
		e.GRAPH/Node.Int in tree_GRAPH/Nodes and e[GRAPH/Node][Int] not in tree_GRAPH/Nodes or {
			e.GRAPH/Node.Int not in tree_GRAPH/Nodes and e[GRAPH/Node][Int] in tree_GRAPH/Nodes
		}
	}
}
*/
pred isAdjacent[s: State, u: GRAPH/Node, v: GRAPH/Node] {
	let tree_nodes = s.tree[GRAPH/Node][Int] + First | {
		u in tree_nodes and v not in tree_nodes or {
			u not in tree_nodes and v in tree_nodes
		}
	}
}


pred isCheapestEdge[s: State, add: GRAPH/Node -> Int -> GRAPH/Node] {
	/*
	 Issue: we want all the GRAPH/Nodes such that they are adjacent, but we don't require all
	GRAPH/Nodes to be adjacent...
	*/
	all disj u, v: GRAPH/Node | isAdjacent[s, u, v] implies {
		getWeight[s.graph + s.tree, u -> v] >= add.GRAPH/Node[GRAPH/Node]
	}
}

pred isConnected[g: GRAPH/Node -> Int -> GRAPH/Node] {
	all disj u,v: GRAPH/Node | (u->v) in ^(unweightedEdges[g])
}

--funs

fun getWeight[t: GRAPH/Node -> Int -> GRAPH/Node, e: GRAPH/Node -> GRAPH/Node]: Int {
	{i : Int | e.GRAPH/Node -> i -> e[GRAPH/Node] in t}
}

fun unweightedEdges[t: GRAPH/Node -> Int -> GRAPH/Node]: GRAPH/Node -> GRAPH/Node {
	{u, v: GRAPH/Node | some i: Int | u -> i -> v in t}
}

/*
fun adjacentEdges[s: State]: GRAPH/Node -> GRAPH/Node {
	{u, v: GRAPH/Node | u in s.tree[GRAPH/Node][Int] and v not in s.tree[GRAPH/Node][Int] or {
			u not in s.tree[GRAPH/Node][Int] and v in s.tree[GRAPH/Node][Int]
	}}
}
*/

-- facts

fact edgeProperties {
	all u,v: GRAPH/Node | all s: State | all i: Int | {
		s->u->i->v in graph implies s->v->i->u in graph and {		--bidirectional
			no j: Int - i | s->v->j->u in graph
		}

	}
}

fact initialState {
	-- We need to somehow choose a random GRAPH/Node and add it
	no first.tree
	isConnected[first.graph]
}

fact trace {
	all s1: State - last | let s2 = s1.next |
		some e: Event | e.pre = s1 and e.post = s2
}

fact finalState {
	GRAPH/Node in last.tree[GRAPH/Node][Int]
	isConnected[last.tree]
}

fact positiveEdges {
	all i : State.graph.GRAPH/Node[GRAPH/Node] | i > 0
}

// TODO: Show how it fails for negative edge weights? Or is that only dijkstras? Only Dijskstra's

run {} for 5 but exactly 5 GRAPH/Node
