open graph_definitions as GRAPH
open util/ordering[State]
-- sigs

sig State {
	graph: Node -> Int -> Node,
	tree: Node -> Int -> Node
}

one sig Source extends GRAPH/Node {}

sig Event {
	pre: State,
	post: State,
	add: GRAPH/Node -> Int -> GRAPH/Node
} {
	add in pre.graph
	add not in pre.tree
	#(add.GRAPH/Node.Int) = 1 and #(add[GRAPH/Node][Int]) = 1

	let reverseAdd = add[GRAPH/Node][Int] -> (~(add.GRAPH/Node)) | {
		post.graph = pre.graph - add - reverseAdd
		post.tree = pre.tree + add + reverseAdd
	}

	-- Adds the cheapest edge adjacent to the tree, to the tree.
	isAdjacent[pre, add.GRAPH/Node.Int, add[GRAPH/Node][Int]]
	isCheapestAdjacentEdge[pre, add]
}

-- preds
/*
Checks if the edge between GRAPH/Nodes u and v is considered adjacent to the tree
in the given state.
*/
pred isAdjacent[s: State, u: GRAPH/Node, v: GRAPH/Node] {
	let tree_nodes = s.tree[GRAPH/Node][Int] + Source | {
		u in tree_nodes and v not in tree_nodes or {
			u not in tree_nodes and v in tree_nodes
		}
	}
}

/*
Checks if the edge 'add' is the cheapest adjacent edge to add to the tree.
*/
pred isCheapestAdjacentEdge[s: State, add: GRAPH/Node -> Int -> GRAPH/Node] {
	all disj u, v: GRAPH/Node | isAdjacent[s, u, v] implies {
		getWeight[s.graph + s.tree, u -> v] >= add.GRAPH/Node[GRAPH/Node]
	}
}

/*
Checks if the weighted graph relation 'g' is a connected graph.
*/
pred isConnected[g: GRAPH/Node -> Int -> GRAPH/Node] {
	all disj u,v: GRAPH/Node | (u->v) in ^(unweightedEdges[g])
}

--funs
/*
Returns the weight of an edge 'e' in the weighted graph relation 'g'.
*/
fun getWeight[g: GRAPH/Node -> Int -> GRAPH/Node, e: GRAPH/Node -> GRAPH/Node]: Int {
	{i : Int | e.GRAPH/Node -> i -> e[GRAPH/Node] in g}
}

/*
Returns the unweighted edge relation of a weighted graph relation 'g'.
*/
fun unweightedEdges[g: GRAPH/Node -> Int -> GRAPH/Node]: GRAPH/Node -> GRAPH/Node {
	{u, v: GRAPH/Node | some i: Int | u -> i -> v in g}
}

-- facts
/*
Bidirectional edge implementation.
*/
fact edgeProperties {
	all u,v: GRAPH/Node | all s: State | all i: Int | {
		s->u->i->v in graph implies s->v->i->u in graph and {
			no j: Int - i | s->v->j->u in graph
		}
	}
}

/*
Ensuring the initial state starts with an empty tree.
*/
fact initialState {
	no first.tree
}

fact trace {
	all s1: State - last | let s2 = s1.next |
		some e: Event | e.pre = s1 and e.post = s2
}

/*
Ensures all GRAPH/Nodes are in the minimum spanning tree, and that it indeed spans.
*/
fact finalState {
	GRAPH/Node in last.tree[GRAPH/Node][Int]
	isConnected[last.tree]
}

-- Prim's Algorithm for a connected graph.
run {isConnected[first.graph]} for 5 but exactly 5 GRAPH/Node
