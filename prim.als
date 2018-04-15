open util/ordering[State]

sig State {
	graph: set Edge,
	tree_edges: set Edge,
	tree_nodes: set Node
} {
	consistent[tree_edges, tree_nodes]
}

pred consistent[edges : set Edge, nodes: set Node] {
	all e: Edge | e in edges implies e.node1 in nodes and e.node2 in nodes
}

sig Node { }

sig Edge {
	node1: one Node,
	node2: one Node,
	weight: Int
} {
	node1 != node2
}

fact initialState {
	one first.tree_nodes
	Edge in first.graph
	no first.tree_edges
}

sig Event {
	pre: State,
	post: State,
	add: Edge
} {
	(add.node1 in pre.tree_nodes and add.node2 not in pre.tree_nodes) or (add.node1 not in pre.tree_nodes and add.node2 in pre.tree_nodes)
--	let adjacentEdges =  set Edge | {
--		add in adjacentEdges
--		all e: adjacentEdges - add | add.weight <= e.weight
--	}
	let adjacentEdges = pre.graph | {
		all e: adjacentEdges | isAdjacent[pre, e]
		add not in pre.tree_edges
		--add in post.tree_edges
		post.tree_edges = pre.tree_edges + add
	}
}

pred isAdjacent[s: State, e: Edge] {
	e.node1 in s.tree_nodes and e.node2 not in s.tree_nodes or {
		e.node1 not in s.tree_nodes and e.node2 in s.tree_nodes
	}
}

/*
fun getCheapAdjacentEdges[t: set Edge, e: Edge] : set Edge {
	--TODO: add cheap property
	{(e.node1 in t and e.node2 not in t) or (e.node1 not in t and e.node2 in t)}
}	{t -
*/ 

fun getAdjacentEdges[s: State] : set Edge {
	/*
	let free_nodes = {Node - (t.node1 + t.node2)} | {
		{node1.free_nodes + node2.free_nodes}
	}
	*/
	{e: Edge | e.node1 in s.tree_nodes and e.node2 not in s.tree_nodes or e.node1 not in s.tree_nodes and e.node2 in s.tree_nodes}
}



/*
fun cheapestEdge[edges: set Edge] : Edge {
	{
}
*/

fact trace {
	all s1: State - last | let s2 = s1.next |
		one e: Event | e.pre = s1 and e.post = s2 
}




fact finalState {
	Node in last.tree_nodes
}

/*
fact undirectedEdge {
	all disj n1, n2: Node | lone e: Edge | (n1 + n2) in (e.node1 + e.node2)
}
*/

fact positiveEdges {
	all e: Edge | e.weight > 0
}


run {} for 3 but exactly 3 Node, 5 Edge
