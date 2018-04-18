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
	--QUESTION: what does "one" do in this case?
	node1: Node,
	node2: Node,
	weight: Int
} {
	--QUESTION: can we have self loops?
	--QUESTION: does the graph have to contain every node? Does it need to be connected? Probs yes
	node1 != node2
}

fact initialState {
	one first.tree_nodes
	Edge in first.graph
	no first.tree_edges
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
	add not in pre.tree_edges
	post.tree_edges = pre.tree_edges + add
	post.tree_nodes = pre.tree_nodes + add.node1 + add.node2
	post.graph = pre.graph
	-- add must be an edge adjacent to pre.tree and it has to be the cheapest one
	isAdjacent[pre, add]
	isCheapestEdge[pre, add]
}	


pred isAdjacent[s: State, e: Edge] {
	e.node1 in s.tree_nodes and e.node2 not in s.tree_nodes or {
		e.node1 not in s.tree_nodes and e.node2 in s.tree_nodes
	}
}

pred isCheapestEdge[s: State, cheapest: Edge] {
	no e: s.graph - s.tree_edges | {
		e.weight < cheapest.weight
		isAdjacent[s, e]
	}
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

// TODO: Show how it fails for negative edge weights? Or is that only dijkstras?

run {} for 5 but exactly 5 Node, 7 Edge
