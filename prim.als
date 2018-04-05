open util/ordering[State]

sig State {
	graph: set Edge,
	tree: set Edge
}

sig Event {
	pre: State,
	post: State,
	add: Edge
}

sig Node {
	--edges: set Edge
}

sig Edge {
	node1: one Node,
	node2: one Node,
	weight: Int
}

fact initialState {
	no first.tree
	Edge in first.graph
}

fact trace {
	all s1: State - last | let s2 = s1.next |
		one e: Event | e.pre = s1 and e.post = s2 
}

fact finalState {
	no last.graph
	Edge in last.tree
}

fact undirectedEdge {
	all n1, n2: Node | one e: Edge | (n1 + n2) in (e.node1 + e.node2)
}

fact positiveEdges {
	all e: Edge | e.weight > 0
}


run for exactly ... {}
