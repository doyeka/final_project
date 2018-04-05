open util/ordering[State]

sig State {
	graph: set Node,
	tree: set Node
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
	one first.tree
	Node in first.graph
}

sig Event {
	pre: State,
	post: State,
	add: Node
} {

	add in pre.graph
	add not in pre.tree
	add in post.tree
	
	let cheapestEdge = Edge | 

}

fun getCheapAdjacentEdges[t: set Node] : Edge {
	--TODO: add cheap property
	{e: Edge | (e.node1 in t and e.node2 not in t) or (e.node1 not in t and e.node2 in t)}
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
	no last.graph
	Node in last.tree
}

/*
fact undirectedEdge {
	all disj n1, n2: Node | lone e: Edge | (n1 + n2) in (e.node1 + e.node2)
}
*/

fact positiveEdges {
	all e: Edge | e.weight > 0
}


run {} for 12 but exactly 3 Node, 5 Edge
