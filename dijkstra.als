open util/ordering[State]

sig Node {
	distance: Int,
	infinite: Int
}

sig State {
	graph: Node -> Int -> Node,
	unvisited: set Node,
	source: Node,
	destination: Node
}

sig Event {
	pre: State,
	post: State,
	current: Node
}{
	current in pre.unvisited
	post.unvisited = pre.unvisited - current
}

--facts

fact directionalEdges {
	all u,v: Node | all s: State | all i: Int | {
		s->u->i->v in graph implies s->v->i->u not in graph --and {	
	--		no j: Int - i | s->v->j->u in graph
--		}
	}
}

fact initialState {
	first.unvisited = Node
	all n: first.unvisited | n.infinite = 1 and n.distance = 0
	isConnected[first.graph]
}

fact finalState {
	last.destination not in last.unvisited
}

fact trace {
	all s1: State - last | let s2 = s1.next | one e: Event | s1 = e.pre and s2 = e.post
}

--preds
pred isConnected[g: Node -> Int -> Node] {
	all disj u,v: Node | (u->v) in ^(unweightedEdges[g])
}


-- funs
fun unweightedEdges[t: Node -> Int -> Node]: Node -> Node {
	{u, v: Node | some i: Int | u -> i -> v in t}
}

run {} for 5 but 5 Node
