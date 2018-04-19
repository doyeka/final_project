open util/ordering[State]

sig Node {
	distance: Int
}

sig 

sig State {
	unvisited: set Node,
	destination: Node,
	graph: 
}

sig Event{
	pre: State,
	post: State,
	current: Node,
}{
	pre.destination = post.destination
	current in pre.unvisited
	post.unvisited = pre.unvisited - current
	post.c
}

--facts

fact initialState {
	first.unvisited = Node
	all n: first.unvisited | n.distance = 0  
}

fact trace {
	all s1: State - last | let s2 = s1.next | one e: Event | s1 = e.pre and s2 = e.post
}

run {}
