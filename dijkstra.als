open util/ordering[State]

sig Node {}

one sig Source extends Node {}

sig State {
	graph: Node -> Int -> Node,
	unvisited: set Node,
	distance: Node -> one Int,
	infinite: Node -> one Int,
	previous: Node -> Node
}

sig Event {
	pre: State,
	post: State,
	current: Node
}{
	current in pre.unvisited
	post.unvisited = pre.unvisited - current
	post.graph = pre.graph

	-- Ensuring current is smallest distance among unvisited, non-infinite nodes.
	pre.infinite[current] = 1 implies no n : pre.unvisited - current | pre.infinite[n] = 0
	no n: pre.unvisited - current | {
		pre.distance[n] < pre.distance[current] and pre.infinite[n] = 0 
	}

	-- Updating distance relation for each neighbor to current.
	all v : Node | {
		isAdjacent[pre, current, v] and pre.infinite[current] = 0 implies {
			-- If infinite or greater distance than current + incident edge:
			let new_dist = plus[pre.distance[current], pre.graph[current].v] | {

				pre.infinite[v] = 1 implies {
					post.infinite[v] = 0
					post.distance[v] = new_dist
					post.previous[v] = current
				}	 

				pre.infinite[v] = 0 and pre.distance[v] >= new_dist implies {
					post.infinite[v] = 0
					post.distance[v] = new_dist
					post.previous[v] = current
				}	 
			
				pre.infinite[v] = 0 and pre.distance[v] < new_dist implies {
					post.infinite[v] = 0
					post.distance[v] = pre.distance[v]
					post.previous[v] = pre.previous[v]
				}
			} 
		} else {
			post.infinite[v] = pre.infinite[v]
			post.distance[v] = pre.distance[v]
			post.previous[v] = pre.previous[v]
		}
	}  
}

--facts

fact initialState {
	no first.previous

	-- All Nodes are unvisited, and Source will be the first visited Node in the algorithm.
	first.unvisited = Node
	pre.first.current = Source

	-- Marking all nodes besides source unvisited with distance = infinity
	all n: first.unvisited - Source | first.infinite[n] = 1 and first.distance[n] = 0
	first.infinite[Source] = 0 and first.distance[Source] = 0
}

fact finalState {
	no last.unvisited
}

fact trace {
	all s1: State - last | let s2 = s1.next | one e: Event | s1 = e.pre and s2 = e.post
}

/*
Ensures edge weights are consistent.
*/
fact oneEdgeWeight {
	all s : State | all u, v : Node | {
		u->v in unweightedEdges[s.graph] implies #(s.graph.u[v]) = 1
	}
}

--preds
/*
Checks if there is another iteration of Dijkstra's possible
*/
pred anotherStepPossible[s : State] {
	some u, v : Node | {
		isAdjacent[s, u, v]
	 	plus[s.distance[u], s.graph[u].v] < s.distance[v]
		s.infinite[u] = 0
	}
}

/*
Checks if all edges within the graph relation of the state 's' are positive.
*/
pred positiveEdges[s : State] {
	all i : s.graph.Node[Node] | i > 0
}

/*
Ensures Node 'v' is adjacent to Node 'u' in the graph relation of the specified State 's'.
*/
pred isAdjacent[s: State, u: Node, v: Node] {
	u -> v in unweightedEdges[s.graph]
}

/*
Ensures the weighted graph relation 'g' is connected.
*/
pred isConnected[g: Node -> Int -> Node] {
	all disj u,v: Node | (u->v) in ^(unweightedEdges[g])
}


-- funs
/*
Returns the unweighted graph relation of the graph relation 'g'.
*/
fun unweightedEdges[g: Node -> Int -> Node]: Node -> Node {
	{u, v: Node | some i: Int | u -> i -> v in g}
}

check dijkstraWin { positiveEdges[first] implies not anotherStepPossible[last]} for 5 but 5 Node

run {positiveEdges[first]} for 5 but 5 Node
