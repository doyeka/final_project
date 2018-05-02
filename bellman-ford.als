open util/ordering[State]

sig Node {}

one sig Source extends Node {}

sig State {
	graph: Node -> Int -> Node,
	unvisited: set Node,
	distance: Node -> one Int,
	infinite: Node -> one Int,
	previous: Node -> Node,
	isNegativeCycle: Int
}


sig Event {
	pre: State,
	post: State,
	current: Node
}{
	current in pre.unvisited
	
	#(pre.unvisited) = 1 and post != last implies post.unvisited = Node
	#(pre.unvisited) = 1 and post = last implies post.unvisited = pre.unvisited - current
	#(pre.unvisited) != 1 and post != last implies post.unvisited = pre.unvisited - current

	post.graph = pre.graph

	-- Ensuring current is smallest distance among unvisited, non-infinite nodes.
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
/*
Ensures the negative cycle isn't updated until the last state.
*/
fact negativeCycleFoundAtEnd {
	all s : State - last | s.isNegativeCycle = 0
}

fact initialState {
	no first.previous
	edgeProperties[first]
	first.unvisited = Node

	-- Marking all nodes besides source unvisited with distance = infinity
	all n: first.unvisited - Source | first.infinite[n] = 1 and first.distance[n] = 0
	first.infinite[Source] = 0 and first.distance[Source] = 0

	isConnected[first.graph]
}

fact finalState {
	anotherStepPossible[last] implies last.isNegativeCycle = 1 else last.isNegativeCycle = 0
}

/*
Ensures the addition for distances does not our bit width.
*/
fact managableEdgeWeights {
	all i : Int | i in first.graph.Node[Node] implies { i > -10 and i < 10}
}


fact traces {
  all s: State - last |
    some e: Event | e.pre = s and e.post = s.next
}

--preds
/*
Checks if another iteration of the algorithm is possible
*/
pred anotherStepPossible[s : State] {
	some u, v : Node | {
		isAdjacent[s, u, v]
	 	plus[s.distance[u], s.graph[u].v] < s.distance[v]
	}
}

/*
Ensures edge weights are consistent
*/
pred edgeProperties[s : State] {
	all u, v : Node | one i : Int | u -> i -> v in s.graph 
}

/*
Checks if two nodes (u,v) are adjacent in the specified state 's'.
*/
pred isAdjacent[s: State, u: Node, v: Node] {
	u -> v in unweightedEdges[s.graph]
}

/*
Checks if a graph relation 'g' is connected.
*/
pred isConnected[g: Node -> Int -> Node] {
	all disj u,v: Node | (u->v) in ^(unweightedEdges[g])
}

-- funs
/*
Returns the unweighted edge relation of a weighted edge relation 'g'.
*/
fun unweightedEdges[t: Node -> Int -> Node]: Node -> Node {
	{u, v: Node | some i: Int | u -> i -> v in t}
}

run {} for 4 but exactly 2 Node, 4 Event, 5 Int
