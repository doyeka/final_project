/*
    Mark all nodes unvisited. Create a set of all the unvisited nodes called the unvisited set.

    Assign to every node a tentative distance value: set it to zero for our initial node and to infinity for all other nodes. 
		Set the initial node as current.

    For the current node, consider all of its unvisited neighbors and calculate their tentative distances through the current node. 
		Compare the newly calculated tentative distance to the current assigned value and assign the smaller one. For example, if the 
		current node A is marked with a distance of 6, and the edge connecting it with a neighbor B has length 2, then the distance to 
		B through A will be 6 + 2 = 8. If B was previously marked with a distance greater than 8 then change it to 8. Otherwise, keep the 
		current value.

    When we are done considering all of the neighbors of the current node, mark the current node as visited and remove it from 
		the unvisited set. A visited node will never be checked again.

    Move to the next unvisited node with the smallest tentative distances and repeat the above steps which check neighbors and mark visited.

    If the destination node has been marked visited (when planning a route between two specific nodes) or if the smallest tentative distance 
		among the nodes in the unvisited set is infinity (when planning a complete traversal; occurs when there is no connection between the 
		initial node and remaining unvisited nodes), then stop. The algorithm has finished.

    Otherwise, select the unvisited node that is marked with the smallest tentative distance, set it as the new "current node", 
		and go back to step 3.
*/

open util/ordering[State]

sig Node {}

one sig Source extends Node {}

sig State {
	graph: Node -> Int -> Node,
	--path: Node -> Int -> Node,
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

	-- current is smallest distance among unvisited, non-infinite nodes
	pre.infinite[current] = 1 implies no n : pre.unvisited - current | pre.infinite[n] = 0
	no n: pre.unvisited - current | {
		pre.distance[n] < pre.distance[current] and pre.infinite[n] = 0 
	}

	-- update distance variables of neighbors
	all v : Node | {
		isAdjacent[pre, current, v] and pre.infinite[current] = 0 implies {
			-- if infinite or greater distance than current + incident edge
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
	
	--TODO: update distance variable of neighbors if new, shorter distance is possible
	-- choose shortest neighbor and add it to the path
	-- set current to the next node along the path
	/*
	all n: pre.graph[current][Int] | n in pre.unvisited |
		n.infinite = 1 implies {
			post.graph[current][Int]
-- TODO: Specify how to access the post graph version of a node.
		}
	}
	*/
	

--facts


fact initialState {
	
	no first.previous

	-- all unvisited
	first.unvisited = Node
	pre.first.current = Source

	-- mark all nodes besides source unvisited with distance = infinity
	all n: first.unvisited - Source | first.infinite[n] = 1 and first.distance[n] = 0
	first.infinite[Source] = 0 and first.distance[Source] = 0

	--isConnected[first.graph]
}

fact finalState {
	no last.unvisited
}

fact trace {
	all s1: State - last | let s2 = s1.next | one e: Event | s1 = e.pre and s2 = e.post
}

--preds

pred anotherStepPossible[s : State] {
	some u, v : Node | {
		isAdjacent[s, u, v]
	 	plus[s.distance[u], s.graph[u].v] < s.distance[v]
		s.infinite[u] = 0
	}
}

fact oneEdgeWeight {
	all s : State | all u, v : Node | {
		u->v in unweightedEdges[s.graph] implies #(s.graph.u[v]) = 1
	}
}

pred positiveEdges[s : State] {
	all i : s.graph.Node[Node] | i > 0
}

pred isAdjacent[s: State, u: Node, v: Node] {
	u -> v in unweightedEdges[s.graph]
}

pred isConnected[g: Node -> Int -> Node] {
	all disj u,v: Node | (u->v) in ^(unweightedEdges[g])
}


-- funs
fun unweightedEdges[t: Node -> Int -> Node]: Node -> Node {
	{u, v: Node | some i: Int | u -> i -> v in t}
}

check dijkstraWin { positiveEdges[first] implies not anotherStepPossible[last]} for 5 but 5 Node

check dijkstraFail { (not positiveEdges[first]) implies not anotherStepPossible[last]} for 5 but 5 Node






run {} for 5 but 5 Node
