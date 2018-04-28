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

sig Node {
	distance: Int,
	infinite: Int,
	previous: Node
}

one sig Source extends Node {}

one sig Sink extends Node {}

sig State {
	graph: Node -> Int -> Node,
	path: Node -> Int -> Node,
	unvisited: set Node
}


sig Event {
	pre: State,
	post: State,
	current: Node
}{
	current in pre.unvisited
	--current.infinite = 0
	no n: pre.unvisited - current | n.distance < current.distance and n.infinite = 1

	all v : Node | isAdjacent[pre, current, v] implies post.

	post.unvisited = pre.unvisited - current
	post.graph = pre.graph
	
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
	
}

--facts

fact edgeProperties {
	-- positive edge weights
	all i : State.graph.Node[Node] | i > 0
}


fact initialState {
	first.unvisited = Node
	pre.first.current = Source
	all n: first.unvisited - Source | n.infinite = 1 and n.distance = 0
	Source.infinite = 0 and Source.distance = 0
	isConnected[first.graph]
}

fact finalState {
	post.last.current = Sink
	--Sink not in last.unvisited
}

fact trace {
	all s1: State - last | let s2 = s1.next | one e: Event | s1 = e.pre and s2 = e.post
}

--preds
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

run {} for 5 but 5 Node
