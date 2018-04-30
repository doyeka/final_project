/*
   function BellmanFord(list vertices, list edges, vertex source)
   ::distance[],predecessor[]
   
   // This implementation takes in a graph, represented as
   // lists of vertices and edges, and fills two arrays
   // (distance and predecessor) with shortest-path
   // (less cost/distance/metric) information
   
   // Step 1: initialize graph
   for each vertex v in vertices:
       distance[v] := inf             // At the beginning , all vertices have a weight of infinity
       predecessor[v] := null         // And a null predecessor
   
   distance[source] := 0              // The weight is zero at the source
   
   // Step 2: relax edges repeatedly
   for i from 1 to size(vertices)-1:
       for each edge (u, v) with weight w in edges:
           if distance[u] + w < distance[v]:
               distance[v] := distance[u] + w
               predecessor[v] := u
   
   // Step 3: check for negative-weight cycles
   for each edge (u, v) with weight w in edges:
       if distance[u] + w < distance[v]:
           error "Graph contains a negative-weight cycle"
   
   return distance[], predecessor[]
*/

open util/ordering[State]

sig Node {}

one sig Source extends Node {}

one sig Sink extends Node {}

sig State {
	graph: Node -> Int -> Node,
	--path: Node -> Int -> Node,
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

	-- current is smallest distance among unvisited, non-infinite nodes
	no n: pre.unvisited - current | pre.distance[n] < pre.distance[current] and pre.infinite[n] = 0

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
fact negativeCycleFoundAtEnd {
	all s : State - last | s.isNegativeCycle = 0
}

fact initialState {
	
	first.isNegativeCycle = 0
	
	no first.previous

	edgeProperties[first]

	-- all unvisited
	first.unvisited = Node
	--pre.first.current = Source

	-- mark all nodes besides source unvisited with distance = infinity
	all n: first.unvisited - Source | first.infinite[n] = 1 and first.distance[n] = 0
	first.infinite[Source] = 0 and first.distance[Source] = 0

	isConnected[first.graph]
}

fact finalState {
	--Sink not in last.unvisited
	-- TODO: Say there is no *possible* current for which this would happen
	let penultimate = post.last.pre | {
		some n : last.graph.Node.Int + last.graph[Node][Int] | last.distance[n] != penultimate.distance[n] implies {
			last.isNegativeCycle = 1
		} else {
			last.isNegativeCycle = 0
		}
		
	}
}

fact trace {
	all s1: State - last | let s2 = s1.next | one e: Event | s1 = e.pre and s2 = e.post
}

--preds

pred edgeProperties[s : State] {
	-- positive edge weights
	--all i : s.graph.Node[Node] | i > 0
	all u, v : Node | one i : Int | u -> i -> v in s.graph 
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

run {} for 5 but 2 Node, 5 Int
