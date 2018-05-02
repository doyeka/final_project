open prim as PRIM
open kruskal as KRUSKAL
open graph_definitions as GRAPH

/*
Checks equality of the initial graph in both algorithms.
*/
pred sameIn {
	KRUSKAL/first.graph = PRIM/first.graph
}

/*
Checks equality of the last tree in both algorithms.
*/
pred sameOut {
	KRUSKAL/last.tree = PRIM/last.tree
}

/*
Checks non-uniqueness of minimum spanning trees.
*/
pred nonUniqueMST {
	some disj u, v : GRAPH/Node | some i : Int | {
		u -> i -> v in PRIM/last.graph - PRIM/last.tree 
		not KRUSKAL/acyclic[u -> i -> v + PRIM/last.tree]
		/*	
		The MST will be non-unique if there exists an edge that can be added to the MST
		to create a cycle in the MST, and if that edge has a weight equal to an edge that 
		exists in the MST.
		*/
		let cycle = getCycle[PRIM/last.tree + u -> i -> v] {
			some w, x : Node | w -> x in cycle and PRIM/getWeight[PRIM/first.graph, w->x] = i
		}	
	}
}

/*
Returns (unweighted) edges that form a cycle in a given weighted graph relation.
*/
fun getCycle[g : GRAPH/Node -> Int -> GRAPH/Node] : GRAPH/Node -> GRAPH/Node {
	{u, v: GRAPH/Node | u -> v in ^(PRIM/unweightedEdges[g] - u -> v) and u -> v in PRIM/unweightedEdges[g]}
}

check {sameIn and not sameOut implies nonUniqueMST}

check {not nonUniqueMST implies (sameIn and sameOut)}


