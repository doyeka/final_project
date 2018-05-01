open prim as PRIM
open kruskal as KRUSKAL
open graph_definitions as GRAPH

/*
pred sameGraph[g1 : KRUSKAL/Node -> Int -> KRUSKAL/Node, g2 : PRIM/Node -> Int -> PRIM/Node] {
	all disj u, v : KRUSKAL/Node | some i : Int | some disj u2, v2 : PRIM/Node | {
		u -> i -> v in g1 iff u2 -> i -> v2 in g2
	}
}
*/

pred sameInSameOut {
	KRUSKAL/first.graph = PRIM/first.graph implies KRUSKAL/last.tree = PRIM/last.tree
}

pred sameEdgeWeight {
	--#(KRUSKAL/first.graph.GRAPH/Node[GRAPH/Node]) = 1
	all disj u, v : GRAPH/Node | u -> v in PRIM/unweightedEdges[KRUSKAL/first.graph] implies {
		one i : Int | u -> i -> v in KRUSKAL/first.graph
	}
}

pred reason {
	some u, v : GRAPH/Node | some i : Int | {
		u -> i -> v in PRIM/last.graph - PRIM/last.tree 
		not KRUSKAL/acyclic[u -> i -> v + PRIM/last.tree]
		let cycle = getSmallestCycle[PRIM/last.tree] | {
			KRUSKAL/cheapestEdge[u -> i -> v , cycle & PRIM/last.tree]
		}	
	}
}

pred smallestCycle[g : GRAPH/Node -> Int -> GRAPH/Node] {
	no u, v: GRAPH/Node | no i : Int | u -> i -> v in g and not KRUSKAL/acyclic[g - u -> i -> v]
}

fun getSmallestCycle[g : GRAPH/Node -> Int -> GRAPH/Node] : GRAPH/Node -> GRAPH/Node {
	{t : KRUSKAL/unweightedEdges[g] | smallestCycle[t]}
}

check sameOutput {sameInSameOut}

check unweighted {not sameInSameOut implies reason}

run {sameEdgeWeight and KRUSKAL/first.graph = PRIM/first.graph}


