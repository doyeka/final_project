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

pred sameIn {
	KRUSKAL/first.graph = PRIM/first.graph
}

pred sameOut {
	KRUSKAL/last.tree = PRIM/last.tree
}

pred sameEdgeWeight {
	--#(KRUSKAL/first.graph.GRAPH/Node[GRAPH/Node]) = 1
	all disj u, v : GRAPH/Node | u -> v in PRIM/unweightedEdges[KRUSKAL/first.graph] implies {
		one i : Int | u -> i -> v in KRUSKAL/first.graph
	}
}

pred nonUniqueMST {
	some disj u, v : GRAPH/Node | some i : Int | {
		u -> i -> v in PRIM/last.graph - PRIM/last.tree 
		not KRUSKAL/acyclic[u -> i -> v + PRIM/last.tree]
		-- smallest edge in cycle intersecting with last.tree
		let cycle = getCycle[PRIM/last.tree + u -> i -> v] {
			some w, x : Node | w -> x in cycle and PRIM/getWeight[PRIM/first.graph, w->x] = i
		}	
	}
}



pred smallestCycle[g : GRAPH/Node -> Int -> GRAPH/Node] {
	no u, v: GRAPH/Node | no i : Int | u -> i -> v in g and not KRUSKAL/acyclic[g - u -> i -> v]
}

fun getCycle[g : GRAPH/Node -> Int -> GRAPH/Node] : GRAPH/Node -> GRAPH/Node {
	{u, v: GRAPH/Node | u -> v in ^(PRIM/unweightedEdges[g] - u -> v) and u -> v in PRIM/unweightedEdges[g]}
}

check {sameIn and not sameOut implies nonUniqueMST}

check {not nonUniqueMST implies (sameIn and sameOut)}


