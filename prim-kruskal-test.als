open prim as PRIM
open kruskal as KRUSKAL

pred sameGraph[g1 : KRUSKAL/Node -> Int -> KRUSKAL/Node, g2 : PRIM/Node -> Int -> PRIM/Node] {
	all disj u, v : KRUSKAL/Node | some i : Int | some disj u2, v2 : PRIM/Node | {
		u -> i -> v in g1 iff u2 -> i -> v2 in g2
	}
}

check sameInSameOut {sameGraph[KRUSKAL/first.graph, PRIM/first.graph] implies sameGraph[KRUSKAL/last.tree, PRIM/last.tree]}

run {sameGraph[KRUSKAL/first.graph, PRIM/first.graph]}
