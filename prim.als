open util/ordering[State]
-- sigs

/*


    Initialize a tree with a single vertex, chosen arbitrarily from the graph.
    Grow the tree by one edge: of the edges that connect the tree to vertices not yet in the tree, find the minimum-weight edge, and transfer it to the tree.
    Repeat step 2 (until all vertices are in the tree).


*/
sig Node {
}

sig State {
	graph: Node -> Int -> Node,
	tree: Node -> Int -> Node
}


sig Event {
	pre: State,
	post: State,
	add: Node -> Int -> Node
} {
	add in pre.graph
	add not in pre.tree
	#(add.Node.Int) = 1 and #(add[Node][Int]) = 1

	let reverseAdd = add[Node][Int] -> (~(add.Node)) | {
		post.graph = pre.graph - add - reverseAdd
		post.tree = pre.tree + add + reverseAdd
	}

	-- add must be an edge adjacent to pre.tree and it has to be the cheapest one
	--isAdjacent[pre, add]
	isCheapestEdge[pre, add]
}

-- preds
/*
pred isAdjacent[s: State, e: Node -> Int -> Node] {
	let tree_nodes = s.tree[Node][Int] | {
		e.Node.Int in tree_nodes and e[Node][Int] not in tree_nodes or {
			e.Node.Int not in tree_nodes and e[Node][Int] in tree_nodes
		}
	}
}
*/
pred isAdjacent[s: State, u: Node, v: Node] {
	let tree_nodes = s.tree[Node][Int] | {
		u in tree_nodes and v not in tree_nodes or {
			u not in tree_nodes and v in tree_nodes
		}
	}
}


pred isCheapestEdge[s: State, add: Node -> Int -> Node] {
	all disj u, v: Node | isAdjacent[s, u, v] and {
		getWeight[s.graph + s.tree, u -> v] >= add.Node[Node]
	}
}

pred isConnected[g: Node -> Int -> Node] {
	all disj u,v: Node | (u->v) in ^(unweightedEdges[g])
}

--funs

fun getWeight[t: Node -> Int -> Node, e: Node -> Node]: Int {
	{i : Int | e.Node -> i -> e[Node] in t}
}

fun unweightedEdges[t: Node -> Int -> Node]: Node -> Node {
	{u, v: Node | some i: Int | u -> i -> v in t}
}

/*
fun adjacentEdges[s: State]: Node -> Node {
	{u, v: Node | u in s.tree[Node][Int] and v not in s.tree[Node][Int] or {
			u not in s.tree[Node][Int] and v in s.tree[Node][Int]
	}}
}
*/

-- facts

fact initialState {
	no first.tree
	isConnected[first.graph]
}

fact trace {
	all s1: State - last | let s2 = s1.next |
		one e: Event | e.pre = s1 and e.post = s2 
}	

fact finalState {
	Node in last.tree[Node][Int]
	isConnected[last.tree]
}

fact positiveEdges {
	all i : State.graph.Node[Node] | i > 0
}

// TODO: Show how it fails for negative edge weights? Or is that only dijkstras? Only Dijskstra's

run {} for 5 but exactly 5 Node
