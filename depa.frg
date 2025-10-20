#lang forge

abstract sig Path {}
one sig Left, Right extends Path {}

abstract sig Vertex {
    depth: one Int,
    path: pfunc Int -> Path
}

sig Nonterminal extends Vertex {
    children: set Vertex
}
one sig Root extends Nonterminal {}
one sig Terminal extends Vertex {}

pred rootVertex {
    Root.depth = 0
    no children.Root
    all v: Vertex | v != Root implies {
        reachable[v, Root, children]
    }
}

pred wellFormedGraph {
    all v: Vertex | not reachable[v, v, children]
}

pred compactGraph {
    all v: Vertex | #children.v <= 1 implies #v.children = 2
}

pred wellFormedVertex {
    rootVertex
    all v: Nonterminal | #v.children <= 2
    all v: Nonterminal | not reachable[v, v, children]
}

pred wellFormedDepth {
    all parent: Nonterminal | {
        all child: parent.children | child.depth = parent.depth + 1
    }
}

run {
    wellFormedVertex
    wellFormedGraph
    compactGraph
    // wellFormedDepth
    // rootVertexDepa
} for exactly 5 Vertex