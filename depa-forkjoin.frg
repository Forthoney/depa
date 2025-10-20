#lang forge

sig Vertex {
    depth: one Int,
    path: pfunc Int -> Int,
    left: lone Vertex,
    right: lone Vertex
}

one sig Root extends Vertex {}

one sig Sink extends Vertex {}

fun children[v: Vertex]: set Vertex {
    v.left + v.right
}

fun parents[v: Vertex]: set Vertex {
    left.v + right.v
}

-- By construction, a spawn is binary since a vertex has at most two children
-- A touch is not, however, and requires this predicate
pred binaryTouch {
    all v: Vertex | #parents[v] <= 2
}

pred wellFormed {
    no left.Root
    no right.Root
    
    no Sink.left
    no Sink.right

    no v: Vertex | reachable[v, v, left, right] -- no cycle
    all v: Vertex - Root | reachable[v, Root, left, right] -- starts from root
    all v: Vertex - Sink | reachable[Sink, v, left, right] -- ends at sink

    no Root.path
    Root.depth = 0

    binaryTouch
    isSeqOf[Vertex.path, Int]
}

pred nonSinkHaveChildren {
    all v: Vertex - Sink | some children[v]
}

pred nonRootHaveParent {
    all v: Vertex - Root | some parents[v]
}

pred binarySpawnTouch {
    all v: Vertex | #parents[v] <= 2 and #children[v] <= 2
}

assert wellFormed is sufficient for nonSinkHaveChildren
assert wellFormed is sufficient for nonRootHaveParent
assert wellFormed is sufficient for binarySpawnTouch

assert wellFormed is sat

-- Only vertices that meaningfully spawn or join are in the output
pred compact {
    no v: Vertex | #parents[v] = 1 and #children[v] = 1
}

pred depthCalc {
    all v: (Vertex - Root) | {
        v.depth = add[max[children[v].depth], 1]
    }
}

fun nextIdx[indices: set Int]: Int {
    no indices => 0
    else add[max[indices], 1]
}

pred pathCalc {
    all spawnPoint: {v: Vertex | some v.left and some v.right} | {
        let indices = inds[spawnPoint.path] | {
            all i: indices | {
                spawnPoint.left.path[i] = spawnPoint.path[i]
                spawnPoint.right.path[i] = spawnPoint.path[i]
            }
            // spawnPoint.left.path[nextIdx[indices]] = 1
            // spawnPoint.right.path[nextIdx[indices]] = 1
        }
    }
}

pred valid {
    wellFormed
    compact

    depthCalc
    pathCalc
}

pred monotonicDepth {
    all parent: Vertex - Sink | {
        all child: Vertex | reachable[child, parent, left, right] implies child.depth > parent
    }
}

assert valid is sat
assert valid is sufficient for monotonicDepth

pred nontrivial {
    some (Vertex - Root - Sink)
}

run {
    valid
    nontrivial
}