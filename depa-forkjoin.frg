#lang forge

sig Vertex {
    depth: one Int,
    path: pfunc Int -> Int,
    children: set Vertex
}

one sig Root extends Vertex {}

one sig Sink extends Vertex {}

pred binarySpawnTouch {
    all v: Vertex | #v.children <= 2 and #children.v <= 2
}

pred justSpawned[v: Vertex] {
    some {parent: children.v | #parent.children > 1}
}

-- a freshly spawned vertex has but one parent
pred uniqueParent {
    all parent: Vertex | #parent.children > 1 implies {
        children.(parent.children) = parent
    }
}

pred wellFormed {
    no children.Root
    no Sink.children

    no v: Vertex | reachable[v, v, children] -- no cycle
    Root.*children = Vertex
    (*children.Sink) = Vertex

    uniqueParent

    no Root.path
    Root.depth = 0

    binarySpawnTouch
}

pred nonSinkHaveChildren {
    all v: Vertex - Sink | some v.children
}

pred nonRootHaveParent {
    all v: Vertex - Root | some children.v
}

pred maxOneSharedParent {
    all disj left, right: Vertex | {
        lone (children.left & children.right)
    }
}

assert wellFormed is sufficient for nonSinkHaveChildren
assert wellFormed is sufficient for nonRootHaveParent
assert wellFormed is sufficient for maxOneSharedParent

assert wellFormed is sat

pred depthCalc {
    all v: Vertex - Root | {
        v.depth = add[max[children.v.depth], 1]
    }
}

fun nextIdx[indices: set Int]: Int {
    no indices => 0
    else add[max[indices], 1]
}

pred pathCalc {
    all spawn: {parent: Vertex | #parent.children > 1} {
        let j = nextIdx[inds[spawn.path]] | {
            one left: spawn.children | left.path[j] = 4
            one right: spawn.children | right.path[j] = -4
            all i: Int - j | {
                spawn.children.path[i] = spawn.path[i]
            }
        }
    }

    all touch: {child: Vertex | #children.child > 1} {
        let targetIdx = inds[children.touch.path] | {
            all i: targetIdx | touch.path[i] = (sum parent: children.touch | sum[parent.path[i]])
            all j: Int - targetIdx | touch.path[j] = children.touch.path[j]
        }
    }

    // all dummy: {v: Vertex | #children.v = 1 and #v.children = 1} {
    //     all i: Int | dummy.path[i] = children.dummy.path[i]
    // }
}

pred valid {
    wellFormed

    depthCalc
    pathCalc
}

pred monotonicDepth {
    all v: Vertex - Sink | {
        min[v.^children.depth] > v.depth
    }
}

assert valid is sat
assert valid is sufficient for monotonicDepth

pred nontrivial {
    some (Vertex - Root - Sink)
    some {v: Vertex | #v.children > 1}
    #Root.children > 1
    #children.Sink > 1
}

run {
    valid
    nontrivial
} for 8 Vertex