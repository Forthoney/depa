#lang forge
// option solver "../glucose/glucose-simp"

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

pred spawnPoint[v: Vertex] {
    #v.children > 1
}

pred touchPoint[v: Vertex] {
    #children.v > 1
}

pred pathCalc {
    -- If i am a spawn point, my children should have these values
    all spawn: {v: Vertex | spawnPoint[v]} | {
        let j = nextIdx[inds[spawn.path]] | {
            one left: spawn.children | left.path[j] = abs[divide[min[Int], 2]]
            one right: spawn.children | right.path[j] = divide[min[Int], 2]
            all i: Int - j | {
                all child: spawn.children | {
                    child.path[i] = (one spawn.path[i] => divide[spawn.path[i], 2] else none)
                }
            }
        }
    }

    -- If i am a touch point, I should take these values from my parents
    all touch: {v: Vertex | touchPoint[v]} {
        let targetIdx = inds[children.touch.path] | {
            all i: targetIdx | {
                touch.path[i] = 
                (some children.touch.path[i] => (sum parent: children.touch | sum[parent.path[i]])
                else none)
            }
            all j: Int - targetIdx | touch.path[j] = children.touch.path[j]
        }
    }
}

-- a bit of a hack to get around useless intermediate vertices appearing
-- The premise is that DePa only creates vertices when they are actually needed
pred onlyNecessary {
    all v: Vertex | {
        spawnPoint[v] or touchPoint[v] or
        spawnPoint[children.v] and touchPoint[v.children]
    }
    all v: Vertex | touchPoint[v] and not spawnPoint[v] implies {
        all child: v.children | not spawnPoint[child]
    }
}

pred valid {
    wellFormed

    depthCalc
    pathCalc

    onlyNecessary
}

pred monotonicDepth {
    all v: Vertex - Sink | {
        min[v.^children.depth] > v.depth
    }
}

pred sinkResolved {
    all i: Int | no Sink.path[i] or Sink.path[i] = 0
}

pred validSeq {
    all v: Vertex | isSeqOf[v.path, Int]
}

assert valid is sat
assert valid is sufficient for validSeq
assert valid is sufficient for monotonicDepth
assert valid is sufficient for sinkResolved for 16 Vertex, 5 Int

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