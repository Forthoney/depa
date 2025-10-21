#lang forge

option no_overflow true


sig Vertex {
    depth: one Int,
    path: pfunc Int -> Int,
    children: set Vertex
}

one sig Root extends Vertex {}

pred binarySpawnTouch {
    all v: Vertex | #v.children <= 2 and #children.v <= 2
}

pred wellFormed {
    no children.Root
    all v: Vertex | not reachable[v, v, children]
    binarySpawnTouch

    Root.*children = Vertex -- actually more of an "optimization"
}

pred spawn {
    all parent: {v: Vertex | #v.children > 1} | {
        -- spawned children should not have any other parent besides me
        children.(parent.children) = parent
    }
}

pred causedBySpawn[v: Vertex] {
    some parent: children.v | {
        #parent.children = 2
    }
}

pred causedByTouch[v: Vertex] {
    #children.v = 2 -- two parents
}

pred vertexCreatedWithReason {
    all v: Vertex - Root | causedBySpawn[v] or causedByTouch[v]
}

pred vertexCreation {
    spawn
    vertexCreatedWithReason
}

pred wellFormedDePa {
    no Root.path
    Root.depth = 0
}

pred append[old, new: pfunc Int -> Int, e: Int] {
    let indices = inds[old] | {
        let insertAt = no indices => 0 else add[max[indices], 1] | {
            new[insertAt] = e
            all i: indices | new[i] = divide[old[i], 2]
            all j: Int - indices - insertAt | new[j] = old[j]
        }
    }
}

pred spawnDePa {
    all spawnPoint: {v: Vertex | #v.children > 1} | {
        spawnPoint.children.depth = add[spawnPoint.depth, 1]

        let v = divide[min[Int], 2] | {
            one left: spawnPoint.children | append[spawnPoint.path, left.path, v]
            one right: spawnPoint.children | append[spawnPoint.path, right.path, abs[v]]
        }
    }
}

pred touchDePa {
    all touchPoint: {v: Vertex | #children.v > 1} | {
        touchPoint.depth = add[max[(children.touchPoint).depth], 1]

        let parents = children.touchPoint | {
            all i: inds[parents.path] | {
                touchPoint.path[i] = (sum parent: parents | sum[parent.path[i]])
            }
            all i: Int - inds[parents.path] | no touchPoint.path[i]
        }
    }
}

pred depa {
    wellFormedDePa
    spawnDePa
    touchDePa
}

pred valid {
    wellFormed
    vertexCreation
    depa
}

pred monotonicDepth {
    all v: Vertex | some v.children implies {
        v.depth < v.^children.depth
    }
}

pred uniqueTag {
    all disj v1, v2: Vertex | {
        v1.depth != v2.depth or
        (some i: Int | v1.path[i] != v2.path[i])
    }
}

assert valid is sat
assert valid is sufficient for monotonicDepth for 16 Vertex, 5 Int
assert valid is sufficient for uniqueTag for 16 Vertex, 5 Int

-- predicates for getting interesting visualizations

pred nontrivial {
    Vertex != Root
}

run {
    valid
    nontrivial
} for 16 Vertex, 5 Int