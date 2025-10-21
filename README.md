# DePa on DAGs
A generalization of DePa to operate on DAGs as opposed to merely series-parallel graphs.
This presents the algorithmic description without regard for efficiency

## Key differences
The `path` is treated not as a list of bits, but rather as a **vector** of rational numbers.

The type of `path` is no longer a list of bits, but rather $\mathbb{Q}^n$.
I imagine this can be substituted for something else, but rational numbers is the most straightforward for reasoning about the algorithm.

When spawning new children, instead of appending a single L or R to the path,
append 1 and -1 respectively.
```
spawn(Vertex parent) {
    let left, right = new Vertex(), new Vertex()

    left.path = parent.path ++ 1
    right.path = parent.path ++ -1
    
    left.depth = parent.depth + 1
    right.depth = parent.depth + 1
}
```

When touching/joining two parents, 