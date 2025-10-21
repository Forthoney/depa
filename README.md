# DePa on DAGs
A generalization of DePa to operate on DAGs as opposed to merely series-parallel graphs.
This presents the algorithmic description without regard for efficiency

## Key differences
The `path` is treated not as a list of bits, but rather as a **vector** of rational numbers: $\mathbb{Q}^n$.

Let $p \in \mathbb{Q}^n$ be the path of the spawning vertex.
Then the paths of the left and right children $l, r \in \mathbb{Q}^{n + 1}$ respectively, are 
```math
\forall i = 1, \dots, n: l_i = r_i = p_i / 2
```
```math
l_{n + 1} = 1
```
```math
r_{n + 1} = -1
```

When touching/joining two vertices, the path calculation is simply $c = l + r$ where $c$ is the path of the continuation.
