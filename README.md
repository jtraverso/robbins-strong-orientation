# Robbins' theorem on strongly connected orientations in Lean 4

Author and maintainer: **Juan Pablo Traverso Gianini**. Licence: Apache-2.0 (see `LICENSE`).

An *orientation* of a simple graph `G` is a digraph `D` (Mathlib's `Digraph`) whose underlying
undirected graph (`Digraph.toSimpleGraphInclusive`) is `G` and which never contains both arcs
`u → v` and `v → u`. It is *strongly connected* if every vertex reaches every other vertex along
arcs (`Relation.ReflTransGen D.Adj`). All statements are in the namespace `StrongOrientation`:

1. `robbins`, **Robbins' theorem (1939)**. A finite connected graph has a strongly connected
   orientation if and only if no edge of it is a bridge (Mathlib's `SimpleGraph.IsBridge`).
2. `exists_strong_orientation_of_isEdgeConnected_two`. Every finite 2-edge-connected graph
   (Mathlib's `SimpleGraph.IsEdgeConnected 2`) on a nonempty vertex type has a strongly connected
   orientation.

Mathlib has bridges, edge connectivity and digraphs, but not this theorem.

## Files

- [`Challenge.lean`](Challenge.lean): the audited statements. It imports only Mathlib.
- [`Solution.lean`](Solution.lean) and [`RobbinsLib/`](RobbinsLib): the proofs.
- [`comparator.json`](comparator.json): the theorems that are compared.
- [`MATHLIB_DEFINITIONS.md`](MATHLIB_DEFINITIONS.md): verbatim copies of the Mathlib definitions
  used.
- [`formalization.yaml`](formalization.yaml): provenance, sources and process.

## How the proof goes

* **Necessity.** If an arc `a → b` of a strongly connected orientation lay on a bridge, the
  directed path from `b` back to `a` would connect `b` to `a` without using the edge `ab`.
* **Sufficiency.** A partial orientation is grown while keeping the invariant that every oriented
  arc `a → b` has a directed path back from `b` to `a`. If an edge `uv` is still unoriented and is
  not a bridge, there is a path from `v` to `u` avoiding it; orienting `u → v` together with the
  unoriented edges of that path (an *ear*) preserves the invariant. By induction on the number of
  unoriented edges every edge gets oriented, and then connectivity of `G` gives strong
  connectivity.

## Sources

* H. E. Robbins, *A theorem on graphs, with an application to a problem of traffic control*, Amer.
  Math. Monthly 46 (1939) 281–283, doi:10.2307/2303897.

## Authorship and use of AI

The author chose the result. The statements, the proof plan and the Lean proofs were written with
Claude in Claude Code (the statement was first checked by brute force on all graphs with six
vertices). Lean checks everything mechanically. See `formalization.yaml`.

## Building

Lean `v4.35.0-rc3`, Mathlib `c55e6e786f49471c72fbddbec5415808896aec1e`:

```bash
lake exe cache get
lake build
```
