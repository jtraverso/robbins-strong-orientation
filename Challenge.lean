/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib

/-!
# Robbins' theorem: strongly connected orientations

An *orientation* of a simple graph `G` is a digraph `D` (Mathlib's `Digraph`) whose underlying
undirected graph (`Digraph.toSimpleGraphInclusive`) is `G` and which never contains both arcs
`u → v` and `v → u`. It is *strongly connected* if every vertex can reach every other vertex along
arcs (`Relation.ReflTransGen D.Adj`).

* `StrongOrientation.robbins`: **Robbins (1939).** A finite connected graph has a strongly connected
  orientation if and only if it has no bridge (Mathlib's `SimpleGraph.IsBridge`, restricted to
  edges of `G`).
* `StrongOrientation.exists_strong_orientation_of_isEdgeConnected_two`: every finite `2`-edge-connected
  graph (Mathlib's `SimpleGraph.IsEdgeConnected`) on a nonempty vertex type has a strongly connected
  orientation.

The Mathlib definitions used in these statements are reproduced verbatim, with file and line at the
pinned Mathlib revision, in `MATHLIB_DEFINITIONS.md` at the root of this repository.
-/

@[expose] public section

open SimpleGraph

namespace StrongOrientation

/-- **Robbins' theorem (1939).** A finite connected graph has a strongly connected orientation if
and only if no edge of it is a bridge. -/
theorem robbins {V : Type*} [Finite V] (G : SimpleGraph V) (hG : G.Connected) :
    (∃ D : Digraph V, D.toSimpleGraphInclusive = G ∧ (∀ u v, D.Adj u v → ¬ D.Adj v u) ∧
        ∀ u v, Relation.ReflTransGen D.Adj u v) ↔
      ∀ e ∈ G.edgeSet, ¬ G.IsBridge e := by
  sorry

/-- Every finite `2`-edge-connected graph on a nonempty vertex type has a strongly connected
orientation. -/
theorem exists_strong_orientation_of_isEdgeConnected_two {V : Type*} [Finite V] [Nonempty V]
    (G : SimpleGraph V) (hG : G.IsEdgeConnected 2) :
    ∃ D : Digraph V, D.toSimpleGraphInclusive = G ∧ (∀ u v, D.Adj u v → ¬ D.Adj v u) ∧
      ∀ u v, Relation.ReflTransGen D.Adj u v := by
  sorry

end StrongOrientation
