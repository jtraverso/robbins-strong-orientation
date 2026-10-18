/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib
public import RobbinsLib.Robbins

/-!
# Proofs of the statements in `Challenge.lean`

The theorems are proved in `RobbinsLib/` (namespace `Robbins`). Necessity: if an arc `a → b`
lay on a bridge, the strongly connected orientation would give a directed path from `b` back to
`a` avoiding the edge `ab`. Sufficiency (`RobbinsAux.lean`): a partial orientation is grown one
unoriented edge at a time while keeping the invariant that every oriented arc `a → b` has a
directed return path from `b` to `a`; an unoriented edge `uv` that is not a bridge lies on a path
from `v` to `u` avoiding it, and orienting `u → v` together with the unoriented edges of that
path (an ear step) preserves the invariant. When every edge is oriented, connectivity gives strong connectivity.
-/

@[expose] public section

open SimpleGraph

namespace StrongOrientation

/-- **Robbins' theorem (1939).** A finite connected graph has a strongly connected orientation if
and only if no edge of it is a bridge. -/
theorem robbins {V : Type*} [Finite V] (G : SimpleGraph V) (hG : G.Connected) :
    (∃ D : Digraph V, D.toSimpleGraphInclusive = G ∧ (∀ u v, D.Adj u v → ¬ D.Adj v u) ∧
        ∀ u v, Relation.ReflTransGen D.Adj u v) ↔
      ∀ e ∈ G.edgeSet, ¬ G.IsBridge e :=
  Robbins.robbins G hG

/-- Every finite `2`-edge-connected graph on a nonempty vertex type has a strongly connected
orientation. -/
theorem exists_strong_orientation_of_isEdgeConnected_two {V : Type*} [Finite V] [Nonempty V]
    (G : SimpleGraph V) (hG : G.IsEdgeConnected 2) :
    ∃ D : Digraph V, D.toSimpleGraphInclusive = G ∧ (∀ u v, D.Adj u v → ¬ D.Adj v u) ∧
      ∀ u v, Relation.ReflTransGen D.Adj u v :=
  Robbins.exists_strong_orientation_of_isEdgeConnected_two G hG

end StrongOrientation
