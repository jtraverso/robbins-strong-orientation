/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib
public import RobbinsLib.RobbinsAux

/-!
# Robbins' theorem: strongly connected orientations

An *orientation* of a simple graph `G` is a digraph `D` (Mathlib's `Digraph`) whose underlying
undirected graph (`Digraph.toSimpleGraphInclusive`) is `G` and which never contains both arcs
`u → v` and `v → u`. It is *strongly connected* if every vertex can reach every other vertex along
arcs (`Relation.ReflTransGen D.Adj`).

* `Robbins.robbins`: **Robbins (1939).** A finite connected graph has a strongly connected
  orientation if and only if it has no bridge (Mathlib's `SimpleGraph.IsBridge`, restricted to
  edges of `G`).
* `Robbins.exists_strong_orientation_of_isEdgeConnected_two`: every finite `2`-edge-connected
  graph (Mathlib's `SimpleGraph.IsEdgeConnected`) on a nonempty vertex type has a strongly connected
  orientation.
-/

@[expose] public section

open SimpleGraph

namespace Robbins

/-- **Robbins' theorem (1939).** A finite connected graph has a strongly connected orientation if
and only if no edge of it is a bridge. -/
theorem robbins {V : Type*} [Finite V] (G : SimpleGraph V) (hG : G.Connected) :
    (∃ D : Digraph V, D.toSimpleGraphInclusive = G ∧ (∀ u v, D.Adj u v → ¬ D.Adj v u) ∧
        ∀ u v, Relation.ReflTransGen D.Adj u v) ↔
      ∀ e ∈ G.edgeSet, ¬ G.IsBridge e := by
  constructor
  · rintro ⟨Dg, hDg, hanti, hstrong⟩ e he
    induction e using Sym2.ind with
    | _ u v =>
      have hadj : ∀ x y, Dg.Adj x y → G.Adj x y := by
        intro x y h
        rw [← hDg]
        simp only [Digraph.toSimpleGraphInclusive, fromRel_adj]
        exact ⟨fun hxy => hanti x y h (hxy ▸ h), Or.inl h⟩
      have huvG : G.Adj u v := he
      have hor : Dg.Adj u v ∨ Dg.Adj v u := by
        rw [← hDg] at huvG
        simp only [Digraph.toSimpleGraphInclusive, fromRel_adj] at huvG
        exact huvG.2
      -- reduce to an arc `a → b` with `s(a, b) = s(u, v)`
      suffices key : ∀ a b, Dg.Adj a b → ¬ G.IsBridge s(a, b) by
        rcases hor with h | h
        · exact key u v h
        · rw [Sym2.eq_swap]; exact key v u h
      intro a b hab
      rw [isBridge_iff, not_not]
      set H := G.deleteEdges {s(a, b)}
      have hback : ∀ x, Relation.ReflTransGen Dg.Adj x a → H.Reachable x a := by
        intro x hx
        induction hx using Relation.ReflTransGen.head_induction_on with
        | refl => exact Reachable.refl _
        | @head x y hxy _ ih =>
          by_cases hxa : x = a
          · subst hxa; exact Reachable.refl _
          · have hHxy : H.Adj x y := by
              rw [deleteEdges_adj]
              refine ⟨hadj x y hxy, ?_⟩
              intro hmem
              rcases Sym2.eq_iff.1 (Set.mem_singleton_iff.1 hmem) with ⟨h1, -⟩ | ⟨h1, h2⟩
              · exact hxa h1
              · subst h1; subst h2; exact hanti _ _ hab hxy
            exact hHxy.reachable.trans ih
      exact (hback b (hstrong b a)).symm
  · intro hb
    obtain ⟨D, hI, hcov⟩ := Robbins.exists_full hb
    refine ⟨⟨D⟩, ?_, hI.anti, ?_⟩
    · ext a b
      simp only [Digraph.toSimpleGraphInclusive, fromRel_adj]
      constructor
      · rintro ⟨-, h | h⟩
        · exact hI.sub _ _ h
        · exact (hI.sub _ _ h).symm
      · intro h
        exact ⟨G.ne_of_adj h, hcov a b h⟩
    · intro a b
      obtain ⟨w⟩ := hG.preconnected a b
      exact reach_of_walk w fun d _ => reach_of_oriented hI (hcov _ _ d.adj)

/-- Every finite `2`-edge-connected graph on a nonempty vertex type has a strongly connected
orientation. -/
theorem exists_strong_orientation_of_isEdgeConnected_two {V : Type*} [Finite V] [Nonempty V]
    (G : SimpleGraph V) (hG : G.IsEdgeConnected 2) :
    ∃ D : Digraph V, D.toSimpleGraphInclusive = G ∧ (∀ u v, D.Adj u v → ¬ D.Adj v u) ∧
      ∀ u v, Relation.ReflTransGen D.Adj u v := by
  refine (robbins G (hG.connected (by norm_num))).2 ?_
  intro e he
  induction e using Sym2.ind with
  | _ u v =>
    rw [isBridge_iff_not_isEdgeReachable_two he, not_not]
    exact hG u v

end Robbins
