/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib

/-!
# Auxiliary results for Robbins' theorem

A *partial orientation* of `G` is a relation `D` on the vertices such that every arc is an edge
of `G`, no edge is oriented both ways, and every arc lies on a directed closed walk (`Inv`).
Starting from the empty relation, an unoriented edge `uv` that is not a bridge is oriented as
`u → v`, together with the still unoriented edges of a path from `v` to `u` avoiding `uv`
(the ear argument); the invariant is preserved (`extend`). Iterating, a bridgeless graph has a
partial orientation covering every edge (`exists_full`).
-/

@[expose] public section

open Finset SimpleGraph

namespace Robbins

variable {V : Type*} (G : SimpleGraph V)

/-- A partial orientation of `G` in which every arc lies on a directed closed walk. -/
structure Inv (D : V → V → Prop) : Prop where
  sub : ∀ a b, D a b → G.Adj a b
  anti : ∀ a b, D a b → ¬ D b a
  ret : ∀ a b, D a b → Relation.ReflTransGen D b a

variable {G}

lemma reach_of_oriented {D : V → V → Prop} (h : Inv G D) {x y : V} (hxy : D x y ∨ D y x) :
    Relation.ReflTransGen D x y := by
  rcases hxy with h1 | h1
  · exact Relation.ReflTransGen.single h1
  · exact h.ret _ _ h1

/-- Chaining reachability along the darts of a walk. -/
lemma reach_of_walk {H : SimpleGraph V} {D : V → V → Prop} :
    ∀ {a b : V} (p : H.Walk a b), (∀ d ∈ p.darts, Relation.ReflTransGen D d.fst d.snd) →
      Relation.ReflTransGen D a b
  | _, _, .nil, _ => Relation.ReflTransGen.refl
  | _, _, .cons h p, hd => by
      have h1 := hd ⟨(_, _), h⟩ (by simp)
      exact h1.trans (reach_of_walk p fun d hd' => hd d (by simp [hd']))

/-- Two darts of a path are never reverse to each other. -/
lemma not_rev_of_isPath {H : SimpleGraph V} {a b : V} {q : H.Walk a b} (hq : q.IsPath)
    {d₁ d₂ : H.Dart} (h₁ : d₁ ∈ q.darts) (h₂ : d₂ ∈ q.darts) (hf : d₁.fst = d₂.snd)
    (hs : d₁.snd = d₂.fst) : False := by
  have hsymm : d₂ = d₁.symm := by
    ext
    · exact hs.symm
    · exact hf.symm
  have hnd : (q.darts.map Dart.edge).Nodup := by
    rw [← Walk.edges_eq_map_darts]; exact hq.isTrail.edges_nodup
  have heq : d₁ = d₂ := List.inj_on_of_nodup_map hnd h₁ h₂ (by rw [hsymm, Dart.edge_symm])
  exact Dart.symm_ne d₁ (by rw [← hsymm, heq])

open Classical in
/-- **The ear step.** An unoriented edge `uv` that is not a bridge can be oriented, together with
the unoriented edges of a path from `v` to `u` avoiding `uv`, preserving the invariant. -/
lemma extend {D : V → V → Prop} (hI : Inv G D) {u v : V} (huv : G.Adj u v) (hnu : ¬ D u v)
    (hnv : ¬ D v u) (hnb : ¬ G.IsBridge s(u, v)) :
    ∃ D' : V → V → Prop, Inv G D' ∧ (∀ a b, D a b → D' a b) ∧ D' u v := by
  set H := G.deleteEdges {s(u, v)} with hH
  have hreach : H.Reachable u v := by
    by_contra h
    exact hnb (isBridge_iff.mpr h)
  obtain ⟨q, hq⟩ := (Classical.choice hreach.symm).toPath
  -- the darts of the path
  have hdart : ∀ d ∈ q.darts, G.Adj d.fst d.snd ∧ s(d.fst, d.snd) ≠ s(u, v) := by
    intro d _
    have h : G.Adj d.fst d.snd ∧ s(d.fst, d.snd) ∉ ({s(u, v)} : Set (Sym2 V)) :=
      deleteEdges_adj.mp d.adj
    exact ⟨h.1, by simpa using h.2⟩
  let N : V → V → Prop := fun a b => ∃ d ∈ q.darts, d.fst = a ∧ d.snd = b
  let D' : V → V → Prop := fun a b =>
    D a b ∨ (a = u ∧ b = v) ∨ (N a b ∧ ¬ D a b ∧ ¬ D b a)
  have hND : ∀ a b, N a b → G.Adj a b ∧ s(a, b) ≠ s(u, v) := by
    rintro a b ⟨d, hd, rfl, rfl⟩
    exact hdart d hd
  have hNuv : ¬ N v u := by
    intro h
    exact (hND v u h).2 Sym2.eq_swap
  have hmono : ∀ a b, D a b → D' a b := fun a b h => Or.inl h
  -- every dart of the path is traversable in `D'`
  have hdartR : ∀ d ∈ q.darts, Relation.ReflTransGen D' d.fst d.snd := by
    intro d hd
    by_cases h1 : D d.fst d.snd
    · exact Relation.ReflTransGen.single (Or.inl h1)
    by_cases h2 : D d.snd d.fst
    · exact Relation.ReflTransGen.mono hmono _ _ (hI.ret _ _ h2)
    · exact Relation.ReflTransGen.single (Or.inr (Or.inr ⟨⟨d, hd, rfl, rfl⟩, h1, h2⟩))
  have hvu : Relation.ReflTransGen D' v u := reach_of_walk q hdartR
  have hvx : ∀ x ∈ q.support, Relation.ReflTransGen D' v x := fun x hx =>
    reach_of_walk (q.takeUntil x hx) fun d hd =>
      hdartR d (Walk.darts_takeUntil_subset_darts q hx hd)
  have hxu : ∀ x ∈ q.support, Relation.ReflTransGen D' x u := fun x hx =>
    reach_of_walk (q.dropUntil x hx) fun d hd =>
      hdartR d (Walk.darts_dropUntil_subset_darts q hx hd)
  refine ⟨D', ⟨?_, ?_, ?_⟩, hmono, Or.inr (Or.inl ⟨rfl, rfl⟩)⟩
  · rintro a b (h | ⟨rfl, rfl⟩ | ⟨h, -, -⟩)
    · exact hI.sub _ _ h
    · exact huv
    · exact (hND a b h).1
  · intro a b h h'
    rcases h with h | ⟨ha, hb⟩ | ⟨h, h1, h2⟩ <;>
      rcases h' with h' | ⟨ha', hb'⟩ | ⟨h', h1', h2'⟩
    · exact hI.anti _ _ h h'
    · subst ha' hb'; exact hnv h
    · exact h2' h
    · subst ha hb; exact hnv h'
    · subst ha hb; exact G.ne_of_adj huv ha'.symm
    · subst ha hb; exact hNuv h'
    · exact h2 h'
    · subst ha' hb'; exact hNuv h
    · obtain ⟨d₁, hd₁, hf₁, hs₁⟩ := h
      obtain ⟨d₂, hd₂, hf₂, hs₂⟩ := h'
      exact not_rev_of_isPath hq hd₁ hd₂ (hf₁.trans hs₂.symm) (hs₁.trans hf₂.symm)
  · rintro a b (h | ⟨rfl, rfl⟩ | ⟨h, -, -⟩)
    · exact Relation.ReflTransGen.mono hmono _ _ (hI.ret _ _ h)
    · exact hvu
    · obtain ⟨d, hd, rfl, rfl⟩ := h
      have ha := Walk.dart_fst_mem_support_of_mem_darts q hd
      have hb := Walk.dart_snd_mem_support_of_mem_darts q hd
      exact ((hxu _ hb).tail (Or.inr (Or.inl ⟨rfl, rfl⟩))).trans (hvx _ ha)

open Classical in
/-- A finite bridgeless graph has a partial orientation, with every arc on a directed closed walk,
that orients every edge. -/
lemma exists_full [Finite V] (hb : ∀ e ∈ G.edgeSet, ¬ G.IsBridge e) :
    ∃ D : V → V → Prop, Inv G D ∧ ∀ a b, G.Adj a b → D a b ∨ D b a := by
  have := Fintype.ofFinite V
  let cnt : (V → V → Prop) → ℕ := fun D =>
    #{p : V × V | G.Adj p.1 p.2 ∧ ¬ D p.1 p.2 ∧ ¬ D p.2 p.1}
  suffices key : ∀ n, ∀ D : V → V → Prop, Inv G D → cnt D = n →
      ∃ D : V → V → Prop, Inv G D ∧ ∀ a b, G.Adj a b → D a b ∨ D b a by
    refine key _ (fun _ _ => False) ⟨fun _ _ h => h.elim, fun _ _ h => h.elim,
      fun _ _ h => h.elim⟩ rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro D hI hn
    by_cases hfull : ∀ a b, G.Adj a b → D a b ∨ D b a
    · exact ⟨D, hI, hfull⟩
    push Not at hfull
    obtain ⟨u, v, huv, hnu, hnv⟩ := hfull
    obtain ⟨D', hI', hmono, hD'⟩ := extend hI huv hnu hnv (hb _ huv)
    refine ih (cnt D') ?_ D' hI' rfl
    rw [← hn]
    apply Finset.card_lt_card
    rw [Finset.ssubset_iff_of_subset]
    · refine ⟨(u, v), ?_, ?_⟩
      · simp [huv, hnu, hnv]
      · simp [hD']
    · intro p hp
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
      exact ⟨hp.1, fun h => hp.2.1 (hmono _ _ h), fun h => hp.2.2 (hmono _ _ h)⟩

end Robbins
