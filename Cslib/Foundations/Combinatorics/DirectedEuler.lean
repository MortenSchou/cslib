/-
Copyright (c) 2026 Morten Schou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Morten Schou
-/

module

public import Cslib.Init
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Ring.Int
public import Mathlib.Data.Fintype.Basic

/-! # Walks and Euler's lemma in directed multigraphs

A directed multigraph is given by a type `E` of edges, a type `V` of vertices and two maps
`src tgt : E → V`. Walks are lists of edges. Mathlib has Eulerian trails only for simple graphs
(`SimpleGraph.Walk.IsEulerian`) and its quivers have dependently typed paths with no notion of the
multiplicity of an edge, so the directed Euler lemma is proved here.

## Main definitions

* `IsWalk`: `IsWalk src tgt a l b` iff the list of edges `l` is a walk from `a` to `b`.
* `flowCoeff`: the coefficient `[src e = z] - [tgt e = z]` of flow conservation at `z`.

## Main results

* `IsWalk.sum_flowCoeff_mul_count`: the net flow of a walk at `z` is `[z = a] - [z = b]`.
* `exists_closed_walk_count_eq`: the **directed Euler lemma**. In a finite multigraph whose vertices
  are strongly connected, every strictly positive balanced multiplicity function is the edge count
  of a closed walk.
-/

@[expose] public section

namespace Cslib.DiMultigraph

variable {V E : Type*}

/-- `IsWalk src tgt a l b`: the list of edges `l` is a walk from `a` to `b` in the directed
multigraph with sources `src` and targets `tgt`. -/
inductive IsWalk (src tgt : E → V) : V → List E → V → Prop
  | nil (a : V) : IsWalk src tgt a [] a
  | cons (e : E) {l : List E} {b : V} :
    IsWalk src tgt (tgt e) l b → IsWalk src tgt (src e) (e :: l) b

section Walk

variable {src tgt : E → V} {a b c : V} {p q : List E}

namespace IsWalk

/-- Inversion of `IsWalk.cons`. -/
theorem cons_iff {e : E} {l : List E} :
    IsWalk src tgt a (e :: l) b ↔ a = src e ∧ IsWalk src tgt (tgt e) l b := by
  refine ⟨fun h => ?_, fun ⟨h, h'⟩ => h ▸ .cons e h'⟩
  cases h with
  | cons _ h => exact ⟨rfl, h⟩

/-- Concatenation of walks. -/
theorem append (hp : IsWalk src tgt a p b) (hq : IsWalk src tgt b q c) :
    IsWalk src tgt a (p ++ q) c := by
  induction hp with
  | nil => exact hq
  | cons e _ ih => exact .cons e (ih hq)

/-- A walk along a concatenation splits at an intermediate vertex. -/
theorem append_iff :
    IsWalk src tgt a (p ++ q) c ↔ ∃ b, IsWalk src tgt a p b ∧ IsWalk src tgt b q c := by
  refine ⟨fun h => ?_, fun ⟨b, hp, hq⟩ => hp.append hq⟩
  induction p generalizing a with
  | nil => exact ⟨a, .nil a, h⟩
  | cons e p ih =>
    obtain ⟨rfl, h'⟩ := cons_iff.1 h
    obtain ⟨b, hp, hq⟩ := ih h'
    exact ⟨b, .cons e hp, hq⟩

/-- A walk from `a` to `b` is empty, or ends with an edge into `b`. -/
theorem eq_or_exists_tgt (hp : IsWalk src tgt a p b) : a = b ∨ ∃ e ∈ p, tgt e = b := by
  induction hp with
  | nil => exact .inl rfl
  | cons e _ ih =>
    rcases ih with rfl | ⟨e', he', h⟩
    · exact .inr ⟨e, by simp, rfl⟩
    · exact .inr ⟨e', by simp [he'], h⟩

/-- A walk from inside to outside of a set of vertices contains an edge leaving the set. -/
theorem exists_exit (hp : IsWalk src tgt a p b) {P : V → Prop} (ha : P a) (hb : ¬ P b) :
    ∃ e ∈ p, P (src e) ∧ ¬ P (tgt e) := by
  induction hp with
  | nil => exact absurd ha hb
  | cons e _ ih =>
    by_cases h : P (tgt e)
    · obtain ⟨e', he', h'⟩ := ih h hb
      exact ⟨e', by simp [he'], h'⟩
    · exact ⟨e, by simp, ha, h⟩

/-- Rotating a closed walk so that it starts and ends at the target of one of its edges. -/
theorem exists_rotate (hp : IsWalk src tgt a p a) {e : E} (he : e ∈ p) :
    ∃ q, IsWalk src tgt (tgt e) q (tgt e) ∧ q.Perm p := by
  obtain ⟨A, B, rfl⟩ := List.append_of_mem he
  obtain ⟨u, hA, hB⟩ := append_iff.1 hp
  obtain ⟨rfl, hB'⟩ := cons_iff.1 hB
  classical
  refine ⟨B ++ (A ++ [e]), hB'.append (hA.append (.cons e (.nil _))), ?_⟩
  rw [List.perm_iff_count]
  intro x
  simp only [List.count_append, List.count_cons, List.count_nil]
  omega

end IsWalk

end Walk

open Classical in
/-- The coefficient of flow conservation at `z`: `+1` for an edge leaving `z`, `-1` for an edge
entering `z`, and `0` for loops and for edges not incident to `z`. -/
noncomputable def flowCoeff (src tgt : E → V) (z : V) (e : E) : ℤ :=
  (if src e = z then 1 else 0) - (if tgt e = z then 1 else 0)

section Euler

variable [Fintype E] [DecidableEq E] {src tgt : E → V} {a b : V} {p : List E}

/-- The net flow of a walk from `a` to `b` at `z`. -/
theorem IsWalk.sum_flowCoeff_mul_count [DecidableEq V] (h : IsWalk src tgt a p b) (z : V) :
    ∑ e, flowCoeff src tgt z e * (p.count e : ℤ) =
      (if z = a then 1 else 0) - (if z = b then 1 else 0) := by
  induction h with
  | nil => simp
  | cons e _ ih =>
    simp only [List.count_cons, Nat.cast_add, mul_add, Finset.sum_add_distrib, ih,
      beq_iff_eq]
    simp [flowCoeff, eq_comm]

/-- The length of a list is the sum of the multiplicities of its entries. -/
theorem length_eq_sum_count (p : List E) : p.length = ∑ e, p.count e := by
  induction p with
  | nil => simp
  | cons e p ih => simp [List.count_cons, Finset.sum_add_distrib, ih]

/-- **Directed Euler lemma**: in a finite directed multigraph whose vertices in `S` are strongly
connected and contain all endpoints of edges, every strictly positive balanced multiplicity
function `g` is the edge count of a closed walk at any vertex of `S`. -/
theorem exists_closed_walk_count_eq {S : Set V} (hS : ∀ e, src e ∈ S ∧ tgt e ∈ S)
    (hsc : ∀ a ∈ S, ∀ b ∈ S, ∃ p, IsWalk src tgt a p b) {g : E → ℕ} (hpos : ∀ e, 0 < g e)
    (hbal : ∀ z, ∑ e, flowCoeff src tgt z e * (g e : ℤ) = 0) {s : V} (hs : s ∈ S) :
    ∃ p, IsWalk src tgt s p s ∧ ∀ e, p.count e = g e := by
  classical
  have len_le : ∀ p : List E, (∀ e, p.count e ≤ g e) → p.length ≤ ∑ e, g e := fun p hp => by
    rw [length_eq_sum_count]
    exact Finset.sum_le_sum fun e _ => hp e
  -- every trail extends to a closed walk using every edge `g e` times
  have key : ∀ n (u z : V) (p : List E), u ∈ S → IsWalk src tgt u p z → (∀ e, p.count e ≤ g e) →
      ∑ e, g e - p.length = n → ∃ (u : V) (p : List E), IsWalk src tgt u p u ∧
        ∀ e, p.count e = g e := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
    intro u z p hu hp hle hn
    -- extending a trail by an edge with a residual multiplicity
    have ext : ∀ w ∈ S, ∀ (q : List E) (e : E), IsWalk src tgt w q (src e) → q.Perm p →
        p.count e < g e → ∃ (u : V) (p : List E), IsWalk src tgt u p u ∧ ∀ e, p.count e = g e := by
      intro w hw q e hq hqp he
      have hc := hqp.count_eq
      have hl := hqp.length_eq
      have hle' : ∀ x, (q ++ [e]).count x ≤ g x := by
        intro x
        by_cases hx : e = x <;> grind [List.count_singleton]
      have hlen := len_le _ hle'
      simp only [List.length_append, List.length_singleton] at hlen
      exact ih _ (by simp only [List.length_append, List.length_singleton]; omega) w (tgt e)
        (q ++ [e]) hw (hq.append (.cons e (.nil _))) hle' rfl
    by_cases hzu : z = u
    · subst hzu
      by_cases htot : ∀ e, p.count e = g e
      · exact ⟨z, p, hp, htot⟩
      -- some edge is not yet used `g e` times: find one starting on the walk
      push Not at htot
      obtain ⟨t₀, ht₀⟩ := htot
      let W : V → Prop := fun v => v = z ∨ ∃ e ∈ p, tgt e = v
      obtain ⟨e, hW, he⟩ : ∃ e, W (src e) ∧ p.count e < g e := by
        by_cases h : W (src t₀)
        · exact ⟨t₀, h, lt_of_le_of_ne (hle t₀) ht₀⟩
        obtain ⟨r, hr⟩ := hsc z hu _ (hS t₀).1
        obtain ⟨e, he, hsrc, htgt⟩ := hr.exists_exit (P := W) (Or.inl rfl) h
        refine ⟨e, hsrc, ?_⟩
        rw [List.count_eq_zero.2 fun hep => htgt (Or.inr ⟨e, hep, rfl⟩)]
        exact hpos e
      rcases hW with hW | ⟨e', he', hW⟩
      · exact ext z hu p e (hW ▸ hp) (List.Perm.refl p) he
      · obtain ⟨q, hq, hqp⟩ := hp.exists_rotate he'
        exact ext (tgt e') (hW ▸ (hS e').2) q e (hW ▸ hq) hqp he
    · -- the trail is open: flow conservation leaves a residual edge at its end
      have hsum : ∑ e, flowCoeff src tgt z e * ((g e : ℤ) - p.count e) = 1 := by
        simp only [mul_sub, Finset.sum_sub_distrib, hbal, hp.sum_flowCoeff_mul_count]
        simp [hzu]
      obtain ⟨e, -, he⟩ := Finset.exists_lt_of_sum_lt (s := Finset.univ) (f := fun _ => (0 : ℤ))
        (g := fun e => flowCoeff src tgt z e * ((g e : ℤ) - p.count e)) (by simp [hsum])
      have := hle e
      unfold flowCoeff at he
      split_ifs at he <;> try omega
      exact ext u hu p e (by simp_all) (List.Perm.refl p) (by omega)
  -- rotate the closed walk to the vertex `s`
  obtain ⟨u, p, hp, hc⟩ := key _ s s [] hs (.nil s) (by simp) rfl
  rcases isEmpty_or_nonempty E with hE | ⟨⟨e₀⟩⟩
  · exact ⟨[], .nil s, fun e => isEmptyElim e⟩
  obtain ⟨r, hr⟩ := hsc _ (hS e₀).2 s hs
  obtain ⟨e₁, he₁⟩ : ∃ e₁, tgt e₁ = s := by
    rcases hr.eq_or_exists_tgt with h | ⟨e, -, h⟩
    exacts [⟨e₀, h⟩, ⟨e, h⟩]
  have hmem : e₁ ∈ p := List.count_pos_iff.1 (by rw [hc]; exact hpos e₁)
  obtain ⟨q, hq, hqp⟩ := hp.exists_rotate hmem
  exact ⟨q, he₁ ▸ hq, fun e => (hqp.count_eq e).trans (hc e)⟩

end Euler

end Cslib.DiMultigraph
