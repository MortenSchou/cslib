/-
Copyright (c) 2026 Morten Schou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Morten Schou
-/

module

public import Cslib.Computability.VAS.Run
public import Cslib.Foundations.Combinatorics.DirectedEuler
public import Cslib.Foundations.Data.RatDefinable.FourierMotzkin
public import Mathlib.Algebra.BigOperators.Finprod

/-! # Production graphs and Kirchhoff functions

The graph-theoretic part of the block on transformer relations (Leroux, Section 5.3).

## Main definitions

* `ProdGraph`: a graph whose states and transitions are configurations and `(state, action, state)`
  triples. Its paths are the walks (`Cslib.DiMultigraph.IsWalk`) of the multigraph of its
  transitions.
* `ProdGraph.IsKirchhoff`, `ProdGraph.disp`: flow conservation and displacement of a function on
  the transitions.
* `ProdGraph.relR`: the relation `R(G; S_x, S_y)` defined through Kirchhoff functions.

## Main results

* `ProdGraph.euler_lemma`: on a finite strongly connected graph every strictly positive integer
  Kirchhoff function is the Parikh image of a total cycle (a directed Euler lemma, an instance of
  `Cslib.DiMultigraph.exists_closed_walk_count_eq`).
* `ProdGraph.relR_definable`: the relation `relR` of a finite graph is definable in `FO(ℚ; +, ≤)`.
-/

@[expose] public section

namespace Cslib

open DiMultigraph

variable {ι : Type*}

/-- The *production graph* data: a graph whose states are configurations and whose transitions
are `(s, a, s')` triples. -/
structure ProdGraph (ι : Type*) where
  /-- The states. -/
  states : Set (VASConfig ι)
  /-- The transitions `(source state, action, target state)`. -/
  trans : Set (VASConfig ι × (ι → ℤ) × VASConfig ι)

namespace ProdGraph

/-- A transition of a production graph: a source state, an action and a target state. -/
abbrev Edge (ι : Type*) := VASConfig ι × (ι → ℤ) × VASConfig ι

variable (G : ProdGraph ι)

/-- The source state of a transition. -/
abbrev src (t : G.trans) : VASConfig ι := t.1.1

/-- The target state of a transition. -/
abbrev tgt (t : G.trans) : VASConfig ι := t.1.2.2

/-- The action of a transition. -/
abbrev act (t : G.trans) : ι → ℤ := t.1.2.1

/-- Paths in a production graph, as words of transitions. -/
abbrev IsPath : VASConfig ι → List G.trans → VASConfig ι → Prop :=
  IsWalk G.src G.tgt

/-- A single transition is a path. -/
theorem isPath_single (t : G.trans) : G.IsPath (G.src t) [t] (G.tgt t) :=
  .cons t (.nil _)

/-- Strong connectivity: any two states are joined by a path. -/
def StronglyConnected : Prop := ∀ s ∈ G.states, ∀ s' ∈ G.states, ∃ p, G.IsPath s p s'

/-- Every transition goes between states. -/
def WellFormed : Prop := ∀ t ∈ G.trans, t.1 ∈ G.states ∧ t.2.2 ∈ G.states

/-- A Kirchhoff function: flow conservation at every vertex (for a well-formed graph this is the
same as conservation at every state). -/
def IsKirchhoff (f : G.trans → ℚ) : Prop :=
  ∀ s, ∑ᶠ t, (flowCoeff G.src G.tgt s t : ℚ) * f t = 0

/-- The displacement `δ(f) = ∑ f(t) · a_t` of a function on transitions (a junk value unless the
graph has finitely many transitions). -/
noncomputable def disp (f : G.trans → ℚ) : ι → ℚ := fun i => ∑ᶠ t, f t * (G.act t i : ℚ)

/-- The Parikh image of a word of transitions: the number of occurrences of each transition. -/
def parikh [DecidableEq G.trans] (p : List G.trans) : G.trans → ℕ := fun t => p.count t

/-- The relation `R(G; S_x, S_y) ⊆ ℚ≥0^ι × ℚ≥0^ι` attached to a graph and two supports: both
components are non-negative with supports exactly `S_x`, `S_y`, and `v - u = δ(f)` for a strictly
positive Kirchhoff function `f` of `G`. -/
def relR (Sx Sy : Set ι) : Set (ι ⊕ ι → ℚ) :=
  {w | (∀ i, 0 ≤ w (Sum.inl i) ∧ 0 ≤ w (Sum.inr i)) ∧
    (∀ i, 0 < w (Sum.inl i) ↔ i ∈ Sx) ∧ (∀ i, 0 < w (Sum.inr i) ↔ i ∈ Sy) ∧
    ∃ f : G.trans → ℚ, (∀ t, 0 < f t) ∧ G.IsKirchhoff f ∧
      (fun i => w (Sum.inr i) - w (Sum.inl i)) = G.disp f}

variable {G}

section Finite

variable [Fintype G.trans]

/-- Flow conservation as a finite sum. -/
theorem isKirchhoff_iff {f : G.trans → ℚ} :
    G.IsKirchhoff f ↔ ∀ s, ∑ t, (flowCoeff G.src G.tgt s t : ℚ) * f t = 0 := by
  simp only [IsKirchhoff, finsum_eq_sum_of_fintype]

/-- The displacement as a finite sum. -/
theorem disp_apply (f : G.trans → ℚ) (i : ι) : G.disp f i = ∑ t, f t * (G.act t i : ℚ) :=
  finsum_eq_sum_of_fintype _

end Finite

section Linear

variable [Finite G.trans]

/-- Kirchhoff functions are closed under subtraction. -/
theorem IsKirchhoff.sub {f g : G.trans → ℚ} (hf : G.IsKirchhoff f) (hg : G.IsKirchhoff g) :
    G.IsKirchhoff (f - g) := by
  have := Fintype.ofFinite G.trans
  simp only [isKirchhoff_iff, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib] at *
  intro s
  rw [hf s, hg s, sub_zero]

/-- Kirchhoff functions are closed under scaling. -/
theorem IsKirchhoff.smul {f : G.trans → ℚ} (hf : G.IsKirchhoff f) (a : ℚ) :
    G.IsKirchhoff (a • f) := by
  have := Fintype.ofFinite G.trans
  simp only [isKirchhoff_iff, Pi.smul_apply, smul_eq_mul, mul_left_comm _ a,
    ← Finset.mul_sum] at *
  intro s
  rw [hf s, mul_zero]

/-- The displacement is compatible with subtraction. -/
theorem disp_sub (f g : G.trans → ℚ) : G.disp (f - g) = G.disp f - G.disp g := by
  have := Fintype.ofFinite G.trans
  ext i
  simp only [disp_apply, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

/-- The displacement is homogeneous. -/
theorem disp_smul (a : ℚ) (f : G.trans → ℚ) : G.disp (a • f) = a • G.disp f := by
  have := Fintype.ofFinite G.trans
  ext i
  simp only [disp_apply, Pi.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum]

/-- `relR` is stable under positive scaling. -/
theorem relR_smul {Sx Sy : Set ι} {w : ι ⊕ ι → ℚ} (hw : w ∈ G.relR Sx Sy) {q : ℚ} (hq : 0 < q) :
    q • w ∈ G.relR Sx Sy := by
  obtain ⟨hnn, hsx, hsy, f, hfpos, hK, hdisp⟩ := hw
  refine ⟨fun i => ⟨mul_nonneg hq.le (hnn i).1, mul_nonneg hq.le (hnn i).2⟩, fun i => ?_,
    fun i => ?_, q • f, fun t => mul_pos hq (hfpos t), hK.smul q, ?_⟩
  · simpa [hq] using hsx i
  · simpa [hq] using hsy i
  · rw [disp_smul, ← hdisp]
    ext i
    simp [mul_sub]

end Linear

section Paths

variable [Finite G.trans] {s : VASConfig ι} {p : List G.trans}

/-- The displacement of the Parikh image of a path is the sum of its labels. -/
theorem disp_parikh [DecidableEq G.trans] (p : List G.trans) (i : ι) :
    G.disp (fun t => (G.parikh p t : ℚ)) i = (((p.map G.act).sum i : ℤ) : ℚ) := by
  have := Fintype.ofFinite G.trans
  induction p with
  | nil => simp [disp_apply, parikh]
  | cons t p ih =>
    simp only [disp_apply, parikh, List.count_cons, beq_iff_eq] at ih ⊢
    simp [add_mul, Finset.sum_add_distrib, ih, add_comm]

/-- The Parikh image of a closed path is a Kirchhoff function. -/
theorem IsPath.isKirchhoff_parikh [DecidableEq G.trans] (h : G.IsPath s p s) :
    G.IsKirchhoff fun t => (G.parikh p t : ℚ) := by
  have := Fintype.ofFinite G.trans
  classical
  refine isKirchhoff_iff.2 fun z => ?_
  have h' := congrArg ((↑) : ℤ → ℚ) (h.sum_flowCoeff_mul_count z)
  simpa [parikh] using h'

/-- **Euler's lemma** (directed version): on a finite strongly connected graph whose transitions
go between states, every strictly positive integer Kirchhoff function is the Parikh image of a
total cycle on any given state. -/
theorem euler_lemma [DecidableEq G.trans] (hwf : G.WellFormed) (hsc : G.StronglyConnected)
    (f : G.trans → ℕ) (hpos : ∀ t, 0 < f t) (hK : G.IsKirchhoff fun t => (f t : ℚ))
    (hs : s ∈ G.states) : ∃ p, G.IsPath s p s ∧ G.parikh p = f := by
  classical
  have := Fintype.ofFinite G.trans
  obtain ⟨p, hp, hc⟩ := exists_closed_walk_count_eq (src := G.src) (tgt := G.tgt)
    (S := G.states) (fun t => hwf t.1 t.2) hsc hpos
    (fun z => by exact_mod_cast isKirchhoff_iff.1 hK z) hs
  exact ⟨p, hp, funext hc⟩

end Paths

end ProdGraph

namespace ProdGraph

open RatDefinable

variable {G : ProdGraph ι}

/-- Flow conservation only needs checking at the endpoints of transitions. -/
theorem isKirchhoff_iff_vtx [Fintype G.trans] {f : G.trans → ℚ} :
    G.IsKirchhoff f ↔ ∀ j : G.trans ⊕ G.trans,
      ∑ t, (flowCoeff G.src G.tgt (Sum.elim G.src G.tgt j) t : ℚ) * f t = 0 := by
  rw [isKirchhoff_iff]
  refine ⟨fun h j => h _, fun h s => ?_⟩
  by_cases hs : ∃ t, G.src t = s ∨ G.tgt t = s
  · obtain ⟨t, ht | ht⟩ := hs
    · simpa [ht] using h (Sum.inl t)
    · simpa [ht] using h (Sum.inr t)
  · push Not at hs
    refine Finset.sum_eq_zero fun t _ => ?_
    simp [flowCoeff, (hs t).1, (hs t).2]

/-- `relR` of a finite graph is definable in `FO(ℚ; +, ≤, 0)`: it is the projection (onto the
coordinates `w`) of the conjunction of finitely many linear constraints on `(w, f)`. -/
theorem relR_definable [Fintype ι] [Finite G.trans] (Sx Sy : Set ι) :
    RatDefinable (G.relR Sx Sy) := by
  classical
  have := Fintype.ofFinite G.trans
  let C : Set ((ι ⊕ ι) ⊕ G.trans → ℚ) := {v | (∀ k, 0 ≤ v (Sum.inl k)) ∧
    (∀ i, 0 < v (Sum.inl (Sum.inl i)) ↔ i ∈ Sx) ∧ (∀ i, 0 < v (Sum.inl (Sum.inr i)) ↔ i ∈ Sy) ∧
    (∀ t, 0 < v (Sum.inr t)) ∧
    (∀ j : G.trans ⊕ G.trans, ∑ t, (flowCoeff G.src G.tgt (Sum.elim G.src G.tgt j) t : ℚ) *
      v (Sum.inr t) = 0) ∧
    (∀ i, v (Sum.inl (Sum.inr i)) - v (Sum.inl (Sum.inl i)) = ∑ t, v (Sum.inr t) * G.act t i)}
  have hC : RatDefinable C := by
    have hK : RatDefinable {v : (ι ⊕ ι) ⊕ G.trans → ℚ | ∀ j : G.trans ⊕ G.trans,
        ∑ t, (flowCoeff G.src G.tgt (Sum.elim G.src G.tgt j) t : ℚ) * v (Sum.inr t) = 0} :=
      forall_fintype fun j => by
        convert zero (Sum.elim (fun _ : ι ⊕ ι => (0 : ℤ))
          (fun t => flowCoeff G.src G.tgt (Sum.elim G.src G.tgt j) t)) using 1
        ext v
        simp [Fintype.sum_sum_type]
    have hD : RatDefinable {v : (ι ⊕ ι) ⊕ G.trans → ℚ | ∀ i : ι,
        v (Sum.inl (Sum.inr i)) - v (Sum.inl (Sum.inl i)) = ∑ t, v (Sum.inr t) * G.act t i} :=
      forall_fintype fun i => by
        convert zero (Sum.elim (fun k : ι ⊕ ι => (if k = Sum.inr i then 1 else 0) -
          (if k = Sum.inl i then 1 else 0)) (fun t => - G.act t i)) using 1
        ext v
        simp only [Set.mem_ofPred_eq, Fintype.sum_sum_type]
        simp only [mul_comm, Sum.elim_inl, reduceCtorEq, ↓reduceIte, Sum.inl.injEq, zero_sub,
          Int.cast_neg, Int.cast_ite, Int.cast_one, Int.cast_zero, neg_mul, ite_mul, one_mul,
          zero_mul, Finset.sum_neg_distrib, Finset.sum_ite_eq', Finset.mem_univ, Sum.inr.injEq,
          sub_zero, Sum.elim_inr]
        constructor <;> intro h <;> linarith
    exact (forall_fintype fun k => coord_nonneg (Sum.inl k)).inter
      ((forall_fintype fun i => coord_pos_iff (Sum.inl (Sum.inl i)) (i ∈ Sx)).inter
      ((forall_fintype fun i => coord_pos_iff (Sum.inl (Sum.inr i)) (i ∈ Sy)).inter
      ((forall_fintype fun t => coord_pos (Sum.inr t)).inter (hK.inter hD))))
  have := hC.proj (κ := ι ⊕ ι) (κ' := G.trans)
  convert this using 1
  ext w
  simp only [relR, C, Set.mem_ofPred_eq, Sum.forall, Sum.elim_inl, Sum.elim_inr]
  constructor
  · rintro ⟨hnn, hsx, hsy, f, hf, hK, hd⟩
    refine ⟨f, ⟨fun a => (hnn a).1, fun b => (hnn b).2⟩, hsx, hsy, hf, ?_, fun i => ?_⟩
    · simpa [Sum.forall] using isKirchhoff_iff_vtx.1 hK
    · rw [← disp_apply, ← congrFun hd i]
  · rintro ⟨f, ⟨h1, h2⟩, hsx, hsy, hf, hK, hd⟩
    refine ⟨fun i => ⟨h1 i, h2 i⟩, hsx, hsy, f, hf, isKirchhoff_iff_vtx.2 ?_, funext fun i => ?_⟩
    · simpa [Sum.forall] using hK
    · rw [disp_apply]
      exact hd i

end ProdGraph

end Cslib
