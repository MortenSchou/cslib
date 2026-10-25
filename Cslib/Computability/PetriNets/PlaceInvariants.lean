/-
Copyright (c) 2026 Morten Schou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Morten Schou
-/

module

public import Cslib.Computability.PetriNets.Semantics

/-! # Place invariants

A *place invariant* is a weighting of the places such that every transition consumes and produces
the same total weight. The weighted number of tokens is then constant along every firing sequence.
If every place has positive weight, this bounds the number of tokens in every place.

## Main definitions

- `PetriNet.Marking.weight`: the weighted token count of a marking.
- `PetriNet.IsInvariant`: a weighting preserved by every transition.

## Main statements

- `PetriNet.IsInvariant.weight_eq`: the weighted token count is constant on reachable markings.
- `PetriNet.IsInvariant.kBounded`: a positive invariant bounds every place.
- `PetriNet.conservative_iff_isInvariant`: conservative nets are those with weighting `1`.

## References

* [T. Murata, *Petri nets: Properties, analysis and applications*][Murata1989]
-/

@[expose] public section

namespace Cslib

namespace PetriNet

variable {Place : Type*} {Transition : Type*}

/-- The weighted number of tokens of a marking, for a weighting `w` of the places: the sum of the
weights of its tokens. -/
def Marking.weight (w : Place → ℕ) : Marking Place →+ ℕ :=
  Multiset.sumAddMonoidHom.comp (Multiset.mapAddMonoidHom w)

theorem Marking.weight_apply (w : Place → ℕ) (M : Marking Place) :
    Marking.weight w M = (M.map w).sum :=
  rfl

@[simp] theorem Marking.weight_one (M : Marking Place) :
    Marking.weight (fun _ => 1) M = M.card := by
  simp [Marking.weight_apply]

/-- A weighting of the places is an invariant if every transition consumes and produces the same
total weight. -/
def IsInvariant (N : PetriNet Place Transition) (w : Place → ℕ) : Prop :=
  ∀ t, Marking.weight w (•[N] t) = Marking.weight w (t •[N])

variable {N : PetriNet Place Transition} {w : Place → ℕ}

/-- Firing preserves the weighted token count of an invariant. -/
theorem IsInvariant.weight_fires (hw : N.IsInvariant w) {M M' : Marking Place} {t : Transition}
    (h : M [t⟩[N] M') : Marking.weight w M' = Marking.weight w M := by
  obtain ⟨R, rfl, rfl⟩ := h
  have := hw t
  simp only [map_add]
  omega

/-- The weighted token count of an invariant is constant on reachable markings. -/
theorem IsInvariant.weight_eq (hw : N.IsInvariant w) {M M' : Marking Place}
    (h : M ⇝[N] M') : Marking.weight w M' = Marking.weight w M :=
  h.invariant (P := fun K => Marking.weight w K = Marking.weight w M)
    (fun htr hK => (hw.weight_fires htr).trans hK) rfl

/-- A marking has weight zero if all its tokens lie in places of weight zero. -/
theorem weight_eq_zero_of {w : Place → ℕ} {M : Marking Place} (h : ∀ p ∈ M, w p = 0) :
    Marking.weight w M = 0 := by
  rw [Marking.weight_apply, Multiset.sum_eq_zero_iff]
  simpa using h

/-- Adding tokens never decreases the weight. -/
theorem Marking.weight_mono (w : Place → ℕ) {M M' : Marking Place} (h : M ≤ M') :
    Marking.weight w M ≤ Marking.weight w M' := by
  obtain ⟨K, rfl⟩ := exists_add_of_le h
  rw [map_add]
  exact Nat.le_add_right _ _

/-- A token in `p` contributes the weight of `p`. -/
theorem Marking.le_weight_of_mem (w : Place → ℕ) {M : Marking Place} {p : Place} (h : p ∈ M) :
    w p ≤ Marking.weight w M :=
  Multiset.le_sum_of_mem (Multiset.mem_map_of_mem w h)

/-- A place carries at most its share of the weighted token count. -/
theorem Marking.mul_le_weight [DecidableEq Place] (w : Place → ℕ) (M : Marking Place) (p : Place) :
    w p * M.count p ≤ Marking.weight w M := by
  have := Marking.weight_mono w (Multiset.le_count_iff_replicate_le.1 (le_refl (M.count p)))
  simpa [Marking.weight_apply, mul_comm] using this

/-- A positive invariant bounds the tokens in every place by the initial weighted token count. -/
theorem IsInvariant.kBounded (hw : N.IsInvariant w) (hpos : ∀ p, 0 < w p)
    (M₀ : Marking Place) : N.KBounded M₀ (Marking.weight w M₀) := by
  classical
  refine kBounded_iff.2 fun M hM p => ?_
  calc M.count p ≤ w p * M.count p := Nat.le_mul_of_pos_left _ (hpos p)
    _ ≤ Marking.weight w M := Marking.mul_le_weight w M p
    _ = Marking.weight w M₀ := hw.weight_eq hM

/-- A net with a positive invariant is bounded at every marking. -/
theorem IsInvariant.bounded (hw : N.IsInvariant w) (hpos : ∀ p, 0 < w p)
    (M₀ : Marking Place) : N.Bounded M₀ :=
  ⟨_, hw.kBounded hpos M₀⟩

/-- Conservative nets are those with the constant weighting `1` as an invariant. -/
theorem conservative_iff_isInvariant : N.Conservative ↔ N.IsInvariant (fun _ => 1) := by
  simp [Conservative, IsInvariant]

end PetriNet

end Cslib
