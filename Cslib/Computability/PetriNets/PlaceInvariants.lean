/-
Copyright (c) 2026 Morten Schou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Morten Schou
-/

module

public import Cslib.Computability.PetriNets.Semantics
public import Mathlib.Data.Finsupp.Multiset

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

/-- The weighted number of tokens of a marking, for a weighting `w` of the places. -/
noncomputable def Marking.weight (w : Place → ℕ) : Marking Place →+ ℕ :=
  Finsupp.liftAddHom fun p => AddMonoidHom.mulLeft (w p)

theorem Marking.weight_apply (w : Place → ℕ) (M : Marking Place) :
    Marking.weight w M = M.sum fun p n => w p * n := by
  simp [Marking.weight, Finsupp.liftAddHom_apply]

/-- The weight of a marking given as a multiset is the sum of the weights of its tokens. -/
theorem Marking.weight_toFinsupp [DecidableEq Place] (w : Place → ℕ) (s : Multiset Place) :
    Marking.weight w (Multiset.toFinsupp s) = (s.map w).sum := by
  induction s using Multiset.induction with
  | empty => simp
  | cons a s ih =>
    rw [← Multiset.singleton_add, map_add Multiset.toFinsupp, map_add (Marking.weight w), ih]
    simp [Multiset.toFinsupp_singleton, Marking.weight_apply]

@[simp] theorem Marking.weight_one (M : Marking Place) :
    Marking.weight (fun _ => 1) M = M.size := by
  simp [Marking.weight_apply, Marking.size, Finsupp.degree_apply, Finsupp.sum]

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

/-- A marking has weight zero if every place has weight zero or no tokens. -/
theorem weight_eq_zero_of {w : Place → ℕ} {M : Marking Place} (h : ∀ p, w p = 0 ∨ M p = 0) :
    Marking.weight w M = 0 := by
  rw [Marking.weight_apply]
  exact Finset.sum_eq_zero fun p _ => by rcases h p with h | h <;> simp [h]

/-- A place carries at most its share of the weighted token count. -/
theorem Marking.mul_le_weight (w : Place → ℕ) (M : Marking Place) (p : Place) :
    w p * M p ≤ Marking.weight w M := by
  rw [Marking.weight_apply]
  by_cases hp : p ∈ M.support
  · exact Finset.single_le_sum (f := fun i => w i * M i) (fun _ _ => Nat.zero_le _) hp
  · simp [Finsupp.notMem_support_iff.1 hp]

/-- A positive invariant bounds the tokens in every place by the initial weighted token count. -/
theorem IsInvariant.kBounded (hw : N.IsInvariant w) (hpos : ∀ p, 0 < w p) (M₀ : Marking Place) :
    N.KBounded M₀ (Marking.weight w M₀) := fun M hM p =>
  calc M p ≤ w p * M p := Nat.le_mul_of_pos_left _ (hpos p)
    _ ≤ Marking.weight w M := Marking.mul_le_weight w M p
    _ = Marking.weight w M₀ := hw.weight_eq hM

/-- A net with a positive invariant is bounded at every marking. -/
theorem IsInvariant.bounded (hw : N.IsInvariant w) (hpos : ∀ p, 0 < w p) (M₀ : Marking Place) :
    N.Bounded M₀ :=
  ⟨_, hw.kBounded hpos M₀⟩

/-- Conservative nets are those with the constant weighting `1` as an invariant. -/
theorem conservative_iff_isInvariant : N.Conservative ↔ N.IsInvariant (fun _ => 1) := by
  simp [Conservative, IsInvariant]

end PetriNet

end Cslib
