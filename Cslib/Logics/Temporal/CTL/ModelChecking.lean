/-
Copyright (c) 2026 Morten Schou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Morten Schou
-/

module

public import Cslib.Logics.Temporal.CTL.Denotation
public import Cslib.Foundations.Data.Finset.Iterate
public import Mathlib.Data.Fintype.Powerset

/-! # Model checking CTL on finite models

For a model with finitely many states, the satisfaction of a CTL formula is decidable. The
algorithm is the classical labelling algorithm [Clarke1986]: the set of states satisfying a formula
is computed bottom-up, with `E[φ U ψ]` and `EG φ` computed by iterating their fixpoint operators
`card State` times from `∅`, respectively from `univ`. Since the operators are monotone on a
finite lattice, the iteration reaches the fixpoint after at most `card State` steps.

## Main definitions

- `check`: the finite set of states satisfying a formula.

## Main statements

- `coe_check`: `check` computes `denote`, hence `⇓CTL[m,s ⊨ φ]` (`mem_check_iff`).
- `Satisfies.decidable`: satisfaction is decidable for finite models.
-/

@[expose] public section

namespace Cslib.Logic.CTL

open scoped InferenceSystem Formula Cslib.Logic

section Check

variable {State : Type*} {Atom : Type*} [Fintype State] [DecidableEq State]
  (m : Model State Atom) [DecidableRel m.tr]

instance Model.decidableDead (s : State) : Decidable (m.Dead s) :=
  inferInstanceAs (Decidable (∀ t, ¬ m.tr s t))

/-- The states with a successor in `X`. -/
def Model.preF (X : Finset State) : Finset State :=
  Finset.univ.filter fun s => ∃ t, m.tr s t ∧ t ∈ X

/-- One step of the iteration for `E[A U B]`. -/
def euStep (A B X : Finset State) : Finset State := B ∪ (A ∩ m.preF X)

/-- One step of the iteration for `EG A`. -/
def egStep (A X : Finset State) : Finset State :=
  A ∩ (m.preF X ∪ Finset.univ.filter fun s => m.Dead s)

theorem Model.coe_preF (X : Finset State) : (m.preF X : Set State) = m.pre X := by
  ext s; simp [Model.preF, Model.pre]

theorem euStep_mono (A B : Finset State) : Monotone (euStep m A B) := fun X Y h =>
  Finset.union_subset_union (le_refl _) (Finset.inter_subset_inter (le_refl _)
    (fun s hs => by
      simp only [Model.preF, Finset.mem_filter, Finset.mem_univ, true_and] at hs ⊢
      obtain ⟨t, htr, ht⟩ := hs
      exact ⟨t, htr, h ht⟩))

theorem egStep_mono (A : Finset State) : Monotone (egStep m A) := fun X Y h =>
  Finset.inter_subset_inter (le_refl _) (Finset.union_subset_union (fun s hs => by
      simp only [Model.preF, Finset.mem_filter, Finset.mem_univ, true_and] at hs ⊢
      obtain ⟨t, htr, ht⟩ := hs
      exact ⟨t, htr, h ht⟩) (le_refl _))

variable [∀ s p, Decidable (m.v s p)]

/-- The finite set of states satisfying a formula, computed by the labelling algorithm. -/
def check : Formula Atom → Finset State
  | .atom p => Finset.univ.filter fun s => m.v s p
  | .false => ∅
  | .not φ => (check φ)ᶜ
  | .or φ ψ => check φ ∪ check ψ
  | .ex φ => m.preF (check φ)
  | .eu φ ψ => (euStep m (check φ) (check ψ))^[Fintype.card State] ∅
  | .eg φ => (egStep m (check φ))^[Fintype.card State] Finset.univ

/-- The labelling algorithm computes the fixpoint semantics. -/
theorem coe_check (φ : Formula Atom) : (check m φ : Set State) = denote m φ := by
  induction φ with
  | atom p => ext s; simp [check, denote]
  | false => simp [check, denote]
  | not φ ih => simp [check, denote, ← ih]
  | or φ ψ ihφ ihψ => simp [check, denote, ← ihφ, ← ihψ]
  | ex φ ih => simp [check, denote, Model.coe_preF, ih]
  | eu φ ψ ihφ ihψ =>
    rw [check, denote, ← lfp_eq_iterate (euStep_mono m _ _) (euOp m (denote m φ) (denote m ψ))]
    intro X
    simp [euStep, Model.coe_preF, ihφ, ihψ]
    rfl
  | eg φ ih =>
    rw [check, denote, ← gfp_eq_iterate (egStep_mono m _) (egOp m (denote m φ))]
    intro X
    simp [egStep, Model.coe_preF, ih]
    rfl

/-- A state satisfies a formula iff the labelling algorithm puts it in the set of the formula. -/
theorem mem_check_iff (φ : Formula Atom) (s : State) : s ∈ check m φ ↔ ⇓CTL[m,s ⊨ φ] := by
  rw [← mem_denote_iff, ← coe_check]
  rfl

/-- Satisfaction of CTL formulas is decidable in finite models. -/
instance Satisfies.decidable (s : State) (φ : Formula Atom) : Decidable (⇓CTL[m,s ⊨ φ]) :=
  decidable_of_iff _ (mem_check_iff m φ s)

end Check

end Cslib.Logic.CTL
