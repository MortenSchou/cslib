/-
Copyright (c) 2026 Morten Schou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Morten Schou
-/

module

public import Cslib.Computability.PetriNets.Semantics
public import Cslib.Foundations.Semantics.LTS.Bisimulation
public import Cslib.Foundations.Semantics.LTS.TraceEq
public import Cslib.Logics.HML.Basic

/-! # Behavioural equivalence of markings

The marking graph of a Petri net is deterministic: firing a transition at a marking has a unique
result. For deterministic labelled transition systems, trace equivalence is a bisimulation, so
bisimilarity coincides with trace equivalence. Together with image-finiteness, this identifies
bisimilar markings with markings satisfying the same Hennessy-Milner formulas.

## Main statements

- `PetriNet.bisimilar_iff_traces_eq`: two markings are bisimilar iff the same firing sequences are
  possible from both.
- `PetriNet.bisimilar_of_dead`: any two dead markings are bisimilar.
- `PetriNet.theoryEq_iff_bisimilar`: two markings satisfy the same HML formulas iff they are
  bisimilar.
-/

@[expose] public section

namespace Cslib

namespace PetriNet

open LTS

variable {Place Transition : Type*} (N : PetriNet Place Transition)

/-- Two markings are bisimilar exactly when they allow the same firing sequences. -/
theorem bisimilar_iff_traces_eq (M₁ M₂ : Marking Place) :
    (M₁ ~[N.lts] M₂) ↔ N.lts.traces M₁ = N.lts.traces M₂ :=
  Deterministic.bisimilarity_iff_traceEq M₁ M₂

/-- A dead marking allows only the empty firing sequence. -/
theorem traces_of_dead {M : Marking Place} (hd : N.Dead M) : N.lts.traces M = {[]} := by
  ext ts
  constructor
  · rintro ⟨M', h⟩
    cases h with
    | refl => rfl
    | stepL htr _ => exact absurd htr (hd _ _)
  · rintro rfl
    exact ⟨M, .refl⟩

/-- Any two dead markings are bisimilar. -/
theorem bisimilar_of_dead {M₁ M₂ : Marking Place} (h₁ : N.Dead M₁) (h₂ : N.Dead M₂) :
    M₁ ~[N.lts] M₂ :=
  (bisimilar_iff_traces_eq N M₁ M₂).2 ((traces_of_dead N h₁).trans (traces_of_dead N h₂).symm)

open Logic.Modal in
/-- Two markings satisfy the same Hennessy-Milner formulas, for any valuation of atoms that
respects bisimilarity, exactly when they are bisimilar. -/
theorem theoryEq_iff_bisimilar {Atom : Type*} (v : Marking Place → Atom → Prop)
    (hv : ∀ {M₁ M₂}, (M₁ ~[N.lts] M₂) → ∀ p, v M₁ p ↔ v M₂ p) (M₁ M₂ : Marking Place) :
    TheoryEq (HML.Model.mk N.lts v).toModal M₁ M₂ ↔ (M₁ ~[N.lts] M₂) := by
  have := theoryEq_eq_bisimilarity (m := HML.Model.mk N.lts v) hv
  exact Iff.of_eq (congrFun (congrFun this M₁) M₂)

end PetriNet

end Cslib
