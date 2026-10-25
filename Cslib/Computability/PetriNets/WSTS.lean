/-
Copyright (c) 2026 Morten Schou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Morten Schou
-/

module

public import Cslib.Computability.PetriNets.Coverability
public import Cslib.Computability.WSTS.InfiniteRuns

/-! # Petri nets as well-structured transition systems

Over finitely many places, the marking graph of a net is a WSTS: markings are well-quasi-ordered by
Dickson's lemma and firing is monotone (`PetriNet.instStronglyMonotone`). The generic theory of
`Cslib.WSTS` therefore applies to Petri nets, and the Petri-net specific coverability and
backward-coverability files are thin wrappers around it.

## Main statements

- `PetriNet.instWSTS`: the marking graph of a net with finitely many places is a WSTS.
- `PetriNet.exists_run_iff`: a marking starts an infinite firing sequence iff it reaches a marking
  that reaches a larger marking in at least one step.
-/

@[expose] public section

namespace Cslib

namespace PetriNet

variable {Place : Type*} {Transition : Type*} {N : PetriNet Place Transition}

/-- Over finitely many places, the marking graph of a net is a well-structured transition system:
it is strongly monotone (`PetriNet.instStronglyMonotone`), and markings are well-quasi-ordered by
Dickson's lemma. -/
instance instWSTS [Finite Place] (N : PetriNet Place Transition) : WSTS N.lts :=
  { (inferInstance : WellQuasiOrderedLE (Marking Place)), instStronglyMonotone N with }

/-- A marking starts an infinite firing sequence iff it reaches a marking that reaches, in at least
one firing, a larger marking. -/
theorem exists_run_iff [Finite Place] (M₀ : Marking Place) :
    (∃ f : ℕ → Marking Place, f 0 = M₀ ∧ ∀ n, N.lts.UnlabelledTr (f n) (f (n + 1))) ↔
      ∃ M₁ M₂, Relation.ReflTransGen N.lts.UnlabelledTr M₀ M₁ ∧
        Relation.TransGen N.lts.UnlabelledTr M₁ M₂ ∧ M₁ ≤ M₂ :=
  WSTS.exists_run_iff (lts := N.lts) M₀

end PetriNet

end Cslib
