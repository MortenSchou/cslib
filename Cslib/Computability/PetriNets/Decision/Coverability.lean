/-
Copyright (c) 2026 Morten Schou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Morten Schou
-/

module

public import Cslib.Computability.PetriNets.WSTS
public import Cslib.Computability.WSTS.Decidability

/-! # Decidable coverability

Over finitely many places, coverability is decided by the generic backward coverability algorithm
of `Cslib.WSTS.decidableCoverable`, run on finite bases of markings. The only net-specific
ingredient is the effective pred-basis: the minimal markings from which `t` fires into the
markings above `b` is `•[N] t + (b - t •[N])`, with truncated subtraction of multisets.
Termination and correctness come from the generic theory, since the marking graph is a WSTS over
finitely many places (`PetriNet.instWSTS`).

## Main definitions

- `PetriNet.predBasis`: the effective pred-basis of a net.

## Main statements

- `PetriNet.isPredBasis`: `predBasis` is a correct pred-basis for the marking graph.
- `PetriNet.instDecidableCoverable`: coverability is decidable over finitely many places and
  transitions, and can be evaluated by `decide`.
-/

@[expose] public section

namespace Cslib

namespace PetriNet

variable {Place Transition : Type*} [DecidableEq Place] [Fintype Transition]
  (N : PetriNet Place Transition)

/-- The minimal markings from which one firing leads above some element of `B`. -/
def predBasis (B : Finset (Marking Place)) : Finset (Marking Place) :=
  B.biUnion fun b => Finset.univ.image fun t => •[N] t + (b - t •[N])

/-- `predBasis` is an effective pred-basis for the marking graph of a net. -/
theorem isPredBasis : WSTS.IsPredBasis N.lts N.predBasis := by
  intro B
  ext M
  change (∃ x ∈ N.predBasis B, x ≤ M) ↔ ∃ t M', M [t⟩[N] M' ∧ ∃ b ∈ B, b ≤ M'
  constructor
  · rintro ⟨x, hx, hle⟩
    obtain ⟨b, hb, hx⟩ := Finset.mem_biUnion.1 hx
    obtain ⟨t, -, rfl⟩ := Finset.mem_image.1 hx
    obtain ⟨R₀, rfl⟩ := le_iff_exists_add.1 hle
    refine ⟨t, b - t •[N] + R₀ + t •[N], ⟨b - t •[N] + R₀, add_assoc .., rfl⟩, b, hb, ?_⟩
    exact le_tsub_add.trans (add_le_add_left le_self_add _)
  · rintro ⟨t, M', ⟨R, rfl, rfl⟩, b, hb, hbM'⟩
    refine ⟨•[N] t + (b - t •[N]), ?_, add_le_add_right (tsub_le_iff_right.2 hbM') _⟩
    exact Finset.mem_biUnion.2 ⟨b, hb, Finset.mem_image.2 ⟨t, Finset.mem_univ _, rfl⟩⟩

/-- Coverability is decidable over finitely many places and transitions.

This is the generic backward coverability algorithm of `Cslib.WSTS.decidableCoverable`, with the
pred-basis `predBasis`. The search for the stable basis uses `searchIter`, so `decide` can evaluate
it. -/
instance instDecidableCoverable [Fintype Place] (M₀ M : Marking Place) :
    Decidable (N.Coverable M₀ M) :=
  WSTS.decidableCoverable (N.isPredBasis) M₀ M

end PetriNet

end Cslib
