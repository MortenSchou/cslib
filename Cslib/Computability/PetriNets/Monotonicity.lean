/-
Copyright (c) 2026 Morten Schou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Morten Schou
-/

module

public import Cslib.Computability.PetriNets.Semantics
public import Cslib.Computability.WSTS.Basic

/-! # Monotonicity of Petri nets

Adding tokens to a marking never disables a firing sequence. This is the basis of most decision
procedures for Petri nets (coverability, boundedness, etc.).

## Main statements

- `PetriNet.Enabled.mono`: enabledness is upward closed.
- `PetriNet.instStronglyMonotone`: the marking graph of any net is strongly monotone, so the
  generic monotonicity results of `Cslib.WSTS` apply (no finiteness of `Place` is needed).
- `PetriNet.mTr_mono`, `PetriNet.Reachable.mono`: a firing sequence from `M₁` can be replayed from
  any larger marking, reaching a marking that is larger than the original target. These are the
  generic `Cslib.WSTS.mTr_mono` and `Cslib.WSTS.canReach_mono`.
- `PetriNet.KBounded.mono_marking`, `PetriNet.Bounded.mono_marking`: boundedness at a marking
  implies boundedness at every smaller marking. Contrapositively, unboundedness is upward closed.
-/

@[expose] public section

namespace Cslib

namespace PetriNet

variable {Place : Type*} {Transition : Type*} {N : PetriNet Place Transition}

/-- Enabledness is upward closed. -/
@[grind →]
theorem Enabled.mono {M₁ M₂ : Marking Place} {t : Transition} (h : M₁ [t⟩[N])
    (hle : M₁ ≤ M₂) : M₂ [t⟩[N] :=
  le_trans h hle

/-- The marking graph of any net is strongly monotone: a firing from `M₁` is matched from any
`M₂ ≥ M₁` by the same transition, reaching a larger marking. Unlike `WSTS`, this needs no
finiteness of `Place`. -/
instance instStronglyMonotone (N : PetriNet Place Transition) : StronglyMonotone N.lts where
  mono {M₁ M₂ M₁'} {t} hle h := by
    obtain ⟨K, rfl⟩ := le_iff_exists_add.1 hle
    exact ⟨M₁' + K, h.add K, le_self_add⟩

/-- A firing sequence from `M₁` can be replayed from any larger marking, and the new target covers
the old one. -/
theorem mTr_mono {M₁ M₁' M₂ : Marking Place} {ts : List Transition}
    (h : N.lts.MTr M₁ ts M₁') (hle : M₁ ≤ M₂) :
    ∃ M₂', N.lts.MTr M₂ ts M₂' ∧ M₁' ≤ M₂' :=
  WSTS.mTr_mono h hle

/-- Reachability is monotone in the source marking. -/
theorem Reachable.mono {M₁ M₁' M₂ : Marking Place} (h : M₁ ⇝[N] M₁') (hle : M₁ ≤ M₂) :
    ∃ M₂', M₂ ⇝[N] M₂' ∧ M₁' ≤ M₂' :=
  WSTS.canReach_mono h hle

/-- Boundedness is downward closed in the initial marking. -/
theorem KBounded.mono_marking {M₁ M₂ : Marking Place} {k : ℕ} (h : N.KBounded M₂ k)
    (hle : M₁ ≤ M₂) : N.KBounded M₁ k := fun _ hM p hp =>
  let ⟨M', hM', hle'⟩ := hM.mono hle
  h M' hM' p (hp.trans hle')

theorem Bounded.mono_marking {M₁ M₂ : Marking Place} (h : N.Bounded M₂) (hle : M₁ ≤ M₂) :
    N.Bounded M₁ :=
  let ⟨k, hk⟩ := h
  ⟨k, hk.mono_marking hle⟩

/-- Unboundedness is upward closed in the initial marking. -/
theorem not_bounded_of_le {M₁ M₂ : Marking Place} (h : ¬ N.Bounded M₁) (hle : M₁ ≤ M₂) :
    ¬ N.Bounded M₂ :=
  fun hb => h (hb.mono_marking hle)

end PetriNet

end Cslib
