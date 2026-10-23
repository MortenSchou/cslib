/-
Copyright (c) 2026 Morten Schou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Morten Schou
-/

module

public import Cslib.Computability.PetriNets.Semantics

/-! # Monotonicity of Petri nets

Adding tokens to a marking never disables a firing sequence. This is the basis of most decision
procedures for Petri nets (coverability, boundedness, etc.).

## Main statements

- `PetriNet.Enabled.mono`: enabledness is upward closed.
- `PetriNet.mTr_mono`, `PetriNet.Reachable.mono`: a firing sequence from `M₁` can be replayed from
  any larger marking, reaching a marking that is larger than the original target.
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

/-- A firing sequence from `M₁` can be replayed from any `M₂ ≥ M₁`, and the new target covers the
old one. -/
theorem mTr_mono {M₁ M₁' M₂ : Marking Place} {ts : List Transition}
    (h : N.lts.MTr M₁ ts M₁') (hle : M₁ ≤ M₂) :
    ∃ M₂', N.lts.MTr M₂ ts M₂' ∧ M₁' ≤ M₂' := by
  obtain ⟨K, rfl⟩ := le_iff_exists_add.1 hle
  exact ⟨M₁' + K, mTr_add h K, le_self_add⟩

theorem Reachable.mono {M₁ M₁' M₂ : Marking Place} (h : M₁ ⇝[N] M₁') (hle : M₁ ≤ M₂) :
    ∃ M₂', M₂ ⇝[N] M₂' ∧ M₁' ≤ M₂' :=
  let ⟨ts, hts⟩ := h
  let ⟨M₂', h₂, hle'⟩ := mTr_mono hts hle
  ⟨M₂', ⟨ts, h₂⟩, hle'⟩

/-- Boundedness is downward closed in the initial marking. -/
theorem KBounded.mono_marking {M₁ M₂ : Marking Place} {k : ℕ} (h : N.KBounded M₂ k)
    (hle : M₁ ≤ M₂) : N.KBounded M₁ k := fun _ hM p =>
  let ⟨M', hM', hle'⟩ := hM.mono hle
  (hle' p).trans (h M' hM' p)

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
