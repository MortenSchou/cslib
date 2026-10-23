/-
Copyright (c) 2026 Morten Schou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Morten Schou
-/

module

public import Cslib.Computability.PetriNets.SeriesReduction

/-! # Fusion of series places

Murata's reduction *fusion of series places* merges two places `p₁` and `p₂` that are linked by a
transition `t`: the transition `t` moves one token from `p₁` to `p₂` and does nothing else
(`•t = {p₁}` and `t• = {p₂}`, with unit weights), and `t` is the only transition that consumes from
`p₁`. Nothing is required of the producers of `p₁` or of the arcs at `p₂`. The reduced net drops
`t`, and every token that a transition puts into `p₁` goes into `p₂` instead, so the merged place
holds `M p₁ + M p₂` tokens. The reduction preserves its properties under side conditions, as in
[Murata1989] (FSP) and in the reduction of workflow nets [Aalst1998].

This is the reduction of `Cslib.Computability.PetriNets.SeriesReduction` for a transition `t` that
drains `p₁`: the net `PetriNet.fuse N t p₁` is the reduced net with the isolated place `p₁`, and
`PetriNet.fuseDelete N t p₁` is the reduced net without it. A token in `p₁` can always be moved to
`p₂` by `t`, which is invisible, so each marking is weakly bisimilar to the marking that has moved
all tokens of `p₁` to `p₂`. The main results are for initial markings with `p₁` empty; the
`_collapse_iff` variants state them for an arbitrary initial marking, at its collapse.

## Main definitions

- `PetriNet.IsSeriesPlace`: `p₁ → t → p₂` is a series of places.

## Main statements

- `PetriNet.IsSeriesPlace.toIsDrain`: a series of places is a drained place, so all results of
  `Cslib.Computability.PetriNets.SeriesReduction` apply (through `h.toIsDrain`): reachability,
  reachable deadlocks, deadlock-freedom and liveness (given a producer of `p₁`) are preserved, for
  the initial marking with `p₁` empty (`h₀`) or at its collapse (`_collapse_iff`).
- `PetriNet.IsSeriesPlace.collapse_apply_right`: the merged place holds `M p₁ + M p₂` tokens.
- `PetriNet.IsSeriesPlace.weakBisimilar_collapse`: each marking is weakly bisimilar to its
  collapse in the reduced net.
- `PetriNet.IsSeriesPlace.bounded_fuseDelete_iff`: the reduction preserves boundedness; the
  condition that the transition produces a token is automatic.
- `PetriNet.IsSeriesPlace.isWFNet_and_sound_fuseDelete`: for a workflow net the reduced net is a
  workflow net, and it is sound iff the original net is.

## References

* [T. Murata, *Petri nets: Properties, analysis and applications*][Murata1989]
* [W. M. P. van der Aalst, *The application of Petri nets to workflow management*,
  J. Circuits Syst. Comput. 8 (1998)][Aalst1998]
-/

@[expose] public section

namespace Cslib

namespace PetriNet

open LTS
open scoped PetriNet

variable {Place Transition : Type*} {N : PetriNet Place Transition}

/-- `p₁ → t → p₂` is a series of places: `t` moves one token from `p₁` to `p₂`, and no other
transition consumes from `p₁`. -/
structure IsSeriesPlace (N : PetriNet Place Transition) (t : Transition) (p₁ p₂ : Place) :
    Prop where
  /-- The two places are different. -/
  ne : p₁ ≠ p₂
  /-- The only input of `t` is one token in `p₁`. -/
  pre_eq : •[N] t = Finsupp.single p₁ 1
  /-- The only output of `t` is one token in `p₂`. -/
  post_eq : t •[N] = Finsupp.single p₂ 1
  /-- No transition other than `t` consumes from `p₁`. -/
  pre_of_ne : ∀ t', t' ≠ t → (•[N] t') p₁ = 0

namespace IsSeriesPlace

variable {t : Transition} {p₁ p₂ : Place}

/-- The transition of a series of places drains the first place. -/
theorem toIsDrain (h : N.IsSeriesPlace t p₁ p₂) : N.IsDrain t p₁ where
  pre_eq := h.pre_eq
  post_apply := by rw [h.post_eq]; exact Finsupp.single_eq_of_ne h.ne
  pre_of_ne := h.pre_of_ne

/-- The transition of a series of places produces a token. -/
theorem post_pos (h : N.IsSeriesPlace t p₁ p₂) : ∃ q, 0 < (t •[N]) q :=
  ⟨p₂, by rw [h.post_eq]; simp⟩

/-- The merged place holds the tokens of both places. -/
theorem collapse_apply_right (h : N.IsSeriesPlace t p₁ p₂) (M : Marking Place) :
    N.collapse t p₁ M p₂ = M p₁ + M p₂ := by
  rw [collapse_apply_of_ne h.ne.symm, h.post_eq]
  simp [add_comm]

/-- The tokens of the other places are unchanged. -/
theorem collapse_apply_other (h : N.IsSeriesPlace t p₁ p₂) (M : Marking Place) {q : Place}
    (hq₁ : q ≠ p₁) (hq₂ : q ≠ p₂) : N.collapse t p₁ M q = M q := by
  rw [PetriNet.collapse_apply_of_ne hq₁, h.post_eq, Finsupp.single_eq_of_ne hq₂]
  simp

/-- Every marking is weakly bisimilar to the marking that has moved the tokens of `p₁` to `p₂`,
where `t` is the invisible action. -/
theorem weakBisimilar_collapse (h : N.IsSeriesPlace t p₁ p₂) (M : Marking Place) :
    WeakBisimilarity (N.labelledLts (hide t)) ((N.fuse t p₁).labelledLts some)
      M (N.collapse t p₁ M) :=
  h.toIsDrain.weakBisimilar_collapse M

/-- The reduction preserves boundedness. -/
theorem bounded_fuseDelete_iff (h : N.IsSeriesPlace t p₁ p₂) {M₀ : Marking Place}
    (h₀ : M₀ p₁ = 0) : (N.fuseDelete t p₁).Bounded (M₀.drop p₁) ↔ N.Bounded M₀ :=
  h.toIsDrain.bounded_fuseDelete_iff h₀ h.post_pos

/-- The reduction preserves boundedness, from any marking. -/
theorem bounded_fuseDelete_collapse_iff (h : N.IsSeriesPlace t p₁ p₂) {M₀ : Marking Place} :
    (N.fuseDelete t p₁).Bounded ((N.collapse t p₁ M₀).drop p₁) ↔ N.Bounded M₀ :=
  h.toIsDrain.bounded_fuseDelete_collapse_iff h.post_pos

/-- For a workflow net whose source is not `p₁`, the reduced net is a workflow net, and it is
sound iff `N` is. -/
theorem isWFNet_and_sound_fuseDelete (h : N.IsSeriesPlace t p₁ p₂) {i o : Place}
    (hN : N.IsWFNet i o) (hi : i ≠ p₁) :
    (N.fuseDelete t p₁).IsWFNet ⟨i, hi⟩ ⟨o, h.toIsDrain.ne_sink hN⟩ ∧
      ((N.fuseDelete t p₁).Sound ⟨i, hi⟩ ⟨o, h.toIsDrain.ne_sink hN⟩ ↔ N.Sound i o) :=
  h.toIsDrain.isWFNet_and_sound_fuseDelete hN hi

end IsSeriesPlace

end PetriNet

end Cslib
