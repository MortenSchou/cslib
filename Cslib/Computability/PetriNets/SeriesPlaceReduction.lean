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
(`•t = {p₁}` and `t• = {p₂}`), and `t` is the only transition that consumes from `p₁`. Nothing is
required of the producers of `p₁` or of the arcs at `p₂`. The reduced net drops `t`, and every token
that a transition puts into `p₁` goes into `p₂` instead, so the merged place holds the tokens of
`p₁` and of `p₂`. The reduction preserves its properties under side conditions, as in
[Murata1989] (FSP) and in the reduction of workflow nets [Aalst1998].

This is the reduction of `Cslib.Computability.PetriNets.SeriesReduction` for a transition `t` that
drains `p₁`: the net `PetriNet.fuse N t p₁` is the reduced net with the isolated place `p₁`, and
`PetriNet.fuseDelete N t p₁` is the reduced net without it. A token in `p₁` can always be moved to
`p₂` by `t`, which is invisible, so each marking is weakly bisimilar to the marking that has moved
all tokens of `p₁` to `p₂`. The main results are for initial markings with `p₁` empty; the
`_collapse_iff` variants state them for an arbitrary initial marking, at its collapse.

## Main definitions

- `PetriNet.IsSeriesPlace`: `p₁ → t → p₂` is a series of places; decidable for finitely many
  transitions.

## Main statements

- `PetriNet.IsSeriesPlace.toIsDrain`: a series of places is a drained place, so all results of
  `Cslib.Computability.PetriNets.SeriesReduction` apply (through `h.toIsDrain`): reachability,
  reachable deadlocks, deadlock-freedom and liveness (given a producer of `p₁`) are preserved, for
  the initial marking with `p₁` empty (`h₀`) or at its collapse (`_collapse_iff`).
- `PetriNet.IsSeriesPlace.count_collapse_right`: the merged place holds the tokens of both places.
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

variable (N) in
/-- `p₁ → t → p₂` is a series of places: `t` drains `p₁` (it is the only transition consuming from
`p₁`, and consumes a single token of it and nothing else), and it moves that token to `p₂`. The two
places are different (`IsSeriesPlace.ne`). -/
structure IsSeriesPlace (t : Transition) (p₁ p₂ : Place) : Prop extends N.IsDrain t p₁ where
  /-- The only output of `t` is one token in `p₂`. -/
  post_eq : t •[N] = {p₂}

instance [DecidableEq Place] [DecidableEq Transition] [Fintype Transition] (t : Transition)
    (p₁ p₂ : Place) : Decidable (N.IsSeriesPlace t p₁ p₂) :=
  decidable_of_iff (N.IsDrain t p₁ ∧ t •[N] = {p₂})
    ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.1, h.2⟩⟩

namespace IsSeriesPlace

variable {t : Transition} {p₁ p₂ : Place}

/-- The two places are different. -/
theorem ne (h : N.IsSeriesPlace t p₁ p₂) : p₁ ≠ p₂ := fun e =>
  h.notMem_post (by rw [h.post_eq, e]; exact Multiset.mem_singleton_self p₂)

/-- The transition of a series of places produces a token. -/
theorem post_ne_zero (h : N.IsSeriesPlace t p₁ p₂) : t •[N] ≠ 0 := by
  rw [h.post_eq]
  exact Multiset.singleton_ne_zero p₂

variable [DecidableEq Place]

/-- The merged place holds the tokens of both places. -/
theorem count_collapse_right (h : N.IsSeriesPlace t p₁ p₂) (M : Marking Place) :
    (N.collapse t p₁ M).count p₂ = M.count p₁ + M.count p₂ := by
  rw [count_collapse_of_ne h.ne.symm, h.post_eq, Multiset.count_singleton_self, Nat.mul_one,
    Nat.add_comm]

/-- The tokens of the other places are unchanged. -/
theorem count_collapse_other (h : N.IsSeriesPlace t p₁ p₂) (M : Marking Place) {q : Place}
    (hq₁ : q ≠ p₁) (hq₂ : q ≠ p₂) : (N.collapse t p₁ M).count q = M.count q := by
  rw [count_collapse_of_ne hq₁, h.post_eq,
    (Multiset.count_eq_zero (s := {p₂})).2 (notMem_token hq₂), Nat.mul_zero, Nat.add_zero]

/-- Every marking is weakly bisimilar to the marking that has moved the tokens of `p₁` to `p₂`,
where `t` is the invisible action. -/
theorem weakBisimilar_collapse [DecidableEq Transition] (h : N.IsSeriesPlace t p₁ p₂)
    (M : Marking Place) :
    WeakBisimilarity (N.labelledLts (hide t)) ((N.fuse t p₁).labelledLts some)
      M (N.collapse t p₁ M) :=
  h.toIsDrain.weakBisimilar_collapse M

/-- The reduction preserves boundedness. -/
theorem bounded_fuseDelete_iff (h : N.IsSeriesPlace t p₁ p₂) {M₀ : Marking Place}
    (h₀ : p₁ ∉ M₀) : (N.fuseDelete t p₁).Bounded (M₀.drop p₁) ↔ N.Bounded M₀ :=
  h.toIsDrain.bounded_fuseDelete_iff h₀ h.post_ne_zero

/-- The reduction preserves boundedness, from any marking. -/
theorem bounded_fuseDelete_collapse_iff (h : N.IsSeriesPlace t p₁ p₂) {M₀ : Marking Place} :
    (N.fuseDelete t p₁).Bounded ((N.collapse t p₁ M₀).drop p₁) ↔ N.Bounded M₀ :=
  h.toIsDrain.bounded_fuseDelete_collapse_iff h.post_ne_zero

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
