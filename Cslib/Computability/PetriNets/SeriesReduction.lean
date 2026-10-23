/-
Copyright (c) 2026 Morten Schou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Morten Schou
-/

module

public import Cslib.Computability.PetriNets.Labelled
public import Cslib.Computability.PetriNets.Reduction
public import Cslib.Computability.PetriNets.Soundness
public import Cslib.Computability.PetriNets.SoundnessNotions
public import Cslib.Computability.Automata.EpsilonNA.Basic
public import Cslib.Foundations.Semantics.LTS.Bisimulation

/-! # Fusion of series transitions

Murata's reduction *fusion of series transitions* removes an intermediate place `p` between two
transitions `t₁` and `t₂`: `t₁` is the only transition that produces into `p`, and `t₂` is the only
transition that consumes from `p`, and `t₂` consumes nothing but a token of `p`. The two transitions
are fused into one that behaves like `t₁` followed by `t₂`. Under such side conditions the reduction
preserves liveness, boundedness and (for workflow nets) soundness, which is the use made of it by
van der Aalst for deciding soundness after reducing the net.

Concretely, the reduced net `PetriNet.fuse N t₂ p` has the transitions of `N` except `t₂`, and
every transition `t` keeps its preset while its postset is *collapsed*: the tokens that `t` puts in
`p` are replaced by the postset of `t₂` (`PetriNet.collapse`). Only `t₁` puts tokens in `p`, so
only `t₁` changes, and it becomes `t₁` followed by `t₂`. The place `p` remains in the type of
places, but it is isolated and never marked. Hence the reduced net is not itself an `IsWFNet`,
since `p` is not on a path from the source. `PetriNet.fuseDelete` deletes `p`
(`Cslib.Computability.PetriNets.RemovePlace`), and the result is a workflow net again.

Everything that the reduction needs about the series is that `t₂` *drains* `p` (`IsDrain`): `t₂`
consumes a single token of `p` and nothing else, and no other transition consumes from `p`. The
uniqueness of the producer `t₁` is not needed: the results hold as soon as some transition produces
into `p` (for liveness and soundness), and they apply to the fusion of series places in
`Cslib.Computability.PetriNets.SeriesPlaceReduction`.

The main results are stated for an initial marking `M₀` with `M₀ p = 0`. For a marking with tokens
in `p`, the `_collapse_iff` variants state them at `collapse M₀`, to which `M₀` is weakly
bisimilar (`PetriNet.IsDrain.weakBisimilar_collapse`) and trace equivalent for weak traces
(`PetriNet.IsDrain.traceEq_saturate_collapse`).

## Main definitions

- `PetriNet.IsDrain`: the transition `t` is the only consumer of `p`, and moves single tokens of
  `p` to its postset.
- `PetriNet.IsSeries`: `t₁ → p → t₂` is a series of transitions.
- `PetriNet.collapse`: fire `t₂` as often as possible, which empties `p`.
- `PetriNet.fuse`: the reduced net, in which `p` is isolated.
- `PetriNet.fuseDelete`: the reduced net without the place `p`.

## Main statements

- `PetriNet.IsDrain.weakBisimilar_collapse`: every marking of `N` is weakly bisimilar to its
  collapse in `fuse N t₂ p`, where `t₂` is the invisible action. This is the correspondence behind
  all of the following results.
- `PetriNet.IsDrain.reachable_fuse_iff`: from a marking with `p` empty, the markings with `p`
  empty reachable in `N` are those reachable in the reduced net.
- `PetriNet.IsDrain.exists_dead_fuse_iff`: `N` reaches a dead marking iff the reduced net does.
- `PetriNet.IsDrain.live_fuse_iff`: `N` is live iff the reduced net is, provided some transition
  produces into `p`.
- `PetriNet.IsDrain.bounded_fuse_iff`: `N` is bounded iff the reduced net is, provided `t₂`
  produces a token somewhere. (Without it, `N` can be unbounded in `p` alone.)
- `PetriNet.IsDrain.sound_fuse_iff`: a workflow net is sound iff its reduction is, which allows
  reducing before deciding soundness.
- `PetriNet.IsDrain.live_fuseDelete_iff`, ...: the same for the reduced net without `p`.
- `PetriNet.IsDrain.isWFNet_and_sound_fuseDelete`, `PetriNet.IsSeries.isWFNet_and_sound_fuseDelete`:
  the reduced net without `p` is a workflow net, and it is sound iff `N` is, so reducing before
  deciding soundness gives an equivalent question.

## References

* [T. Murata, *Petri nets: Properties, analysis and applications*][Murata1989], fusion of series
  transitions (FST).
* [W. M. P. van der Aalst, *The application of Petri nets to workflow management*,
  J. Circuits Syst. Comput. 8 (1998)][Aalst1998], reduction rules for workflow nets.
-/

@[expose] public section

namespace Cslib

namespace PetriNet

open LTS
open scoped PetriNet

variable {Place Transition : Type*} (N : PetriNet Place Transition)

/-- The marking in which every token of `p` has been replaced by a copy of the postset of `t₂`.
It is the marking reached by firing `t₂` as often as possible, when `t₂` consumes only from `p`. -/
noncomputable def collapse (t₂ : Transition) (p : Place) (M : Marking Place) : Marking Place :=
  M - Finsupp.single p (M p) + M p • t₂ •[N]

/-- The net obtained by fusing the series `t₁ → p → t₂`: the transition `t₂` is removed, and the
tokens that a transition puts in `p` are replaced by the postset of `t₂`. -/
noncomputable def fuse (t₂ : Transition) (p : Place) : PetriNet Place {t // t ≠ t₂} where
  pre t := •[N] t.1
  post t := N.collapse t₂ p (t.1 •[N])

/-- The net obtained by fusing the series `t₁ → p → t₂`, with the isolated place `p` deleted. -/
noncomputable def fuseDelete (t₂ : Transition) (p : Place) :
    PetriNet {q // q ≠ p} {t // t ≠ t₂} where
  pre t := Marking.drop p (•[N] t.1)
  post t := Marking.drop p (N.collapse t₂ p (t.1 •[N]))

section Collapse

variable {N} {t₂ : Transition} {p : Place}

/-- The tokens of `N.collapse t₂ p M` outside `p`. -/
theorem collapse_apply_of_ne {q : Place} (hq : q ≠ p) (M : Marking Place) :
    N.collapse t₂ p M q = M q + M p * (t₂ •[N]) q := by
  simp [collapse, hq]

/-- Collapsing is additive. -/
theorem collapse_add (M K : Marking Place) :
    N.collapse t₂ p (M + K) = N.collapse t₂ p M + N.collapse t₂ p K := by
  ext q
  by_cases hq : q = p
  · subst hq
    simp [collapse, add_smul]
  · simp [collapse, hq, add_smul]
    abel

/-- Collapsing a marking with `p` empty does nothing. -/
theorem collapse_of_apply_eq_zero {M : Marking Place} (hM : M p = 0) :
    N.collapse t₂ p M = M := by
  ext q
  by_cases hq : q = p
  · subst hq; simp [collapse, hM]
  · simp [collapse, hM]

/-- Collapsing does not remove tokens outside `p`. -/
theorem le_collapse {M : Marking Place} {q : Place} (hq : q ≠ p) :
    M q ≤ N.collapse t₂ p M q := by
  simp [collapse, hq]

/-- Every token of `p` yields a token in each place of the postset of `t₂`. -/
theorem le_collapse_of_post {M : Marking Place} {q : Place} (hq : 0 < (t₂ •[N]) q) :
    M p ≤ N.collapse t₂ p M q := by
  by_cases hqp : q = p
  · subst hqp
    simpa [collapse] using Nat.le_mul_of_pos_right _ hq
  · rw [collapse_apply_of_ne hqp]
    exact (Nat.le_mul_of_pos_right _ hq).trans (Nat.le_add_left _ _)

/-- A step of the reduced net from a marking with `p` empty is a step of `N` followed by
collapsing. -/
theorem fires_fuse {K K' : Marking Place} {t : {t // t ≠ t₂}}
    (hK : K p = 0) (hf : K [t⟩[N.fuse t₂ p] K') :
    ∃ K₂, K [t.1⟩[N] K₂ ∧ N.collapse t₂ p K₂ = K' := by
  obtain ⟨R, hK', rfl⟩ := hf
  have hR : R p = 0 := by
    have : K p = (•[N] t.1) p + R p := by rw [hK']; rfl
    omega
  refine ⟨R + t.1 •[N], ⟨R, hK', rfl⟩, ?_⟩
  rw [collapse_add, collapse_of_apply_eq_zero hR]
  rfl

/-- Invisible steps of a labelled marking graph are firing sequences. This is not a statement
about the nets alone, but about `HasTau (Option α)`, which is the `ε`-transition of
`Cslib.Computability.Automata.EpsilonNA.Basic`; it stays here to keep that import out of
`Cslib.Computability.PetriNets.Labelled`. -/
theorem reachable_of_τSTr {α : Type*} {ℓ : Transition → Option α} {M M' : Marking Place}
    (h : (N.labelledLts ℓ).τSTr M M') : M ⇝[N] M' := by
  induction h with
  | refl => exact .refl _ _
  | tail _ hr ih =>
    obtain ⟨t, -, hf⟩ := hr
    exact ih.trans hf.reachable

/-- Weak bisimilarity of a net with a reduced net on the transitions other than `t₂`, where `t₂` is
the invisible action. Here `c` sends a marking to the marking that stands for it in the reduced
net `N'`, which is reached from the marking by invisible steps (`hτ`). This is the argument behind
the fusion of series transitions and places and behind the elimination of self-loop transitions.

* `hhid`: firing `t₂` does not change `c`,
* `hvis`: a visible step of `N` is a step of `N'` between the images,
* `hlift`: a step of `N'` from an image is a step of `N` followed by `c`. -/
theorem weakBisimilar_of_collapse {t₂ : Transition} {N' : PetriNet Place {t // t ≠ t₂}}
    (c : Marking Place → Marking Place)
    (hτ : ∀ M, (N.labelledLts (hide t₂)).τSTr M (c M)) (hcc : ∀ M, c (c M) = c M)
    (hhid : ∀ {M M'}, M [t₂⟩[N] M' → c M' = c M)
    (hvis : ∀ {M M'} {t : {t // t ≠ t₂}}, M [t.1⟩[N] M' → (c M) [t⟩[N'] (c M'))
    (hlift : ∀ {M K'} {t : {t // t ≠ t₂}}, (c M) [t⟩[N'] K' → ∃ K₂, (c M) [t.1⟩[N] K₂ ∧ c K₂ = K')
    (M : Marking Place) :
    WeakBisimilarity (N.labelledLts (hide t₂)) (N'.labelledLts some) M (c M) := by
  refine ⟨fun M K => K = c M, rfl, isWeakBisimulation_iff_isSWBisimulation.2 ?_⟩
  rintro M K rfl μ
  constructor
  · rintro M₂ ⟨t, rfl, hf⟩
    by_cases ht : t = t₂
    · subst ht
      refine ⟨_, ?_, (hhid hf).symm⟩
      have : hide t t = HasTau.τ := hide_self t
      rw [this]
      exact .refl
    · exact ⟨_, .single ⟨⟨t, ht⟩, by simp [hide_of_ne ht], hvis hf⟩, rfl⟩
  · rintro K' ⟨t', rfl, hf⟩
    obtain ⟨K₂, hf₂, hc⟩ := hlift hf
    refine ⟨c K₂, .tr (hτ M) ⟨t'.1, ?_, hf₂⟩ (hτ K₂), ?_⟩
    · simp [hide_of_ne t'.2]
    · change K' = c (c K₂)
      rw [hcc, hc]

end Collapse

section Isolated

variable {Q : Type*} {A : PetriNet Q Transition} {r : Q}

/-- The restriction of the marking with a single token. -/
theorem token_drop {i : Q} (hi : i ≠ r) : (token i).drop r = token ⟨i, hi⟩ := by
  classical
  unfold token
  rw [Marking.drop_single]
  simp [hi]

/-- Deleting an isolated place preserves and reflects the soundness of a workflow net whose source
and sink are other places. -/
theorem IsIsolated.sound_removePlace_iff (h : A.IsIsolated r) {i o : Q} (hi : i ≠ r)
    (ho : o ≠ r) : (A.removePlace r).Sound ⟨i, hi⟩ ⟨o, ho⟩ ↔ A.Sound i o := by
  have hred : ∀ M₀ : Marking Q, A.RedundantPlace r M₀ := fun _ => h.redundantPlace
  have hp0 : ∀ M, token i ⇝[A] M → M r = 0 := fun M hM => by
    rw [h.apply_eq_of_reachable hM]
    exact token_apply_of_ne hi.symm
  have hop : token o r = 0 := token_apply_of_ne ho.symm
  have hti := token_drop hi
  have hto := token_drop ho
  constructor
  · intro hs
    refine ⟨fun M hM => ?_, fun M hM hle => ?_, fun t => ?_⟩
    · have hc := hs.completion (M.drop r) (by rw [← hti]; exact hM.drop)
      rw [← hto] at hc
      obtain ⟨M', hM', hd⟩ := ((hred _).reachable_drop_iff hM _).1 hc
      rw [Marking.eq_of_drop_eq (hp0 _ (hM.trans hM')) hop hd] at hM'
      exact hM'
    · refine Marking.eq_of_drop_eq (hp0 M hM) hop ?_
      rw [hto]
      refine hs.proper _ (by rw [← hti]; exact hM.drop) ?_
      rw [← hto]
      exact fun q => hle q.1
    · obtain ⟨K, hK, he⟩ := hs.noDead t
      rw [← hti] at hK
      obtain ⟨M, hM, rfl⟩ := ((hred _).reachable_drop_iff (Reachable.refl A _) K).1 hK
      exact ⟨M, hM, h.enabled_iff.1 he⟩
  · intro hs
    refine ⟨fun K hK => ?_, fun K hK hle => ?_, fun t => ?_⟩
    · rw [← hti] at hK
      obtain ⟨M, hM, rfl⟩ := ((hred _).reachable_drop_iff (Reachable.refl A _) K).1 hK
      rw [← hto]
      exact (hs.completion M hM).drop
    · rw [← hti] at hK
      obtain ⟨M, hM, rfl⟩ := ((hred _).reachable_drop_iff (Reachable.refl A _) K).1 hK
      rw [← hto]
      congr 1
      refine hs.proper M hM fun q => ?_
      by_cases hq : q = r
      · subst hq
        rw [hop]
        exact Nat.zero_le _
      · have := hle ⟨q, hq⟩
        rw [← hto] at this
        simpa using this
    · obtain ⟨M, hM, he⟩ := hs.noDead t
      rw [← hti]
      exact ⟨M.drop r, hM.drop, h.enabled_iff.2 he⟩

end Isolated

@[simp] theorem fuseDelete_pre (t₂ : Transition) (p : Place) (t : {t // t ≠ t₂}) :
    (N.fuseDelete t₂ p).pre t = Marking.drop p (•[N] t.1) := rfl

@[simp] theorem fuseDelete_post (t₂ : Transition) (p : Place) (t : {t // t ≠ t₂}) :
    (N.fuseDelete t₂ p).post t = Marking.drop p (N.collapse t₂ p (t.1 •[N])) := rfl

/-- The reduced net without `p` is the reduced net with the place `p` deleted. -/
theorem fuseDelete_eq (t₂ : Transition) (p : Place) :
    N.fuseDelete t₂ p = (N.fuse t₂ p).removePlace p := rfl

/-- `t` drains `p`: `t` is the only transition that consumes from `p`, it consumes a single token
of `p` and nothing else, and it does not produce into `p`. Every token in `p` can thus be moved by
`t` to the postset of `t` without any other effect. -/
structure IsDrain (t : Transition) (p : Place) : Prop where
  /-- The only input of `t` is one token in `p`. -/
  pre_eq : •[N] t = Finsupp.single p 1
  /-- The transition `t` does not produce into `p`. -/
  post_apply : (t •[N]) p = 0
  /-- No transition other than `t` consumes from `p`. -/
  pre_of_ne : ∀ t', t' ≠ t → (•[N] t') p = 0

/-- `t₁ → p → t₂` is a series of transitions: `t₂` drains `p`, and `t₁` produces a single token
into `p`. The two transitions are different (`IsSeries.ne`), as `t₂` does not produce into `p`.
(Murata also asks `t₁` to be the only producer, which the results do not need.) -/
structure IsSeries (t₁ t₂ : Transition) (p : Place) : Prop extends N.IsDrain t₂ p where
  /-- The transition `t₁` produces one token in `p`. -/
  post_left : (t₁ •[N]) p = 1

variable {N} {t₁ t₂ : Transition} {p : Place}

namespace IsDrain

/-- After collapsing, `p` is empty. -/
theorem collapse_apply_self (h : N.IsDrain t₂ p) (M : Marking Place) :
    N.collapse t₂ p M p = 0 := by
  simp [collapse, h.post_apply]

/-- Collapsing is idempotent. -/
theorem collapse_collapse (h : N.IsDrain t₂ p) (M : Marking Place) :
    N.collapse t₂ p (N.collapse t₂ p M) = N.collapse t₂ p M :=
  collapse_of_apply_eq_zero (h.collapse_apply_self M)

/-- Collapsing the preset of `t₂` gives its postset. -/
theorem collapse_single_add (h : N.IsDrain t₂ p) (R : Marking Place) :
    N.collapse t₂ p (•[N] t₂ + R) = t₂ •[N] + N.collapse t₂ p R := by
  have : N.collapse t₂ p (Finsupp.single p 1) = t₂ •[N] := by
    ext q
    by_cases hq : q = p
    · subst hq; simp [collapse, h.post_apply]
    · simp [collapse]
  rw [collapse_add, h.pre_eq, this]

/-- A step of `N` other than `t₂` is a step of the reduced net between the collapsed markings. -/
theorem fires_collapse (h : N.IsDrain t₂ p) {M M' : Marking Place} {t : Transition}
    (ht : t ≠ t₂) (hf : M [t⟩[N] M') :
    (N.collapse t₂ p M) [(⟨t, ht⟩ : {t // t ≠ t₂})⟩[N.fuse t₂ p] N.collapse t₂ p M' := by
  obtain ⟨R, rfl, rfl⟩ := hf
  refine ⟨N.collapse t₂ p R, ?_, ?_⟩
  · change N.collapse t₂ p (•[N] t + R) = •[N] t + N.collapse t₂ p R
    rw [collapse_add, collapse_of_apply_eq_zero (h.pre_of_ne t ht)]
  · change N.collapse t₂ p (R + t •[N]) = N.collapse t₂ p R + N.collapse t₂ p (t •[N])
    rw [collapse_add]

/-- Firing `t₂` does not change the collapse. -/
theorem collapse_eq_of_fires_right (h : N.IsDrain t₂ p) {M M' : Marking Place}
    (hf : M [t₂⟩[N] M') : N.collapse t₂ p M' = N.collapse t₂ p M := by
  obtain ⟨R, rfl, rfl⟩ := hf
  rw [h.collapse_single_add, collapse_add, collapse_of_apply_eq_zero (M := t₂ •[N]) h.post_apply,
    add_comm]

/-- Reachability in `N` gives reachability between the collapsed markings in the reduced net. -/
theorem reachable_collapse (h : N.IsDrain t₂ p) {M M' : Marking Place} (hr : M ⇝[N] M') :
    N.collapse t₂ p M ⇝[N.fuse t₂ p] N.collapse t₂ p M' :=
  hr.invariant (P := fun K => N.collapse t₂ p M ⇝[N.fuse t₂ p] N.collapse t₂ p K)
    (fun {K t K'} hf hK => by
      by_cases ht : t = t₂
      · subst ht
        rwa [h.collapse_eq_of_fires_right hf]
      · exact hK.trans (h.fires_collapse ht hf).reachable) (.refl _ _)

/-- Firing `t₂` as often as possible, which empties `p`, is a sequence of invisible steps, where
`t₂` is the hidden transition. -/
theorem τSTr_collapse (h : N.IsDrain t₂ p) (M : Marking Place) :
    (N.labelledLts (hide t₂)).τSTr M (N.collapse t₂ p M) := by
  suffices ∀ n (M : Marking Place), M p = n →
      (N.labelledLts (hide t₂)).τSTr M (N.collapse t₂ p M) from this _ M rfl
  intro n
  induction n with
  | zero =>
    intro M hM
    rw [collapse_of_apply_eq_zero hM]
    exact .refl
  | succ n ih =>
    intro M hM
    have hle : •[N] t₂ ≤ M := by
      rw [h.pre_eq, Finsupp.single_le_iff]
      omega
    have hf : M [t₂⟩[N] (M - •[N] t₂ + t₂ •[N]) :=
      ⟨M - •[N] t₂, (add_tsub_cancel_of_le hle).symm, rfl⟩
    have hp : (M - •[N] t₂ + t₂ •[N]) p = n := by
      rw [Finsupp.add_apply, h.post_apply, Finsupp.tsub_apply, h.pre_eq]
      simp [hM]
    rw [← h.collapse_eq_of_fires_right hf]
    exact .head ⟨t₂, by simp [HasTau.τ], hf⟩ (ih _ hp)

/-- Firing `t₂` as often as possible reaches the collapse. -/
theorem reachable_collapse_self (h : N.IsDrain t₂ p) (M : Marking Place) :
    M ⇝[N] N.collapse t₂ p M := by
  exact reachable_of_τSTr (ℓ := hide t₂) (h.τSTr_collapse M)

/-- Reachability in the reduced net lifts to `N`, and keeps `p` empty. -/
theorem reachable_fuse (h : N.IsDrain t₂ p) {M M' : Marking Place}
    (hr : M ⇝[N.fuse t₂ p] M') (hM : M p = 0) : M' p = 0 ∧ M ⇝[N] M' :=
  hr.invariant (P := fun K => K p = 0 ∧ M ⇝[N] K) (fun {K t K'} hf ⟨hK, hKr⟩ => by
    obtain ⟨K₂, hf₂, rfl⟩ := fires_fuse hK hf
    exact ⟨h.collapse_apply_self K₂,
      hKr.trans (hf₂.reachable.trans (h.reachable_collapse_self K₂))⟩)
    ⟨hM, .refl _ _⟩

/-- A transition other than `t₂` that is enabled in `M` is enabled in its collapse. -/
theorem enabled_collapse (h : N.IsDrain t₂ p) {M : Marking Place} {t : Transition}
    (ht : t ≠ t₂) (he : M [t⟩[N]) : (N.collapse t₂ p M) [t⟩[N] := fun q => by
  by_cases hq : q = p
  · subst hq
    simp [h.pre_of_ne t ht]
  · exact (he q).trans (le_collapse hq)

/-- A dead marking has no tokens in `p`, since `t₂` could consume them. -/
theorem apply_eq_zero_of_dead (h : N.IsDrain t₂ p) {M : Marking Place} (hd : N.Dead M) :
    M p = 0 := by
  by_contra hne
  refine dead_iff.1 hd t₂ ?_
  rw [Enabled, h.pre_eq, Finsupp.single_le_iff]
  omega

/-! ### Preservation of behavioural properties -/

/-- From a marking with `p` empty, the markings with `p` empty reachable in `N` are exactly the
markings reachable in the reduced net. -/
theorem reachable_fuse_iff (h : N.IsDrain t₂ p) {M₀ M : Marking Place} (h₀ : M₀ p = 0)
    (hM : M p = 0) : M₀ ⇝[N.fuse t₂ p] M ↔ M₀ ⇝[N] M := by
  refine ⟨fun hr => (h.reachable_fuse hr h₀).2, fun hr => ?_⟩
  have := h.reachable_collapse hr
  rwa [collapse_of_apply_eq_zero h₀, collapse_of_apply_eq_zero hM] at this

/-- Every marking reachable in `N` collapses to a marking reachable in the reduced net. -/
theorem reachable_fuse_collapse (h : N.IsDrain t₂ p) {M₀ M : Marking Place} (h₀ : M₀ p = 0)
    (hr : M₀ ⇝[N] M) : M₀ ⇝[N.fuse t₂ p] N.collapse t₂ p M := by
  have := h.reachable_collapse hr
  rwa [collapse_of_apply_eq_zero h₀] at this

/-- A marking with `p` empty is dead in the reduced net iff it is dead in `N`. -/
theorem dead_fuse_iff (h : N.IsDrain t₂ p) {M : Marking Place} (hM : M p = 0) :
    (N.fuse t₂ p).Dead M ↔ N.Dead M := by
  rw [dead_iff, dead_iff]
  refine ⟨fun hd t he => ?_, fun hd t' he => hd t'.1 he⟩
  by_cases ht : t = t₂
  · subst ht
    rw [Enabled, h.pre_eq, Finsupp.single_le_iff] at he
    omega
  · exact hd ⟨t, ht⟩ he

/-- The reduction preserves the reachability of dead markings, hence deadlock-freedom. -/
theorem exists_dead_fuse_iff (h : N.IsDrain t₂ p) {M₀ : Marking Place} (h₀ : M₀ p = 0) :
    (∃ M, M₀ ⇝[N.fuse t₂ p] M ∧ (N.fuse t₂ p).Dead M) ↔ ∃ M, M₀ ⇝[N] M ∧ N.Dead M := by
  constructor
  · rintro ⟨M, hr, hd⟩
    obtain ⟨hM, hr'⟩ := h.reachable_fuse hr h₀
    exact ⟨M, hr', (h.dead_fuse_iff hM).1 hd⟩
  · rintro ⟨M, hr, hd⟩
    have hM := h.apply_eq_zero_of_dead hd
    refine ⟨M, (h.reachable_fuse_iff h₀ hM).2 hr, (h.dead_fuse_iff hM).2 hd⟩

/-- The reduction preserves deadlock-freedom. -/
theorem deadlockFree_fuse_iff (h : N.IsDrain t₂ p) {M₀ : Marking Place} (h₀ : M₀ p = 0) :
    (∀ M, M₀ ⇝[N.fuse t₂ p] M → ¬ (N.fuse t₂ p).Dead M) ↔ ∀ M, M₀ ⇝[N] M → ¬ N.Dead M :=
  deadlockFree_congr (h.exists_dead_fuse_iff h₀)

/-- After a transition that produces into `p` has fired, `t₂` is enabled. -/
theorem enabled_right (h : N.IsDrain t₂ p) (ht : 0 < (t₁ •[N]) p) {M M' : Marking Place}
    (hf : M [t₁⟩[N] M') : M' [t₂⟩[N] := by
  obtain ⟨R, -, rfl⟩ := hf
  rw [Enabled, h.pre_eq, Finsupp.single_le_iff, Finsupp.add_apply]
  omega

/-- The drained transition `t₂` does not produce into `p`, so it is not a producer. -/
theorem ne_of_post (h : N.IsDrain t₂ p) (ht : 0 < (t₁ •[N]) p) : t₁ ≠ t₂ := fun e => by
  subst e
  simp [h.post_apply] at ht

/-- A transition other than `t₂` is live in the reduced net iff it is live in `N`. -/
theorem liveAt_fuse_iff_of_ne (h : N.IsDrain t₂ p) {M₀ : Marking Place} (h₀ : M₀ p = 0)
    {t : Transition} (ht : t ≠ t₂) :
    (N.fuse t₂ p).LiveAt M₀ ⟨t, ht⟩ ↔ N.LiveAt M₀ t := by
  constructor
  · intro hl M hM
    obtain ⟨M', hr, he⟩ := hl _ (h.reachable_fuse_collapse h₀ hM)
    obtain ⟨-, hr'⟩ := h.reachable_fuse hr (h.collapse_apply_self M)
    exact ⟨M', (h.reachable_collapse_self M).trans hr', he⟩
  · intro hl M hM
    obtain ⟨hM₁, hM₂⟩ := h.reachable_fuse hM h₀
    obtain ⟨M', hr, he⟩ := hl M hM₂
    have hc := h.reachable_collapse hr
    rw [collapse_of_apply_eq_zero hM₁] at hc
    exact ⟨_, hc, h.enabled_collapse ht he⟩

/-- Liveness is preserved by the reduction, in both directions. Some transition has to produce
into `p`, as the transition `t₂` is live only if `p` gets marked. -/
theorem live_fuse_iff (h : N.IsDrain t₂ p) {M₀ : Marking Place} (h₀ : M₀ p = 0)
    (hprod : ∃ t₁, 0 < (t₁ •[N]) p) : (N.fuse t₂ p).Live M₀ ↔ N.Live M₀ := by
  obtain ⟨t₁, ht₁⟩ := hprod
  have hne := h.ne_of_post ht₁
  constructor
  · intro hl t
    by_cases ht : t = t₂
    · subst ht
      intro M hM
      obtain ⟨M₁, hr, he⟩ := (h.liveAt_fuse_iff_of_ne h₀ hne).1 (hl ⟨t₁, hne⟩) M hM
      obtain ⟨M₂, hf⟩ := enabled_iff_exists_fires.1 he
      exact ⟨M₂, hr.trans hf.reachable, h.enabled_right ht₁ hf⟩
    · exact (h.liveAt_fuse_iff_of_ne h₀ ht).1 (hl ⟨t, ht⟩)
  · intro hl t'
    exact (h.liveAt_fuse_iff_of_ne h₀ t'.2).2 (hl t'.1)

/-- A `k`-bounded net stays `k`-bounded after the reduction. -/
theorem kBounded_fuse (h : N.IsDrain t₂ p) {M₀ : Marking Place} (h₀ : M₀ p = 0) {k : ℕ}
    (hk : N.KBounded M₀ k) : (N.fuse t₂ p).KBounded M₀ k :=
  fun M hM => hk M (h.reachable_fuse hM h₀).2

/-- If `t₂` produces a token somewhere, boundedness of the reduced net implies boundedness of `N`:
tokens in `p` are counted in the postset of `t₂`. -/
theorem kBounded_of_fuse (h : N.IsDrain t₂ p) {M₀ : Marking Place} (h₀ : M₀ p = 0) {k : ℕ}
    (hpost : ∃ q, 0 < (t₂ •[N]) q) (hk : (N.fuse t₂ p).KBounded M₀ k) : N.KBounded M₀ k := by
  obtain ⟨q₀, hq₀⟩ := hpost
  intro M hM q
  have hc := hk _ (h.reachable_fuse_collapse h₀ hM)
  by_cases hq : q = p
  · subst hq
    exact (le_collapse_of_post hq₀).trans (hc q₀)
  · exact (le_collapse hq).trans (hc q)

/-- `k`-boundedness is preserved by the reduction when `t₂` produces a token somewhere. -/
theorem kBounded_fuse_iff (h : N.IsDrain t₂ p) {M₀ : Marking Place} (h₀ : M₀ p = 0) {k : ℕ}
    (hpost : ∃ q, 0 < (t₂ •[N]) q) : (N.fuse t₂ p).KBounded M₀ k ↔ N.KBounded M₀ k :=
  ⟨h.kBounded_of_fuse h₀ hpost, h.kBounded_fuse h₀⟩

/-- Boundedness is preserved by the reduction when `t₂` produces a token somewhere. -/
theorem bounded_fuse_iff (h : N.IsDrain t₂ p) {M₀ : Marking Place} (h₀ : M₀ p = 0)
    (hpost : ∃ q, 0 < (t₂ •[N]) q) : (N.fuse t₂ p).Bounded M₀ ↔ N.Bounded M₀ :=
  exists_congr fun _ => h.kBounded_fuse_iff h₀ hpost

/-- Safeness is preserved by the reduction when `t₂` produces a token somewhere. -/
theorem safe_fuse_iff (h : N.IsDrain t₂ p) {M₀ : Marking Place} (h₀ : M₀ p = 0)
    (hpost : ∃ q, 0 < (t₂ •[N]) q) : (N.fuse t₂ p).Safe M₀ ↔ N.Safe M₀ :=
  h.kBounded_fuse_iff h₀ hpost

/-! ### Soundness of workflow nets -/

/-- Fusing a series of transitions preserves and reflects the soundness of a workflow net with
source `i` and sink `o`. The transition `t₂` has to produce a token somewhere, as it does in
every workflow net, and some transition has to produce into `p`. -/
theorem sound_fuse_iff (h : N.IsDrain t₂ p) {i o : Place} (hi : i ≠ p) (ho : o ≠ p)
    (hpost : ∃ q, 0 < (t₂ •[N]) q) (hprod : ∃ t₁, 0 < (t₁ •[N]) p) :
    (N.fuse t₂ p).Sound i o ↔ N.Sound i o := by
  obtain ⟨t₁, ht₁⟩ := hprod
  have hne := h.ne_of_post ht₁
  have h₀ : token i p = 0 := token_apply_of_ne hi.symm
  have hop : token o p = 0 := token_apply_of_ne ho.symm
  have hcol_o : N.collapse t₂ p (token o) = token o := collapse_of_apply_eq_zero hop
  constructor
  · intro hs
    refine ⟨fun M hM => ?_, fun M hM hle => ?_, fun t => ?_⟩
    · have hc := hs.completion _ (h.reachable_fuse_collapse h₀ hM)
      exact (h.reachable_collapse_self M).trans
        (h.reachable_fuse (M := N.collapse t₂ p M) hc (h.collapse_apply_self M)).2
    · have hle' : token o ≤ N.collapse t₂ p M := fun q => by
        by_cases hq : q = o
        · subst hq
          exact (hle q).trans (le_collapse ho)
        · simp [token_apply_of_ne hq]
      have hcM := hs.proper _ (h.reachable_fuse_collapse h₀ hM) hle'
      have hMp : M p = 0 := by
        obtain ⟨q₀, hq₀⟩ := hpost
        have h1 := le_collapse_of_post (N := N) (M := M) (p := p) hq₀
        rw [hcM] at h1
        by_cases hq : q₀ = o
        · subst hq
          have h2 := collapse_apply_of_ne (N := N) (t₂ := t₂) ho M
          rw [hcM] at h2
          have h3 := hle q₀
          have h4 := Nat.le_mul_of_pos_right (M p) hq₀
          simp only [token_apply_self] at h2 h3
          omega
        · rw [token_apply_of_ne hq] at h1
          omega
      rw [collapse_of_apply_eq_zero hMp] at hcM
      exact hcM
    · by_cases ht : t = t₂
      · rw [ht]
        obtain ⟨M, hM, he⟩ := hs.noDead ⟨t₁, hne⟩
        obtain ⟨M', hf⟩ := enabled_iff_exists_fires.1 (show M [t₁⟩[N] from he)
        exact ⟨M', (h.reachable_fuse hM h₀).2.trans hf.reachable, h.enabled_right ht₁ hf⟩
      · obtain ⟨M, hM, he⟩ := hs.noDead ⟨t, ht⟩
        exact ⟨M, (h.reachable_fuse hM h₀).2, he⟩
  · intro hs
    refine ⟨fun M hM => ?_, fun M hM hle => ?_, fun t => ?_⟩
    · obtain ⟨hM₁, hM₂⟩ := h.reachable_fuse hM h₀
      have hc := h.reachable_collapse (hs.completion M hM₂)
      rwa [collapse_of_apply_eq_zero hM₁, hcol_o] at hc
    · exact hs.proper M (h.reachable_fuse hM h₀).2 hle
    · obtain ⟨M, hM, he⟩ := hs.noDead t.1
      exact ⟨N.collapse t₂ p M, h.reachable_fuse_collapse h₀ hM, h.enabled_collapse t.2 he⟩

/-! ### The reduction as a weak bisimulation -/

/-- Every marking of `N` is weakly bisimilar to its collapse in the reduced net, where `t₂` is the
invisible action. The reduction preserves the observable behaviour, and thereby everything that
weak bisimilarity preserves. -/
theorem weakBisimilar_collapse (h : N.IsDrain t₂ p) (M : Marking Place) :
    WeakBisimilarity (N.labelledLts (hide t₂)) ((N.fuse t₂ p).labelledLts some)
      M (N.collapse t₂ p M) :=
  weakBisimilar_of_collapse (N.collapse t₂ p) h.τSTr_collapse h.collapse_collapse
    (fun hf => h.collapse_eq_of_fires_right hf) (fun {_ _ t} hf => h.fires_collapse t.2 hf)
    (fun hf => fires_fuse (h.collapse_apply_self _) hf) M

/-- Every marking of `N` has the same weak traces as its collapse in the reduced net: the traces of
the saturated marking graphs, in which `t₂` is invisible. -/
theorem traceEq_saturate_collapse (h : N.IsDrain t₂ p) (M : Marking Place) :
    M ~tr[(N.labelledLts (hide t₂)).saturate, ((N.fuse t₂ p).labelledLts some).saturate]
      (N.collapse t₂ p M) := by
  obtain ⟨r, hr, hb⟩ := h.weakBisimilar_collapse M
  exact hb.traceEq hr

/-! ### Markings with tokens in `p`

The results above are for markings with `p` empty. For an arbitrary marking `M₀`, apply them to
`N.collapse t₂ p M₀`, which `M₀` reaches in `N` by firing `t₂`, and which has the same behaviour.
Soundness needs no such statement, as the initial marking of a workflow net has a single token in
its source, which is not `p`. -/

/-- A marking with `p` empty is reachable from the collapse of `M₀` exactly when it is reachable
from `M₀`. -/
theorem reachable_collapse_iff (h : N.IsDrain t₂ p) {M₀ M : Marking Place} (hM : M p = 0) :
    N.collapse t₂ p M₀ ⇝[N] M ↔ M₀ ⇝[N] M := by
  refine ⟨fun hr => (h.reachable_collapse_self M₀).trans hr, fun hr => ?_⟩
  have := h.reachable_collapse hr
  rw [collapse_of_apply_eq_zero hM] at this
  exact (h.reachable_fuse this (h.collapse_apply_self M₀)).2

/-- The collapse of a marking reachable from `M₀` is reachable from the collapse of `M₀`. -/
theorem reachable_collapse_collapse (h : N.IsDrain t₂ p) {M₀ M : Marking Place}
    (hr : M₀ ⇝[N] M) : N.collapse t₂ p M₀ ⇝[N] N.collapse t₂ p M :=
  (h.reachable_collapse_iff (h.collapse_apply_self M)).2 (hr.trans (h.reachable_collapse_self M))

/-- The collapse of `M₀` has the same reachable dead markings as `M₀`. -/
theorem exists_dead_collapse_iff (h : N.IsDrain t₂ p) {M₀ : Marking Place} :
    (∃ M, N.collapse t₂ p M₀ ⇝[N] M ∧ N.Dead M) ↔ ∃ M, M₀ ⇝[N] M ∧ N.Dead M := by
  refine ⟨fun ⟨M, hr, hd⟩ => ⟨M, (h.reachable_collapse_self M₀).trans hr, hd⟩,
    fun ⟨M, hr, hd⟩ => ⟨M, ?_, hd⟩⟩
  exact (h.reachable_collapse_iff (h.apply_eq_zero_of_dead hd)).2 hr

/-- `N` is live at the collapse of `M₀` iff it is live at `M₀`. -/
theorem live_collapse_iff (h : N.IsDrain t₂ p) {M₀ : Marking Place} :
    N.Live (N.collapse t₂ p M₀) ↔ N.Live M₀ := by
  refine ⟨fun hl t M hM => ?_, fun hl t M hM => hl t M ((h.reachable_collapse_self M₀).trans hM)⟩
  obtain ⟨M', hr, he⟩ := hl t _ (h.reachable_collapse_collapse hM)
  exact ⟨M', (h.reachable_collapse_self M).trans hr, he⟩

/-- `N` is `k`-bounded at the collapse of `M₀` iff it is `k`-bounded at `M₀`, if `t₂` produces a
token somewhere. -/
theorem kBounded_collapse_iff (h : N.IsDrain t₂ p) {M₀ : Marking Place} {k : ℕ}
    (hpost : ∃ q, 0 < (t₂ •[N]) q) : N.KBounded (N.collapse t₂ p M₀) k ↔ N.KBounded M₀ k := by
  obtain ⟨q₀, hq₀⟩ := hpost
  refine ⟨fun hk M hM q => ?_,
    fun hk M hM => hk M ((h.reachable_collapse_self M₀).trans hM)⟩
  have hc := hk _ (h.reachable_collapse_collapse hM)
  by_cases hq : q = p
  · subst hq
    exact (le_collapse_of_post hq₀).trans (hc q₀)
  · exact (le_collapse hq).trans (hc q)

/-- `N` is bounded at the collapse of `M₀` iff it is bounded at `M₀`, if `t₂` produces a token
somewhere. -/
theorem bounded_collapse_iff (h : N.IsDrain t₂ p) {M₀ : Marking Place}
    (hpost : ∃ q, 0 < (t₂ •[N]) q) : N.Bounded (N.collapse t₂ p M₀) ↔ N.Bounded M₀ :=
  exists_congr fun _ => h.kBounded_collapse_iff hpost

/-- Reachability of markings with `p` empty, from an arbitrary marking: `M₀` reaches `M` in `N`
iff its collapse reaches `M` in the reduced net. -/
theorem reachable_fuse_collapse_iff (h : N.IsDrain t₂ p) {M₀ M : Marking Place} (hM : M p = 0) :
    N.collapse t₂ p M₀ ⇝[N.fuse t₂ p] M ↔ M₀ ⇝[N] M := by
  rw [← h.reachable_collapse_iff hM]
  exact h.reachable_fuse_iff (h.collapse_apply_self M₀) hM

/-- The reduced net reaches a dead marking from the collapse of `M₀` iff `N` does from `M₀`. -/
theorem exists_dead_fuse_collapse_iff (h : N.IsDrain t₂ p) {M₀ : Marking Place} :
    (∃ M, N.collapse t₂ p M₀ ⇝[N.fuse t₂ p] M ∧ (N.fuse t₂ p).Dead M) ↔
      ∃ M, M₀ ⇝[N] M ∧ N.Dead M :=
  (h.exists_dead_fuse_iff (h.collapse_apply_self M₀)).trans h.exists_dead_collapse_iff

/-- The reduced net is deadlock-free from the collapse of `M₀` iff `N` is from `M₀`. -/
theorem deadlockFree_fuse_collapse_iff (h : N.IsDrain t₂ p) {M₀ : Marking Place} :
    (∀ M, N.collapse t₂ p M₀ ⇝[N.fuse t₂ p] M → ¬ (N.fuse t₂ p).Dead M) ↔
      ∀ M, M₀ ⇝[N] M → ¬ N.Dead M :=
  deadlockFree_congr h.exists_dead_fuse_collapse_iff

/-- The reduced net is live at the collapse of `M₀` iff `N` is live at `M₀`. -/
theorem live_fuse_collapse_iff (h : N.IsDrain t₂ p) {M₀ : Marking Place}
    (hprod : ∃ t₁, 0 < (t₁ •[N]) p) : (N.fuse t₂ p).Live (N.collapse t₂ p M₀) ↔ N.Live M₀ :=
  (h.live_fuse_iff (h.collapse_apply_self M₀) hprod).trans h.live_collapse_iff

/-- The reduced net is bounded at the collapse of `M₀` iff `N` is bounded at `M₀`. -/
theorem bounded_fuse_collapse_iff (h : N.IsDrain t₂ p) {M₀ : Marking Place}
    (hpost : ∃ q, 0 < (t₂ •[N]) q) :
    (N.fuse t₂ p).Bounded (N.collapse t₂ p M₀) ↔ N.Bounded M₀ :=
  (h.bounded_fuse_iff (h.collapse_apply_self M₀) hpost).trans (h.bounded_collapse_iff hpost)

/-! ### Deleting the isolated place -/

/-- The reduced net has `p` isolated. -/
theorem isIsolated_fuse (h : N.IsDrain t₂ p) : (N.fuse t₂ p).IsIsolated p :=
  fun t => ⟨h.pre_of_ne t.1 t.2, h.collapse_apply_self _⟩

/-- From a marking with `p` empty, the markings with `p` empty reachable in `N` are those
reachable in the reduced net without `p`. -/
theorem reachable_fuseDelete_iff (h : N.IsDrain t₂ p) {M₀ M : Marking Place} (h₀ : M₀ p = 0)
    (hM : M p = 0) :
    (M₀.drop p) ⇝[N.fuseDelete t₂ p] (M.drop p) ↔ M₀ ⇝[N] M := by
  rw [← h.reachable_fuse_iff h₀ hM, fuseDelete_eq,
    (h.isIsolated_fuse.redundantPlace (M₀ := M₀)).reachable_drop_iff (Reachable.refl _ M₀)]
  constructor
  · rintro ⟨M', hr, hd⟩
    have := (h.reachable_fuse hr h₀).1
    rwa [Marking.eq_of_drop_eq this hM hd] at hr
  · intro hr
    exact ⟨M, hr, rfl⟩

/-- The reduction preserves the reachability of dead markings. -/
theorem exists_dead_fuseDelete_iff (h : N.IsDrain t₂ p) {M₀ : Marking Place} (h₀ : M₀ p = 0) :
    (∃ K, (M₀.drop p) ⇝[N.fuseDelete t₂ p] K ∧ (N.fuseDelete t₂ p).Dead K) ↔
      ∃ M, M₀ ⇝[N] M ∧ N.Dead M := by
  rw [← h.exists_dead_fuse_iff h₀, fuseDelete_eq]
  have hr := h.isIsolated_fuse.redundantPlace (M₀ := M₀)
  constructor
  · rintro ⟨K, hK, hd⟩
    obtain ⟨M, hM, rfl⟩ := (hr.reachable_drop_iff (Reachable.refl _ M₀) K).1 hK
    exact ⟨M, hM, (hr.dead_iff hM).2 hd⟩
  · rintro ⟨M, hM, hd⟩
    exact ⟨M.drop p, hM.drop, (hr.dead_iff hM).1 hd⟩

/-- The reduction preserves deadlock-freedom. -/
theorem deadlockFree_fuseDelete_iff (h : N.IsDrain t₂ p) {M₀ : Marking Place} (h₀ : M₀ p = 0) :
    (∀ K, (M₀.drop p) ⇝[N.fuseDelete t₂ p] K → ¬ (N.fuseDelete t₂ p).Dead K) ↔
      ∀ M, M₀ ⇝[N] M → ¬ N.Dead M :=
  deadlockFree_congr (h.exists_dead_fuseDelete_iff h₀)

/-- Deleting the isolated place preserves liveness. -/
theorem live_fuseDelete_iff (h : N.IsDrain t₂ p) {M₀ : Marking Place} (h₀ : M₀ p = 0)
    (hprod : ∃ t₁, 0 < (t₁ •[N]) p) :
    (N.fuseDelete t₂ p).Live (M₀.drop p) ↔ N.Live M₀ := by
  rw [← h.live_fuse_iff h₀ hprod, fuseDelete_eq]
  exact (h.isIsolated_fuse.redundantPlace (M₀ := M₀)).live_iff.symm

/-- Deleting the isolated place preserves boundedness, if `t₂` produces a token somewhere. -/
theorem bounded_fuseDelete_iff (h : N.IsDrain t₂ p) {M₀ : Marking Place} (h₀ : M₀ p = 0)
    (hpost : ∃ q, 0 < (t₂ •[N]) q) :
    (N.fuseDelete t₂ p).Bounded (M₀.drop p) ↔ N.Bounded M₀ := by
  rw [← h.bounded_fuse_iff h₀ hpost, fuseDelete_eq]
  exact ((h.isIsolated_fuse.redundantPlace (M₀ := M₀)).bounded_iff_of_post_le_pre
    (fun t => by rw [(h.isIsolated_fuse t).2]; exact Nat.zero_le _)).symm

/-- Reachability of markings with `p` empty in the reduced net without `p`, from an arbitrary
marking. -/
theorem reachable_fuseDelete_collapse_iff (h : N.IsDrain t₂ p) {M₀ M : Marking Place}
    (hM : M p = 0) :
    ((N.collapse t₂ p M₀).drop p) ⇝[N.fuseDelete t₂ p] (M.drop p) ↔ M₀ ⇝[N] M :=
  (h.reachable_fuseDelete_iff (h.collapse_apply_self M₀) hM).trans
    (h.reachable_collapse_iff hM)

/-- The reduction preserves the reachability of dead markings, from an arbitrary marking. -/
theorem exists_dead_fuseDelete_collapse_iff (h : N.IsDrain t₂ p) {M₀ : Marking Place} :
    (∃ K, ((N.collapse t₂ p M₀).drop p) ⇝[N.fuseDelete t₂ p] K ∧
        (N.fuseDelete t₂ p).Dead K) ↔ ∃ M, M₀ ⇝[N] M ∧ N.Dead M :=
  (h.exists_dead_fuseDelete_iff (h.collapse_apply_self M₀)).trans h.exists_dead_collapse_iff

/-- The reduction preserves deadlock-freedom, from an arbitrary marking. -/
theorem deadlockFree_fuseDelete_collapse_iff (h : N.IsDrain t₂ p) {M₀ : Marking Place} :
    (∀ K, ((N.collapse t₂ p M₀).drop p) ⇝[N.fuseDelete t₂ p] K →
        ¬ (N.fuseDelete t₂ p).Dead K) ↔ ∀ M, M₀ ⇝[N] M → ¬ N.Dead M :=
  deadlockFree_congr h.exists_dead_fuseDelete_collapse_iff

/-- The reduction without `p` preserves liveness, from an arbitrary marking. -/
theorem live_fuseDelete_collapse_iff (h : N.IsDrain t₂ p) {M₀ : Marking Place}
    (hprod : ∃ t₁, 0 < (t₁ •[N]) p) :
    (N.fuseDelete t₂ p).Live ((N.collapse t₂ p M₀).drop p) ↔ N.Live M₀ :=
  (h.live_fuseDelete_iff (h.collapse_apply_self M₀) hprod).trans h.live_collapse_iff

/-- The reduction without `p` preserves boundedness, from an arbitrary marking. -/
theorem bounded_fuseDelete_collapse_iff (h : N.IsDrain t₂ p) {M₀ : Marking Place}
    (hpost : ∃ q, 0 < (t₂ •[N]) q) :
    (N.fuseDelete t₂ p).Bounded ((N.collapse t₂ p M₀).drop p) ↔ N.Bounded M₀ :=
  (h.bounded_fuseDelete_iff (h.collapse_apply_self M₀) hpost).trans (h.bounded_collapse_iff hpost)

/-- Fusing a series and deleting the isolated place preserves and reflects the soundness of a
workflow net. -/
theorem sound_fuseDelete_iff (h : N.IsDrain t₂ p) {i o : Place} (hi : i ≠ p) (ho : o ≠ p)
    (hpost : ∃ q, 0 < (t₂ •[N]) q) (hprod : ∃ t₁, 0 < (t₁ •[N]) p) :
    (N.fuseDelete t₂ p).Sound ⟨i, hi⟩ ⟨o, ho⟩ ↔ N.Sound i o := by
  rw [fuseDelete_eq, h.isIsolated_fuse.sound_removePlace_iff hi ho]
  exact h.sound_fuse_iff hi ho hpost hprod

/-- A path of `N` between nodes other than `p` and `t₂` contracts to a path of the reduced net
without `p`: a visit to `p` and `t₂` is replaced by the arcs from the producers of `p` to the
postset of `t₂`. -/
theorem reflTransGen_arc_fuseDelete (h : N.IsDrain t₂ p)
    {x y : {q // q ≠ p} ⊕ {t // t ≠ t₂}}
    (hr : Relation.ReflTransGen N.Arc (Sum.map Subtype.val Subtype.val x)
      (Sum.map Subtype.val Subtype.val y)) :
    Relation.ReflTransGen (N.fuseDelete t₂ p).Arc x y := by
  -- `Prod` says that some transition that produces into `p` is reached from `x`
  let R := Relation.ReflTransGen (N.fuseDelete t₂ p).Arc x
  let Prod : Prop := ∃ t, ∃ ht : t ≠ t₂, 0 < (t •[N]) p ∧ R (.inr ⟨t, ht⟩)
  have key : ∀ z, Relation.ReflTransGen N.Arc (Sum.map Subtype.val Subtype.val x) z →
      match z with
      | .inl q => (∀ hq : q ≠ p, R (.inl ⟨q, hq⟩)) ∧ (q = p → Prod)
      | .inr t => (∀ ht : t ≠ t₂, R (.inr ⟨t, ht⟩)) ∧ (t = t₂ → Prod) := by
    intro z hz
    induction hz with
    | refl =>
      rcases x with ⟨q, hq⟩ | ⟨t, ht⟩
      · exact ⟨fun _ => .refl, fun e => absurd e hq⟩
      · exact ⟨fun _ => .refl, fun e => absurd e ht⟩
    | @tail z z' _ hxy ih =>
      rcases z with q | t <;> rcases z' with q' | t'
      · exact hxy.elim
      · change 0 < (•[N] t') q at hxy
        refine ⟨fun ht => ?_, fun e => ?_⟩
        · have hq : q ≠ p := fun e => by
            rw [e, h.pre_of_ne t' ht] at hxy
            exact lt_irrefl _ hxy
          exact (ih.1 hq).tail hxy
        · subst e
          refine ih.2 (by_contra fun hq => ?_)
          rw [h.pre_eq, Finsupp.single_eq_of_ne hq] at hxy
          exact lt_irrefl _ hxy
      · change 0 < (t •[N]) q' at hxy
        refine ⟨fun hq => ?_, fun e => ?_⟩
        · by_cases ht : t = t₂
          · obtain ⟨t₃, ht₃, hpt, hR⟩ := ih.2 ht
            rw [ht] at hxy
            refine hR.tail ?_
            change 0 < N.collapse t₂ p (t₃ •[N]) q'
            rw [collapse_apply_of_ne hq]
            exact Nat.add_pos_right _ (Nat.mul_pos hpt hxy)
          · refine (ih.1 ht).tail ?_
            change 0 < N.collapse t₂ p (t •[N]) q'
            rw [collapse_apply_of_ne hq]
            omega
        · rw [e] at hxy
          have ht : t ≠ t₂ := fun e' => by
            rw [e', h.post_apply] at hxy
            exact lt_irrefl _ hxy
          exact ⟨t, ht, hxy, ih.1 ht⟩
      · exact hxy.elim
  rcases y with ⟨q, hq⟩ | ⟨t, ht⟩
  · exact (key _ hr).1 hq
  · exact (key _ hr).1 ht

/-- The reduction preserves the workflow net structure once `p` is deleted. -/
theorem isWFNet_fuseDelete (h : N.IsDrain t₂ p) {i o : Place} (hN : N.IsWFNet i o) (hi : i ≠ p)
    (ho : o ≠ p) : (N.fuseDelete t₂ p).IsWFNet ⟨i, hi⟩ ⟨o, ho⟩ := by
  refine ⟨fun t => ?_, fun t => hN.no_output_sink t.1, fun n => ?_, fun n => ?_⟩
  · change N.collapse t₂ p (t.1 •[N]) i = 0
    rw [collapse_apply_of_ne hi, hN.no_input_source, hN.no_input_source]
    rfl
  · exact h.reflTransGen_arc_fuseDelete (hN.reach_from_source _)
  · exact h.reflTransGen_arc_fuseDelete (hN.reach_to_sink _)

/-- In a workflow net, the place drained by a transition is not the sink. -/
theorem ne_sink (h : N.IsDrain t₂ p) {i o : Place} (hN : N.IsWFNet i o) : o ≠ p := fun e => by
  have := hN.no_output_sink t₂
  rw [e, h.pre_eq] at this
  simp at this

/-- The reduce-then-decide pipeline for workflow nets: if `p` is drained by `t₂` and is not the
source, the net obtained by fusing and deleting `p` is a workflow net, and it is sound iff `N`
is. -/
theorem isWFNet_and_sound_fuseDelete (h : N.IsDrain t₂ p) {i o : Place} (hN : N.IsWFNet i o)
    (hi : i ≠ p) :
    (N.fuseDelete t₂ p).IsWFNet ⟨i, hi⟩ ⟨o, h.ne_sink hN⟩ ∧
      ((N.fuseDelete t₂ p).Sound ⟨i, hi⟩ ⟨o, h.ne_sink hN⟩ ↔ N.Sound i o) :=
  ⟨h.isWFNet_fuseDelete hN hi (h.ne_sink hN),
    h.sound_fuseDelete_iff hi (h.ne_sink hN) (hN.exists_post t₂) (hN.exists_producer hi.symm)⟩

end IsDrain

namespace IsSeries

/-- The producer `t₁` of a series puts a token into `p`. -/
theorem post_pos (h : N.IsSeries t₁ t₂ p) : 0 < (t₁ •[N]) p := by
  rw [h.post_left]
  exact Nat.one_pos

/-- The two transitions of a series are different. -/
theorem ne (h : N.IsSeries t₁ t₂ p) : t₁ ≠ t₂ := h.toIsDrain.ne_of_post h.post_pos

/-- In a workflow net, a place with a producer is not the source. -/
theorem ne_source (h : N.IsSeries t₁ t₂ p) {i o : Place} (hN : N.IsWFNet i o) : i ≠ p := fun e => by
  have h1 := hN.no_input_source t₁
  rw [e] at h1
  exact one_ne_zero (h.post_left.symm.trans h1)

/-- Liveness is preserved by fusing a series of transitions. -/
theorem live_fuse_iff (h : N.IsSeries t₁ t₂ p) {M₀ : Marking Place} (h₀ : M₀ p = 0) :
    (N.fuse t₂ p).Live M₀ ↔ N.Live M₀ :=
  h.toIsDrain.live_fuse_iff h₀ ⟨t₁, h.post_pos⟩

/-- Boundedness is preserved by fusing a series of transitions, if `t₂` produces a token
somewhere. -/
theorem bounded_fuse_iff (h : N.IsSeries t₁ t₂ p) {M₀ : Marking Place} (h₀ : M₀ p = 0)
    (hpost : ∃ q, 0 < (t₂ •[N]) q) : (N.fuse t₂ p).Bounded M₀ ↔ N.Bounded M₀ :=
  h.toIsDrain.bounded_fuse_iff h₀ hpost

/-- Soundness of a workflow net is preserved by fusing a series of transitions. -/
theorem sound_fuse_iff (h : N.IsSeries t₁ t₂ p) {i o : Place} (hi : i ≠ p) (ho : o ≠ p)
    (hpost : ∃ q, 0 < (t₂ •[N]) q) : (N.fuse t₂ p).Sound i o ↔ N.Sound i o :=
  h.toIsDrain.sound_fuse_iff hi ho hpost ⟨t₁, h.post_pos⟩

/-- For a workflow net, fusing a series of transitions and deleting `p` gives a workflow net, and
it is sound iff `N` is. -/
theorem isWFNet_and_sound_fuseDelete (h : N.IsSeries t₁ t₂ p) {i o : Place}
    (hN : N.IsWFNet i o) :
    (N.fuseDelete t₂ p).IsWFNet ⟨i, h.ne_source hN⟩ ⟨o, h.toIsDrain.ne_sink hN⟩ ∧
      ((N.fuseDelete t₂ p).Sound ⟨i, h.ne_source hN⟩ ⟨o, h.toIsDrain.ne_sink hN⟩ ↔
        N.Sound i o) :=
  h.toIsDrain.isWFNet_and_sound_fuseDelete hN (h.ne_source hN)

end IsSeries

end PetriNet

end Cslib
