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
(`Cslib.Computability.PetriNets.RemovePlace`), and the result is a workflow net again. The reduced
nets and the collapse of a marking are computable, and the side conditions are decidable.

Everything that the reduction needs about the series is that `t₂` *drains* `p` (`IsDrain`): `t₂`
consumes a single token of `p` and nothing else, and no other transition consumes from `p`. The
uniqueness of the producer `t₁` is not needed: the results hold as soon as some transition produces
into `p` (for liveness and soundness), and they apply to the fusion of series places in
`Cslib.Computability.PetriNets.SeriesPlaceReduction`.

The main results are stated for an initial marking `M₀` with `p ∉ M₀`. For a marking with tokens
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

/-- `t` drains `p`: `t` is the only transition that consumes from `p`, it consumes a single token
of `p` and nothing else, and it does not produce into `p`. Every token in `p` can thus be moved by
`t` to the postset of `t` without any other effect. -/
structure IsDrain (t : Transition) (p : Place) : Prop where
  /-- The only input of `t` is one token in `p`. -/
  pre_eq : •[N] t = {p}
  /-- The transition `t` does not produce into `p`. -/
  notMem_post : p ∉ t •[N]
  /-- No transition other than `t` consumes from `p`. -/
  notMem_pre : ∀ t', t' ≠ t → p ∉ •[N] t'

theorem isDrain_iff {t : Transition} {p : Place} :
    N.IsDrain t p ↔ •[N] t = {p} ∧ p ∉ t •[N] ∧ ∀ t', t' ≠ t → p ∉ •[N] t' :=
  ⟨fun h => ⟨h.1, h.2, h.3⟩, fun h => ⟨h.1, h.2.1, h.2.2⟩⟩

instance [DecidableEq Place] [DecidableEq Transition] [Fintype Transition] (t : Transition)
    (p : Place) : Decidable (N.IsDrain t p) :=
  decidable_of_iff _ N.isDrain_iff.symm

namespace IsDrain

variable {N} {t₁ t₂ : Transition} {p : Place}

/-- `t₂` is enabled exactly when `p` is marked. -/
theorem enabled_iff (h : N.IsDrain t₂ p) {M : Marking Place} : M [t₂⟩[N] ↔ p ∈ M := by
  rw [Enabled, h.pre_eq, Multiset.singleton_le]

/-- A dead marking has no tokens in `p`, since `t₂` could consume them. -/
theorem notMem_of_dead (h : N.IsDrain t₂ p) {M : Marking Place} (hd : N.Dead M) : p ∉ M :=
  fun hp => dead_iff.1 hd t₂ (h.enabled_iff.2 hp)

/-- After a transition that produces into `p` has fired, `t₂` is enabled. -/
theorem enabled_right (h : N.IsDrain t₂ p) (ht : p ∈ t₁ •[N]) {M M' : Marking Place}
    (hf : M [t₁⟩[N] M') : M' [t₂⟩[N] := by
  obtain ⟨R, -, rfl⟩ := hf
  exact h.enabled_iff.2 (Multiset.mem_add.2 (.inr ht))

/-- The drained transition `t₂` does not produce into `p`, so it is not a producer. -/
theorem ne_of_post (h : N.IsDrain t₂ p) (ht : p ∈ t₁ •[N]) : t₁ ≠ t₂ := fun e =>
  h.notMem_post (e ▸ ht)

/-- In a workflow net, the place drained by a transition is not the sink. -/
theorem ne_sink (h : N.IsDrain t₂ p) {i o : Place} (hN : N.IsWFNet i o) : o ≠ p := fun e =>
  hN.no_output_sink t₂ (by rw [h.pre_eq, e]; exact Multiset.mem_singleton_self p)

end IsDrain

variable {N}

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
theorem weakBisimilar_of_collapse [DecidableEq Transition] {t₂ : Transition}
    {N' : PetriNet Place {t // t ≠ t₂}} (c : Marking Place → Marking Place)
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

/-- The marking with a single token in `q` has no token in any other place. -/
theorem notMem_token {p q : Place} (h : p ≠ q) : p ∉ token q :=
  fun h' => h (Multiset.mem_singleton.1 h')

variable [DecidableEq Place]

variable (N) in
/-- The marking in which every token of `p` has been replaced by a copy of the postset of `t₂`.
It is the marking reached by firing `t₂` as often as possible, when `t₂` drains `p`. -/
def collapse (t₂ : Transition) (p : Place) (M : Marking Place) : Marking Place :=
  M.filter (· ≠ p) + M.count p • t₂ •[N]

variable (N) in
/-- The net obtained by fusing the series `t₁ → p → t₂`: the transition `t₂` is removed, and the
tokens that a transition puts in `p` are replaced by the postset of `t₂`. -/
def fuse (t₂ : Transition) (p : Place) : PetriNet Place {t // t ≠ t₂} where
  pre t := •[N] t.1
  post t := N.collapse t₂ p (t.1 •[N])

variable (N) in
/-- The net obtained by fusing the series `t₁ → p → t₂`, with the isolated place `p` deleted. -/
def fuseDelete (t₂ : Transition) (p : Place) : PetriNet {q // q ≠ p} {t // t ≠ t₂} :=
  (N.fuse t₂ p).removePlace p

variable (N) in
/-- `t₁ → p → t₂` is a series of transitions: `t₂` drains `p`, and `t₁` produces a single token
into `p`. The two transitions are different (`IsSeries.ne`), as `t₂` does not produce into `p`.
(Murata also asks `t₁` to be the only producer, which the results do not need.) -/
structure IsSeries (t₁ t₂ : Transition) (p : Place) : Prop extends N.IsDrain t₂ p where
  /-- The transition `t₁` produces one token in `p`. -/
  post_left : (t₁ •[N]).count p = 1

instance [DecidableEq Transition] [Fintype Transition] (t₁ t₂ : Transition) (p : Place) :
    Decidable (N.IsSeries t₁ t₂ p) :=
  decidable_of_iff (N.IsDrain t₂ p ∧ (t₁ •[N]).count p = 1)
    ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.1, h.2⟩⟩

@[simp] theorem fuse_pre (t₂ : Transition) (p : Place) (t : {t // t ≠ t₂}) :
    (N.fuse t₂ p).pre t = •[N] t.1 := rfl

@[simp] theorem fuse_post (t₂ : Transition) (p : Place) (t : {t // t ≠ t₂}) :
    (N.fuse t₂ p).post t = N.collapse t₂ p (t.1 •[N]) := rfl

/-- The reduced net without `p` is the reduced net with the place `p` deleted. -/
theorem fuseDelete_eq (t₂ : Transition) (p : Place) :
    N.fuseDelete t₂ p = (N.fuse t₂ p).removePlace p := rfl

@[simp] theorem fuseDelete_pre (t₂ : Transition) (p : Place) (t : {t // t ≠ t₂}) :
    (N.fuseDelete t₂ p).pre t = Marking.drop p (•[N] t.1) := rfl

@[simp] theorem fuseDelete_post (t₂ : Transition) (p : Place) (t : {t // t ≠ t₂}) :
    (N.fuseDelete t₂ p).post t = Marking.drop p (N.collapse t₂ p (t.1 •[N])) := rfl

section Collapse

variable {t₂ : Transition} {p : Place}

/-- The tokens of `N.collapse t₂ p M` outside `p`. -/
theorem count_collapse_of_ne {q : Place} (hq : q ≠ p) (M : Marking Place) :
    (N.collapse t₂ p M).count q = M.count q + M.count p * (t₂ •[N]).count q := by
  simp [collapse, hq]

/-- The places marked after collapsing: the marked places other than `p`, and the postset of `t₂`
if `p` is marked. -/
@[simp] theorem mem_collapse {M : Marking Place} {q : Place} :
    q ∈ N.collapse t₂ p M ↔ q ∈ M ∧ q ≠ p ∨ p ∈ M ∧ q ∈ t₂ •[N] := by
  simp [collapse, Multiset.mem_nsmul]

/-- Collapsing is additive. -/
theorem collapse_add (M K : Marking Place) :
    N.collapse t₂ p (M + K) = N.collapse t₂ p M + N.collapse t₂ p K := by
  simp only [collapse, Multiset.filter_add, Multiset.count_add, add_nsmul]
  abel

/-- Collapsing a marking with `p` empty does nothing. -/
theorem collapse_of_notMem {M : Marking Place} (hM : p ∉ M) : N.collapse t₂ p M = M := by
  rw [collapse, Multiset.count_eq_zero_of_notMem hM, zero_nsmul, add_zero,
    Multiset.filter_eq_self]
  exact fun q hq e => hM (e ▸ hq)

/-- Collapsing a single token of `p` gives the postset of `t₂`. -/
theorem collapse_singleton_self : N.collapse t₂ p {p} = t₂ •[N] := by
  simp [collapse]

/-- Collapsing does not remove tokens outside `p`. -/
theorem le_collapse_of_notMem {K M : Marking Place} (hK : p ∉ K) (h : K ≤ M) :
    K ≤ N.collapse t₂ p M :=
  calc K = K.filter (· ≠ p) :=
        (Multiset.filter_eq_self.2 fun q hq => by rintro rfl; exact hK hq).symm
    _ ≤ M.filter (· ≠ p) := Multiset.filter_le_filter _ h
    _ ≤ N.collapse t₂ p M := le_self_add

/-- Every token of `p` yields a token in each place of the postset of `t₂`. -/
theorem count_le_count_collapse_of_mem {M : Marking Place} {q : Place} (hq : q ∈ t₂ •[N]) :
    M.count p ≤ (N.collapse t₂ p M).count q := by
  have := Multiset.count_le_of_le q (le_add_self : M.count p • t₂ •[N] ≤ N.collapse t₂ p M)
  rw [Multiset.count_nsmul] at this
  exact (Nat.le_mul_of_pos_right _ (Multiset.count_pos.2 hq)).trans this

/-- A marking is `k`-bounded if its collapse is, provided `t₂` produces a token: a token in `p`
becomes a token in each place of the postset of `t₂`. -/
theorem count_le_of_collapse (hpost : t₂ •[N] ≠ 0) {M : Marking Place} {k : ℕ}
    (hc : ∀ q, (N.collapse t₂ p M).count q ≤ k) (q : Place) : M.count q ≤ k := by
  by_cases hq : q = p
  · obtain ⟨q₀, hq₀⟩ := Multiset.exists_mem_of_ne_zero hpost
    exact hq ▸ (count_le_count_collapse_of_mem hq₀).trans (hc q₀)
  · refine le_trans ?_ (hc q)
    rw [count_collapse_of_ne hq]
    exact Nat.le_add_right _ _

/-- A step of the reduced net from a marking with `p` empty is a step of `N` followed by
collapsing. -/
theorem fires_fuse {K K' : Marking Place} {t : {t // t ≠ t₂}}
    (hK : p ∉ K) (hf : K [t⟩[N.fuse t₂ p] K') :
    ∃ K₂, K [t.1⟩[N] K₂ ∧ N.collapse t₂ p K₂ = K' := by
  obtain ⟨R, rfl, rfl⟩ := hf
  refine ⟨R + t.1 •[N], ⟨R, rfl, rfl⟩, ?_⟩
  rw [collapse_add, collapse_of_notMem fun h => hK (Multiset.mem_add.2 (.inr h))]
  rfl

end Collapse

variable {t₁ t₂ : Transition} {p : Place}

namespace IsDrain

/-- After collapsing, `p` is empty. -/
theorem notMem_collapse (h : N.IsDrain t₂ p) (M : Marking Place) : p ∉ N.collapse t₂ p M := by
  simp [h.notMem_post]

/-- Collapsing is idempotent. -/
theorem collapse_collapse (h : N.IsDrain t₂ p) (M : Marking Place) :
    N.collapse t₂ p (N.collapse t₂ p M) = N.collapse t₂ p M :=
  collapse_of_notMem (h.notMem_collapse M)

/-- Collapsing the preset of `t₂` gives its postset. -/
theorem collapse_pre_add (h : N.IsDrain t₂ p) (R : Marking Place) :
    N.collapse t₂ p (•[N] t₂ + R) = t₂ •[N] + N.collapse t₂ p R := by
  rw [collapse_add, h.pre_eq, collapse_singleton_self]

/-- A step of `N` other than `t₂` is a step of the reduced net between the collapsed markings. -/
theorem fires_collapse (h : N.IsDrain t₂ p) {M M' : Marking Place} {t : Transition}
    (ht : t ≠ t₂) (hf : M [t⟩[N] M') :
    (N.collapse t₂ p M) [(⟨t, ht⟩ : {t // t ≠ t₂})⟩[N.fuse t₂ p] N.collapse t₂ p M' := by
  obtain ⟨R, rfl, rfl⟩ := hf
  refine ⟨N.collapse t₂ p R, ?_, collapse_add _ _⟩
  rw [collapse_add, collapse_of_notMem (h.notMem_pre t ht)]
  rfl

/-- Firing `t₂` does not change the collapse. -/
theorem collapse_eq_of_fires_right (h : N.IsDrain t₂ p) {M M' : Marking Place}
    (hf : M [t₂⟩[N] M') : N.collapse t₂ p M' = N.collapse t₂ p M := by
  obtain ⟨R, rfl, rfl⟩ := hf
  rw [h.collapse_pre_add, collapse_add, collapse_of_notMem h.notMem_post, add_comm]

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
theorem τSTr_collapse [DecidableEq Transition] (h : N.IsDrain t₂ p) (M : Marking Place) :
    (N.labelledLts (hide t₂)).τSTr M (N.collapse t₂ p M) := by
  suffices ∀ n (M : Marking Place), M.count p = n →
      (N.labelledLts (hide t₂)).τSTr M (N.collapse t₂ p M) from this _ M rfl
  intro n
  induction n with
  | zero =>
    intro M hM
    rw [collapse_of_notMem (Multiset.count_eq_zero.1 hM)]
    exact .refl
  | succ n ih =>
    intro M hM
    obtain ⟨R, rfl⟩ := Multiset.exists_cons_of_mem (Multiset.count_pos.1 (by omega) : p ∈ M)
    have hf : (p ::ₘ R) [t₂⟩[N] (R + t₂ •[N]) :=
      ⟨R, by rw [h.pre_eq, Multiset.singleton_add], rfl⟩
    have hp : (R + t₂ •[N]).count p = n := by
      rw [Multiset.count_cons_self] at hM
      rw [Multiset.count_add, Multiset.count_eq_zero.2 h.notMem_post]
      omega
    rw [← h.collapse_eq_of_fires_right hf]
    exact .head ⟨t₂, by simp [HasTau.τ], hf⟩ (ih _ hp)

/-- Firing `t₂` as often as possible reaches the collapse. -/
theorem reachable_collapse_self (h : N.IsDrain t₂ p) (M : Marking Place) :
    M ⇝[N] N.collapse t₂ p M := by
  classical
  exact reachable_of_τSTr (ℓ := hide t₂) (h.τSTr_collapse M)

/-- Reachability in the reduced net lifts to `N`, and keeps `p` empty. -/
theorem reachable_fuse (h : N.IsDrain t₂ p) {M M' : Marking Place}
    (hr : M ⇝[N.fuse t₂ p] M') (hM : p ∉ M) : p ∉ M' ∧ M ⇝[N] M' :=
  hr.invariant (P := fun K => p ∉ K ∧ M ⇝[N] K) (fun {K t K'} hf ⟨hK, hKr⟩ => by
    obtain ⟨K₂, hf₂, rfl⟩ := fires_fuse hK hf
    exact ⟨h.notMem_collapse K₂,
      hKr.trans (hf₂.reachable.trans (h.reachable_collapse_self K₂))⟩)
    ⟨hM, .refl _ _⟩

/-- A transition other than `t₂` that is enabled in `M` is enabled in its collapse. -/
theorem enabled_collapse (h : N.IsDrain t₂ p) {M : Marking Place} {t : Transition}
    (ht : t ≠ t₂) (he : M [t⟩[N]) : (N.collapse t₂ p M) [t⟩[N] :=
  le_collapse_of_notMem (h.notMem_pre t ht) he

/-! ### Preservation of behavioural properties -/

/-- From a marking with `p` empty, the markings with `p` empty reachable in `N` are exactly the
markings reachable in the reduced net. -/
theorem reachable_fuse_iff (h : N.IsDrain t₂ p) {M₀ M : Marking Place} (h₀ : p ∉ M₀)
    (hM : p ∉ M) : M₀ ⇝[N.fuse t₂ p] M ↔ M₀ ⇝[N] M := by
  refine ⟨fun hr => (h.reachable_fuse hr h₀).2, fun hr => ?_⟩
  have := h.reachable_collapse hr
  rwa [collapse_of_notMem h₀, collapse_of_notMem hM] at this

/-- Every marking reachable in `N` collapses to a marking reachable in the reduced net. -/
theorem reachable_fuse_collapse (h : N.IsDrain t₂ p) {M₀ M : Marking Place} (h₀ : p ∉ M₀)
    (hr : M₀ ⇝[N] M) : M₀ ⇝[N.fuse t₂ p] N.collapse t₂ p M := by
  have := h.reachable_collapse hr
  rwa [collapse_of_notMem h₀] at this

/-- A marking with `p` empty is dead in the reduced net iff it is dead in `N`. -/
theorem dead_fuse_iff (h : N.IsDrain t₂ p) {M : Marking Place} (hM : p ∉ M) :
    (N.fuse t₂ p).Dead M ↔ N.Dead M := by
  rw [dead_iff, dead_iff]
  refine ⟨fun hd t he => ?_, fun hd t' he => hd t'.1 he⟩
  by_cases ht : t = t₂
  · subst ht
    exact hM (h.enabled_iff.1 he)
  · exact hd ⟨t, ht⟩ he

/-- The reduction preserves the reachability of dead markings, hence deadlock-freedom. -/
theorem exists_dead_fuse_iff (h : N.IsDrain t₂ p) {M₀ : Marking Place} (h₀ : p ∉ M₀) :
    (∃ M, M₀ ⇝[N.fuse t₂ p] M ∧ (N.fuse t₂ p).Dead M) ↔ ∃ M, M₀ ⇝[N] M ∧ N.Dead M := by
  constructor
  · rintro ⟨M, hr, hd⟩
    obtain ⟨hM, hr'⟩ := h.reachable_fuse hr h₀
    exact ⟨M, hr', (h.dead_fuse_iff hM).1 hd⟩
  · rintro ⟨M, hr, hd⟩
    have hM := h.notMem_of_dead hd
    exact ⟨M, (h.reachable_fuse_iff h₀ hM).2 hr, (h.dead_fuse_iff hM).2 hd⟩

/-- The reduction preserves deadlock-freedom. -/
theorem deadlockFree_fuse_iff (h : N.IsDrain t₂ p) {M₀ : Marking Place} (h₀ : p ∉ M₀) :
    (∀ M, M₀ ⇝[N.fuse t₂ p] M → ¬ (N.fuse t₂ p).Dead M) ↔ ∀ M, M₀ ⇝[N] M → ¬ N.Dead M :=
  deadlockFree_congr (h.exists_dead_fuse_iff h₀)

/-- A transition other than `t₂` is live in the reduced net iff it is live in `N`. -/
theorem liveAt_fuse_iff_of_ne (h : N.IsDrain t₂ p) {M₀ : Marking Place} (h₀ : p ∉ M₀)
    {t : Transition} (ht : t ≠ t₂) :
    (N.fuse t₂ p).LiveAt M₀ ⟨t, ht⟩ ↔ N.LiveAt M₀ t := by
  constructor
  · intro hl M hM
    obtain ⟨M', hr, he⟩ := hl _ (h.reachable_fuse_collapse h₀ hM)
    obtain ⟨-, hr'⟩ := h.reachable_fuse hr (h.notMem_collapse M)
    exact ⟨M', (h.reachable_collapse_self M).trans hr', he⟩
  · intro hl M hM
    obtain ⟨hM₁, hM₂⟩ := h.reachable_fuse hM h₀
    obtain ⟨M', hr, he⟩ := hl M hM₂
    have hc := h.reachable_collapse hr
    rw [collapse_of_notMem hM₁] at hc
    exact ⟨_, hc, h.enabled_collapse ht he⟩

/-- Liveness is preserved by the reduction, in both directions. Some transition has to produce
into `p`, as the transition `t₂` is live only if `p` gets marked. -/
theorem live_fuse_iff (h : N.IsDrain t₂ p) {M₀ : Marking Place} (h₀ : p ∉ M₀)
    (hprod : ∃ t₁, p ∈ t₁ •[N]) : (N.fuse t₂ p).Live M₀ ↔ N.Live M₀ := by
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
theorem kBounded_fuse (h : N.IsDrain t₂ p) {M₀ : Marking Place} (h₀ : p ∉ M₀) {k : ℕ}
    (hk : N.KBounded M₀ k) : (N.fuse t₂ p).KBounded M₀ k :=
  fun M hM => hk M (h.reachable_fuse hM h₀).2

/-- If `t₂` produces a token somewhere, boundedness of the reduced net implies boundedness of `N`:
tokens in `p` are counted in the postset of `t₂`. -/
theorem kBounded_of_fuse (h : N.IsDrain t₂ p) {M₀ : Marking Place} (h₀ : p ∉ M₀) {k : ℕ}
    (hpost : t₂ •[N] ≠ 0) (hk : (N.fuse t₂ p).KBounded M₀ k) : N.KBounded M₀ k := by
  rw [kBounded_iff] at hk ⊢
  exact fun M hM => count_le_of_collapse hpost (hk _ (h.reachable_fuse_collapse h₀ hM))

/-- `k`-boundedness is preserved by the reduction when `t₂` produces a token somewhere. -/
theorem kBounded_fuse_iff (h : N.IsDrain t₂ p) {M₀ : Marking Place} (h₀ : p ∉ M₀) {k : ℕ}
    (hpost : t₂ •[N] ≠ 0) : (N.fuse t₂ p).KBounded M₀ k ↔ N.KBounded M₀ k :=
  ⟨h.kBounded_of_fuse h₀ hpost, h.kBounded_fuse h₀⟩

/-- Boundedness is preserved by the reduction when `t₂` produces a token somewhere. -/
theorem bounded_fuse_iff (h : N.IsDrain t₂ p) {M₀ : Marking Place} (h₀ : p ∉ M₀)
    (hpost : t₂ •[N] ≠ 0) : (N.fuse t₂ p).Bounded M₀ ↔ N.Bounded M₀ :=
  exists_congr fun _ => h.kBounded_fuse_iff h₀ hpost

/-- Safeness is preserved by the reduction when `t₂` produces a token somewhere. -/
theorem safe_fuse_iff (h : N.IsDrain t₂ p) {M₀ : Marking Place} (h₀ : p ∉ M₀)
    (hpost : t₂ •[N] ≠ 0) : (N.fuse t₂ p).Safe M₀ ↔ N.Safe M₀ :=
  h.kBounded_fuse_iff h₀ hpost

/-! ### Soundness of workflow nets -/

/-- Fusing a series of transitions preserves and reflects the soundness of a workflow net with
source `i` and sink `o`. The transition `t₂` has to produce a token somewhere, as it does in
every workflow net, and some transition has to produce into `p`. -/
theorem sound_fuse_iff (h : N.IsDrain t₂ p) {i o : Place} (hi : i ≠ p) (ho : o ≠ p)
    (hpost : t₂ •[N] ≠ 0) (hprod : ∃ t₁, p ∈ t₁ •[N]) :
    (N.fuse t₂ p).Sound i o ↔ N.Sound i o := by
  obtain ⟨t₁, ht₁⟩ := hprod
  have hne := h.ne_of_post ht₁
  have h₀ : p ∉ token i := notMem_token hi.symm
  have hop : p ∉ token o := notMem_token ho.symm
  constructor
  · intro hs
    refine ⟨fun M hM => ?_, fun M hM hle => ?_, fun t => ?_⟩
    · have hc := hs.completion _ (h.reachable_fuse_collapse h₀ hM)
      exact (h.reachable_collapse_self M).trans
        (h.reachable_fuse (M := N.collapse t₂ p M) hc (h.notMem_collapse M)).2
    · have hcM := hs.proper _ (h.reachable_fuse_collapse h₀ hM) (le_collapse_of_notMem hop hle)
      -- a token in `p` would collapse to a second token next to the one in `o`
      have hMp : p ∉ M := fun hpM => by
        have h1 := congrArg Multiset.card hcM
        simp only [collapse, Multiset.card_add, Multiset.card_nsmul, token,
          Multiset.card_singleton] at h1
        have h2 : 0 < (M.filter (· ≠ p)).card := Multiset.card_pos_iff_exists_mem.2
          ⟨o, Multiset.mem_filter.2 ⟨token_le_iff.1 hle, ho⟩⟩
        have h3 := Nat.mul_pos (Multiset.count_pos.2 hpM) (Multiset.card_pos.2 hpost)
        omega
      rwa [collapse_of_notMem hMp] at hcM
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
      rwa [collapse_of_notMem hM₁, collapse_of_notMem hop] at hc
    · exact hs.proper M (h.reachable_fuse hM h₀).2 hle
    · obtain ⟨M, hM, he⟩ := hs.noDead t.1
      exact ⟨N.collapse t₂ p M, h.reachable_fuse_collapse h₀ hM, h.enabled_collapse t.2 he⟩

/-! ### The reduction as a weak bisimulation -/

section Weak

variable [DecidableEq Transition]

/-- Every marking of `N` is weakly bisimilar to its collapse in the reduced net, where `t₂` is the
invisible action. The reduction preserves the observable behaviour, and thereby everything that
weak bisimilarity preserves. -/
theorem weakBisimilar_collapse (h : N.IsDrain t₂ p) (M : Marking Place) :
    WeakBisimilarity (N.labelledLts (hide t₂)) ((N.fuse t₂ p).labelledLts some)
      M (N.collapse t₂ p M) :=
  weakBisimilar_of_collapse (N.collapse t₂ p) h.τSTr_collapse h.collapse_collapse
    (fun hf => h.collapse_eq_of_fires_right hf) (fun {_ _ t} hf => h.fires_collapse t.2 hf)
    (fun hf => fires_fuse (h.notMem_collapse _) hf) M

/-- Every marking of `N` has the same weak traces as its collapse in the reduced net: the traces of
the saturated marking graphs, in which `t₂` is invisible. -/
theorem traceEq_saturate_collapse (h : N.IsDrain t₂ p) (M : Marking Place) :
    M ~tr[(N.labelledLts (hide t₂)).saturate, ((N.fuse t₂ p).labelledLts some).saturate]
      (N.collapse t₂ p M) := by
  obtain ⟨r, hr, hb⟩ := h.weakBisimilar_collapse M
  exact hb.traceEq hr

end Weak

/-! ### Markings with tokens in `p`

The results above are for markings with `p` empty. For an arbitrary marking `M₀`, apply them to
`N.collapse t₂ p M₀`, which `M₀` reaches in `N` by firing `t₂`, and which has the same behaviour.
Soundness needs no such statement, as the initial marking of a workflow net has a single token in
its source, which is not `p`. -/

/-- A marking with `p` empty is reachable from the collapse of `M₀` exactly when it is reachable
from `M₀`. -/
theorem reachable_collapse_iff (h : N.IsDrain t₂ p) {M₀ M : Marking Place} (hM : p ∉ M) :
    N.collapse t₂ p M₀ ⇝[N] M ↔ M₀ ⇝[N] M := by
  refine ⟨fun hr => (h.reachable_collapse_self M₀).trans hr, fun hr => ?_⟩
  have := h.reachable_collapse hr
  rw [collapse_of_notMem hM] at this
  exact (h.reachable_fuse this (h.notMem_collapse M₀)).2

/-- The collapse of a marking reachable from `M₀` is reachable from the collapse of `M₀`. -/
theorem reachable_collapse_collapse (h : N.IsDrain t₂ p) {M₀ M : Marking Place}
    (hr : M₀ ⇝[N] M) : N.collapse t₂ p M₀ ⇝[N] N.collapse t₂ p M :=
  (h.reachable_collapse_iff (h.notMem_collapse M)).2 (hr.trans (h.reachable_collapse_self M))

/-- The collapse of `M₀` has the same reachable dead markings as `M₀`. -/
theorem exists_dead_collapse_iff (h : N.IsDrain t₂ p) {M₀ : Marking Place} :
    (∃ M, N.collapse t₂ p M₀ ⇝[N] M ∧ N.Dead M) ↔ ∃ M, M₀ ⇝[N] M ∧ N.Dead M :=
  ⟨fun ⟨M, hr, hd⟩ => ⟨M, (h.reachable_collapse_self M₀).trans hr, hd⟩,
    fun ⟨M, hr, hd⟩ => ⟨M, (h.reachable_collapse_iff (h.notMem_of_dead hd)).2 hr, hd⟩⟩

/-- `N` is live at the collapse of `M₀` iff it is live at `M₀`. -/
theorem live_collapse_iff (h : N.IsDrain t₂ p) {M₀ : Marking Place} :
    N.Live (N.collapse t₂ p M₀) ↔ N.Live M₀ := by
  refine ⟨fun hl t M hM => ?_, fun hl t M hM => hl t M ((h.reachable_collapse_self M₀).trans hM)⟩
  obtain ⟨M', hr, he⟩ := hl t _ (h.reachable_collapse_collapse hM)
  exact ⟨M', (h.reachable_collapse_self M).trans hr, he⟩

/-- `N` is `k`-bounded at the collapse of `M₀` iff it is `k`-bounded at `M₀`, if `t₂` produces a
token somewhere. -/
theorem kBounded_collapse_iff (h : N.IsDrain t₂ p) {M₀ : Marking Place} {k : ℕ}
    (hpost : t₂ •[N] ≠ 0) : N.KBounded (N.collapse t₂ p M₀) k ↔ N.KBounded M₀ k := by
  refine ⟨fun hk => ?_, fun hk M hM => hk M ((h.reachable_collapse_self M₀).trans hM)⟩
  rw [kBounded_iff] at hk ⊢
  exact fun M hM => count_le_of_collapse hpost (hk _ (h.reachable_collapse_collapse hM))

/-- `N` is bounded at the collapse of `M₀` iff it is bounded at `M₀`, if `t₂` produces a token
somewhere. -/
theorem bounded_collapse_iff (h : N.IsDrain t₂ p) {M₀ : Marking Place}
    (hpost : t₂ •[N] ≠ 0) : N.Bounded (N.collapse t₂ p M₀) ↔ N.Bounded M₀ :=
  exists_congr fun _ => h.kBounded_collapse_iff hpost

/-- Reachability of markings with `p` empty, from an arbitrary marking: `M₀` reaches `M` in `N`
iff its collapse reaches `M` in the reduced net. -/
theorem reachable_fuse_collapse_iff (h : N.IsDrain t₂ p) {M₀ M : Marking Place} (hM : p ∉ M) :
    N.collapse t₂ p M₀ ⇝[N.fuse t₂ p] M ↔ M₀ ⇝[N] M := by
  rw [← h.reachable_collapse_iff hM]
  exact h.reachable_fuse_iff (h.notMem_collapse M₀) hM

/-- The reduced net reaches a dead marking from the collapse of `M₀` iff `N` does from `M₀`. -/
theorem exists_dead_fuse_collapse_iff (h : N.IsDrain t₂ p) {M₀ : Marking Place} :
    (∃ M, N.collapse t₂ p M₀ ⇝[N.fuse t₂ p] M ∧ (N.fuse t₂ p).Dead M) ↔
      ∃ M, M₀ ⇝[N] M ∧ N.Dead M :=
  (h.exists_dead_fuse_iff (h.notMem_collapse M₀)).trans h.exists_dead_collapse_iff

/-- The reduced net is deadlock-free from the collapse of `M₀` iff `N` is from `M₀`. -/
theorem deadlockFree_fuse_collapse_iff (h : N.IsDrain t₂ p) {M₀ : Marking Place} :
    (∀ M, N.collapse t₂ p M₀ ⇝[N.fuse t₂ p] M → ¬ (N.fuse t₂ p).Dead M) ↔
      ∀ M, M₀ ⇝[N] M → ¬ N.Dead M :=
  deadlockFree_congr h.exists_dead_fuse_collapse_iff

/-- The reduced net is live at the collapse of `M₀` iff `N` is live at `M₀`. -/
theorem live_fuse_collapse_iff (h : N.IsDrain t₂ p) {M₀ : Marking Place}
    (hprod : ∃ t₁, p ∈ t₁ •[N]) : (N.fuse t₂ p).Live (N.collapse t₂ p M₀) ↔ N.Live M₀ :=
  (h.live_fuse_iff (h.notMem_collapse M₀) hprod).trans h.live_collapse_iff

/-- The reduced net is bounded at the collapse of `M₀` iff `N` is bounded at `M₀`. -/
theorem bounded_fuse_collapse_iff (h : N.IsDrain t₂ p) {M₀ : Marking Place}
    (hpost : t₂ •[N] ≠ 0) :
    (N.fuse t₂ p).Bounded (N.collapse t₂ p M₀) ↔ N.Bounded M₀ :=
  (h.bounded_fuse_iff (h.notMem_collapse M₀) hpost).trans (h.bounded_collapse_iff hpost)

/-! ### Deleting the isolated place -/

/-- The reduced net has `p` isolated. -/
theorem isIsolated_fuse (h : N.IsDrain t₂ p) : (N.fuse t₂ p).IsIsolated p :=
  fun t => ⟨h.notMem_pre t.1 t.2, h.notMem_collapse _⟩

/-- From a marking with `p` empty, the markings with `p` empty reachable in `N` are those
reachable in the reduced net without `p`. -/
theorem reachable_fuseDelete_iff (h : N.IsDrain t₂ p) {M₀ M : Marking Place} (h₀ : p ∉ M₀)
    (hM : p ∉ M) :
    (M₀.drop p) ⇝[N.fuseDelete t₂ p] (M.drop p) ↔ M₀ ⇝[N] M := by
  rw [← h.reachable_fuse_iff h₀ hM, fuseDelete_eq,
    (h.isIsolated_fuse.redundantPlace (M₀ := M₀)).reachable_drop_iff (Reachable.refl _ M₀)]
  refine ⟨fun ⟨M', hr, hd⟩ => ?_, fun hr => ⟨M, hr, rfl⟩⟩
  rwa [Marking.eq_of_drop_eq (h.reachable_fuse hr h₀).1 hM hd] at hr

/-- The reduction preserves the reachability of dead markings. -/
theorem exists_dead_fuseDelete_iff (h : N.IsDrain t₂ p) {M₀ : Marking Place} (h₀ : p ∉ M₀) :
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
theorem deadlockFree_fuseDelete_iff (h : N.IsDrain t₂ p) {M₀ : Marking Place} (h₀ : p ∉ M₀) :
    (∀ K, (M₀.drop p) ⇝[N.fuseDelete t₂ p] K → ¬ (N.fuseDelete t₂ p).Dead K) ↔
      ∀ M, M₀ ⇝[N] M → ¬ N.Dead M :=
  deadlockFree_congr (h.exists_dead_fuseDelete_iff h₀)

/-- Deleting the isolated place preserves liveness. -/
theorem live_fuseDelete_iff (h : N.IsDrain t₂ p) {M₀ : Marking Place} (h₀ : p ∉ M₀)
    (hprod : ∃ t₁, p ∈ t₁ •[N]) :
    (N.fuseDelete t₂ p).Live (M₀.drop p) ↔ N.Live M₀ := by
  rw [← h.live_fuse_iff h₀ hprod, fuseDelete_eq]
  exact (h.isIsolated_fuse.redundantPlace (M₀ := M₀)).live_iff.symm

/-- Deleting the isolated place preserves boundedness, if `t₂` produces a token somewhere. -/
theorem bounded_fuseDelete_iff (h : N.IsDrain t₂ p) {M₀ : Marking Place} (h₀ : p ∉ M₀)
    (hpost : t₂ •[N] ≠ 0) :
    (N.fuseDelete t₂ p).Bounded (M₀.drop p) ↔ N.Bounded M₀ := by
  rw [← h.bounded_fuse_iff h₀ hpost, fuseDelete_eq]
  refine ((h.isIsolated_fuse.redundantPlace (M₀ := M₀)).bounded_iff_of_post_le_pre fun t => ?_).symm
  rw [Multiset.count_eq_zero_of_notMem (h.isIsolated_fuse t).2]
  exact Nat.zero_le _

/-- Reachability of markings with `p` empty in the reduced net without `p`, from an arbitrary
marking. -/
theorem reachable_fuseDelete_collapse_iff (h : N.IsDrain t₂ p) {M₀ M : Marking Place}
    (hM : p ∉ M) :
    ((N.collapse t₂ p M₀).drop p) ⇝[N.fuseDelete t₂ p] (M.drop p) ↔ M₀ ⇝[N] M :=
  (h.reachable_fuseDelete_iff (h.notMem_collapse M₀) hM).trans (h.reachable_collapse_iff hM)

/-- The reduction preserves the reachability of dead markings, from an arbitrary marking. -/
theorem exists_dead_fuseDelete_collapse_iff (h : N.IsDrain t₂ p) {M₀ : Marking Place} :
    (∃ K, ((N.collapse t₂ p M₀).drop p) ⇝[N.fuseDelete t₂ p] K ∧
        (N.fuseDelete t₂ p).Dead K) ↔ ∃ M, M₀ ⇝[N] M ∧ N.Dead M :=
  (h.exists_dead_fuseDelete_iff (h.notMem_collapse M₀)).trans h.exists_dead_collapse_iff

/-- The reduction preserves deadlock-freedom, from an arbitrary marking. -/
theorem deadlockFree_fuseDelete_collapse_iff (h : N.IsDrain t₂ p) {M₀ : Marking Place} :
    (∀ K, ((N.collapse t₂ p M₀).drop p) ⇝[N.fuseDelete t₂ p] K →
        ¬ (N.fuseDelete t₂ p).Dead K) ↔ ∀ M, M₀ ⇝[N] M → ¬ N.Dead M :=
  deadlockFree_congr h.exists_dead_fuseDelete_collapse_iff

/-- The reduction without `p` preserves liveness, from an arbitrary marking. -/
theorem live_fuseDelete_collapse_iff (h : N.IsDrain t₂ p) {M₀ : Marking Place}
    (hprod : ∃ t₁, p ∈ t₁ •[N]) :
    (N.fuseDelete t₂ p).Live ((N.collapse t₂ p M₀).drop p) ↔ N.Live M₀ :=
  (h.live_fuseDelete_iff (h.notMem_collapse M₀) hprod).trans h.live_collapse_iff

/-- The reduction without `p` preserves boundedness, from an arbitrary marking. -/
theorem bounded_fuseDelete_collapse_iff (h : N.IsDrain t₂ p) {M₀ : Marking Place}
    (hpost : t₂ •[N] ≠ 0) :
    (N.fuseDelete t₂ p).Bounded ((N.collapse t₂ p M₀).drop p) ↔ N.Bounded M₀ :=
  (h.bounded_fuseDelete_iff (h.notMem_collapse M₀) hpost).trans (h.bounded_collapse_iff hpost)

end IsDrain

section Isolated

variable {Q : Type*} [DecidableEq Q] {A : PetriNet Q Transition} {r : Q}

/-- The restriction of the marking with a single token. -/
theorem token_drop {i : Q} (hi : i ≠ r) : (token i).drop r = token ⟨i, hi⟩ :=
  by simp [token, Marking.drop_singleton, hi]

/-- Deleting an isolated place preserves and reflects the soundness of a workflow net whose source
and sink are other places. -/
theorem IsIsolated.sound_removePlace_iff (h : A.IsIsolated r) {i o : Q} (hi : i ≠ r)
    (ho : o ≠ r) : (A.removePlace r).Sound ⟨i, hi⟩ ⟨o, ho⟩ ↔ A.Sound i o := by
  have hred : ∀ M₀ : Marking Q, A.RedundantPlace r M₀ := fun _ => h.redundantPlace
  have hp0 : ∀ M, token i ⇝[A] M → r ∉ M := fun M hM => by
    rw [← Multiset.count_eq_zero, h.count_eq_of_reachable hM, Multiset.count_eq_zero]
    exact notMem_token hi.symm
  have hop : r ∉ token o := notMem_token ho.symm
  have hti := token_drop hi
  have hto := token_drop ho
  constructor
  · intro hs
    refine ⟨fun M hM => ?_, fun M hM hle => ?_, fun t => ?_⟩
    · have hc := hs.completion (M.drop r) (hti ▸ hM.drop)
      rw [← hto] at hc
      obtain ⟨M', hM', hd⟩ := ((hred _).reachable_drop_iff hM _).1 hc
      rwa [Marking.eq_of_drop_eq (hp0 _ (hM.trans hM')) hop hd] at hM'
    · refine Marking.eq_of_drop_eq (hp0 M hM) hop ?_
      rw [hto]
      exact hs.proper _ (hti ▸ hM.drop)
        (token_le_iff.2 ((Marking.mem_drop _ (q := ⟨o, ho⟩)).2 (token_le_iff.1 hle)))
    · obtain ⟨K, hK, he⟩ := hs.noDead t
      rw [← hti] at hK
      obtain ⟨M, hM, rfl⟩ := ((hred _).reachable_drop_iff (Reachable.refl A _) K).1 hK
      exact ⟨M, hM, h.enabled_iff.1 he⟩
  · intro hs
    refine ⟨fun K hK => ?_, fun K hK hle => ?_, fun t => ?_⟩
    · rw [← hti] at hK
      obtain ⟨M, hM, rfl⟩ := ((hred _).reachable_drop_iff (Reachable.refl A _) K).1 hK
      exact hto ▸ (hs.completion M hM).drop
    · rw [← hti] at hK
      obtain ⟨M, hM, rfl⟩ := ((hred _).reachable_drop_iff (Reachable.refl A _) K).1 hK
      rw [← hto, hs.proper M hM (token_le_iff.2 ((Marking.mem_drop _).1 (token_le_iff.1 hle)))]
    · obtain ⟨M, hM, he⟩ := hs.noDead t
      exact ⟨M.drop r, hti ▸ hM.drop, h.enabled_iff.2 he⟩

end Isolated

namespace IsDrain

/-- Fusing a series and deleting the isolated place preserves and reflects the soundness of a
workflow net. -/
theorem sound_fuseDelete_iff (h : N.IsDrain t₂ p) {i o : Place} (hi : i ≠ p) (ho : o ≠ p)
    (hpost : t₂ •[N] ≠ 0) (hprod : ∃ t₁, p ∈ t₁ •[N]) :
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
  let Prod : Prop := ∃ t, ∃ ht : t ≠ t₂, p ∈ t •[N] ∧ R (.inr ⟨t, ht⟩)
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
      · change q ∈ •[N] t' at hxy
        refine ⟨fun ht => ?_, fun e => ?_⟩
        · have hq : q ≠ p := fun e => h.notMem_pre t' ht (e ▸ hxy)
          exact (ih.1 hq).tail (show ⟨q, hq⟩ ∈ Marking.drop p (•[N] t') from
            (Marking.mem_drop _).2 hxy)
        · rw [e, h.pre_eq] at hxy
          exact ih.2 (Multiset.mem_singleton.1 hxy)
      · change q' ∈ t •[N] at hxy
        refine ⟨fun hq => ?_, fun e => ?_⟩
        · by_cases ht : t = t₂
          · obtain ⟨t₃, ht₃, hpt, hR⟩ := ih.2 ht
            exact hR.tail (show ⟨q', hq⟩ ∈ Marking.drop p (N.collapse t₂ p (t₃ •[N])) from
              (Marking.mem_drop _).2 (mem_collapse.2 (.inr ⟨hpt, ht ▸ hxy⟩)))
          · exact (ih.1 ht).tail (show ⟨q', hq⟩ ∈ Marking.drop p (N.collapse t₂ p (t •[N])) from
              (Marking.mem_drop _).2 (mem_collapse.2 (.inl ⟨hxy, hq⟩)))
        · subst e
          have ht : t ≠ t₂ := fun e => h.notMem_post (e ▸ hxy)
          exact ⟨t, ht, hxy, ih.1 ht⟩
      · exact hxy.elim
  rcases y with ⟨q, hq⟩ | ⟨t, ht⟩
  · exact (key _ hr).1 hq
  · exact (key _ hr).1 ht

/-- The reduction preserves the workflow net structure once `p` is deleted. -/
theorem isWFNet_fuseDelete (h : N.IsDrain t₂ p) {i o : Place} (hN : N.IsWFNet i o) (hi : i ≠ p)
    (ho : o ≠ p) : (N.fuseDelete t₂ p).IsWFNet ⟨i, hi⟩ ⟨o, ho⟩ := by
  refine ⟨fun t hm => ?_, fun t hm => hN.no_output_sink t.1 ((Marking.mem_drop _).1 hm),
    fun n => h.reflTransGen_arc_fuseDelete (hN.reach_from_source _),
    fun n => h.reflTransGen_arc_fuseDelete (hN.reach_to_sink _)⟩
  rcases mem_collapse.1 ((Marking.mem_drop _).1 hm) with ⟨hm, -⟩ | ⟨-, hm⟩
  · exact hN.no_input_source _ hm
  · exact hN.no_input_source _ hm

/-- The reduce-then-decide pipeline for workflow nets: if `p` is drained by `t₂` and is not the
source, the net obtained by fusing and deleting `p` is a workflow net, and it is sound iff `N`
is. -/
theorem isWFNet_and_sound_fuseDelete (h : N.IsDrain t₂ p) {i o : Place} (hN : N.IsWFNet i o)
    (hi : i ≠ p) :
    (N.fuseDelete t₂ p).IsWFNet ⟨i, hi⟩ ⟨o, h.ne_sink hN⟩ ∧
      ((N.fuseDelete t₂ p).Sound ⟨i, hi⟩ ⟨o, h.ne_sink hN⟩ ↔ N.Sound i o) :=
  ⟨h.isWFNet_fuseDelete hN hi (h.ne_sink hN),
    h.sound_fuseDelete_iff hi (h.ne_sink hN)
      (let ⟨_, hq⟩ := hN.exists_post t₂; fun h0 => Multiset.notMem_zero _ (h0 ▸ hq))
      (hN.exists_producer hi.symm)⟩

end IsDrain

namespace IsSeries

/-- The producer `t₁` of a series puts a token into `p`. -/
theorem post_pos (h : N.IsSeries t₁ t₂ p) : p ∈ t₁ •[N] :=
  Multiset.count_pos.1 (h.post_left ▸ Nat.one_pos)

/-- The two transitions of a series are different. -/
theorem ne (h : N.IsSeries t₁ t₂ p) : t₁ ≠ t₂ := h.toIsDrain.ne_of_post h.post_pos

/-- In a workflow net, a place with a producer is not the source. -/
theorem ne_source (h : N.IsSeries t₁ t₂ p) {i o : Place} (hN : N.IsWFNet i o) : i ≠ p := fun e =>
  hN.no_input_source t₁ (e ▸ h.post_pos)

/-- Liveness is preserved by fusing a series of transitions. -/
theorem live_fuse_iff (h : N.IsSeries t₁ t₂ p) {M₀ : Marking Place} (h₀ : p ∉ M₀) :
    (N.fuse t₂ p).Live M₀ ↔ N.Live M₀ :=
  h.toIsDrain.live_fuse_iff h₀ ⟨t₁, h.post_pos⟩

/-- Boundedness is preserved by fusing a series of transitions, if `t₂` produces a token
somewhere. -/
theorem bounded_fuse_iff (h : N.IsSeries t₁ t₂ p) {M₀ : Marking Place} (h₀ : p ∉ M₀)
    (hpost : t₂ •[N] ≠ 0) : (N.fuse t₂ p).Bounded M₀ ↔ N.Bounded M₀ :=
  h.toIsDrain.bounded_fuse_iff h₀ hpost

/-- Soundness of a workflow net is preserved by fusing a series of transitions. -/
theorem sound_fuse_iff (h : N.IsSeries t₁ t₂ p) {i o : Place} (hi : i ≠ p) (ho : o ≠ p)
    (hpost : t₂ •[N] ≠ 0) : (N.fuse t₂ p).Sound i o ↔ N.Sound i o :=
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
