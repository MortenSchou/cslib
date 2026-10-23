/-
Copyright (c) 2026 Morten Schou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Morten Schou
-/

module

public import Cslib.Computability.PetriNets.Soundness
public import Mathlib.Logic.Relation

/-! # Workflow nets and notions of soundness

A *workflow net* has a source place `i` with no input, a sink place `o` with no output, and every
node of the net lies on a path from `i` to `o`. Besides classical soundness (`PetriNet.Sound`),
the literature has several weaker notions, of which the following are defined here, for a net with
source `i` and sink `o`:

- *`k`-soundness*: from `k` tokens in `i`, the marking with `k` tokens in `o` stays reachable.
  Weak soundness is `1`-soundness, and *up-to-`k`* and *generalized* soundness ask for `l`-soundness
  for all `l ≤ k`, respectively for all `l`.
- *Relaxed soundness*: every transition occurs on some firing sequence that can be completed.
- *Lazy soundness*: the sink can be marked exactly once, but tokens may be left behind.
- *Easy soundness*: the final marking is reachable from the initial one.

Generalized soundness quantifies over all numbers of cases, so it cannot be decided by exploring
one state space. It is decidable for workflow nets without reset or inhibitor arcs (van Hee,
Sidorova and Voorhoeve), by an algebraic argument that is not formalised here. Up-to-`k`
soundness is decided for each `k` in `ExecutableSoundnessNotions`, which refutes generalized
soundness whenever it fails at some `k`; `PetriNet.not_generalizedSound_of_not_upToKSound` states
this.

## Main definitions

- `PetriNet.IsWFNet`: the structure of a workflow net.
- `PetriNet.KSound`, `PetriNet.UpToKSound`, `PetriNet.GeneralizedSound`, `PetriNet.RelaxedSound`,
  `PetriNet.LazySound`, `PetriNet.EasySound`.

## Main statements

- `PetriNet.IsWFNet.proper_of_completion`: in a workflow net, the option to complete implies proper
  completion.
- `PetriNet.IsWFNet.sound_iff`: a workflow net is sound iff it is weakly sound and has no dead
  transition.
- `PetriNet.Sound.weak`, `PetriNet.Sound.relaxed`, `PetriNet.GeneralizedSound.upToK`,
  `PetriNet.KSound.easy`, `PetriNet.LazySound.of_weak`, `PetriNet.RelaxedSound.easy`: the
  implications between the notions.

## References

* [W. M. P. van der Aalst et al., *Soundness of Workflow Nets: Classification, Decidability, and
  Analysis*][Aalst2011]
-/

@[expose] public section

namespace Cslib

namespace PetriNet

variable {Place : Type*} {Transition : Type*} {N : PetriNet Place Transition} {i o : Place}

/-- The flow relation of a net on its places and transitions: an arc runs from a place to every
transition that consumes from it, and from a transition to every place it produces into. -/
def Arc (N : PetriNet Place Transition) : Place ⊕ Transition → Place ⊕ Transition → Prop
  | .inl p, .inr t => 0 < N.pre t p
  | .inr t, .inl p => 0 < N.post t p
  | _, _ => False

/-- A workflow net: the source `i` has no input transition, the sink `o` has no output transition,
and every node lies on a path from `i` to `o`. -/
structure IsWFNet (N : PetriNet Place Transition) (i o : Place) : Prop where
  /-- No transition produces into the source. -/
  no_input_source : ∀ t, N.post t i = 0
  /-- No transition consumes from the sink. -/
  no_output_sink : ∀ t, N.pre t o = 0
  /-- Every node is reachable from the source. -/
  reach_from_source : ∀ n, Relation.ReflTransGen N.Arc (.inl i) n
  /-- The sink is reachable from every node. -/
  reach_to_sink : ∀ n, Relation.ReflTransGen N.Arc n (.inl o)

/-- Every transition of a workflow net produces a token somewhere. -/
theorem IsWFNet.exists_post (h : N.IsWFNet i o) (t : Transition) : ∃ p, 0 < N.post t p := by
  rcases (h.reach_to_sink (.inr t)).cases_head with h' | ⟨c, hc, -⟩
  · exact absurd h' (by simp)
  · cases c with
    | inl p => exact ⟨p, hc⟩
    | inr _ => exact hc.elim

/-- Every transition of a workflow net consumes a token from somewhere. -/
theorem IsWFNet.exists_pre (h : N.IsWFNet i o) (t : Transition) : ∃ p, 0 < N.pre t p := by
  rcases (h.reach_from_source (.inr t)).cases_tail with h' | ⟨c, -, hc⟩
  · exact absurd h' (by simp)
  · cases c with
    | inl p => exact ⟨p, hc⟩
    | inr _ => exact hc.elim

/-- The source is the only place without an input transition. -/
theorem IsWFNet.exists_producer (h : N.IsWFNet i o) {p : Place} (hp : p ≠ i) :
    ∃ t, 0 < N.post t p := by
  rcases (h.reach_from_source (.inl p)).cases_tail with h' | ⟨c, -, hc⟩
  · exact absurd (Sum.inl.inj h') hp
  · cases c with
    | inl _ => exact hc.elim
    | inr t => exact ⟨t, hc⟩

/-- The sink is the only place without an output transition. -/
theorem IsWFNet.exists_consumer (h : N.IsWFNet i o) {p : Place} (hp : p ≠ o) :
    ∃ t, 0 < N.pre t p := by
  rcases (h.reach_to_sink (.inl p)).cases_head with h' | ⟨c, hc, -⟩
  · exact absurd (Sum.inl.inj h') hp
  · cases c with
    | inl _ => exact hc.elim
    | inr t => exact ⟨t, hc⟩

/-- The single token sits in its place. -/
theorem token_apply_self (p : Place) : token p p = 1 := by simp [token]

/-- The single token is absent from every other place. -/
theorem token_apply_of_ne {p q : Place} (h : q ≠ p) : token p q = 0 := by
  simp [token, Ne.symm h]

/-- In a workflow net, a marking that has a token in the sink and something else cannot reach the
final marking: tokens in the sink are never consumed, and every transition leaves a token
somewhere. -/
theorem IsWFNet.not_reachable_token (h : N.IsWFNet i o) {M : Marking Place}
    (hle : token o ≤ M) (hne : M ≠ token o) : ¬ M ⇝[N] token o := by
  intro hr
  have key := hr.invariant (P := fun K => token o ≤ K ∧ K ≠ token o)
    (fun {K t K'} hf ⟨hK, hKne⟩ => ?_) ⟨hle, hne⟩
  · exact key.2 rfl
  · obtain ⟨R, rfl, rfl⟩ := hf
    have hKo : 1 ≤ (•[N] t + R) o := by simpa [token_apply_self] using hK o
    have hRo : 1 ≤ R o := by
      simpa [Finsupp.add_apply, h.no_output_sink t] using hKo
    refine ⟨fun p => ?_, fun heq => ?_⟩
    · by_cases hp : p = o
      · subst hp; simp only [token_apply_self, Finsupp.add_apply]; omega
      · simp [token_apply_of_ne hp]
    · obtain ⟨p, hp⟩ := h.exists_post t
      have := DFunLike.congr_fun heq p
      simp only [Finsupp.add_apply] at this
      by_cases hpo : p = o
      · subst hpo; rw [token_apply_self] at this; omega
      · rw [token_apply_of_ne hpo] at this; omega

/-- In a workflow net, the option to complete implies proper completion. -/
theorem IsWFNet.proper_of_completion (h : N.IsWFNet i o)
    (hc : ∀ M, token i ⇝[N] M → M ⇝[N] token o) :
    ∀ M, token i ⇝[N] M → token o ≤ M → M = token o := fun M hM hle =>
  by_contra fun hne => h.not_reachable_token hle hne (hc M hM)

/-! ### Soundness notions -/

/-- `k`-soundness: from `k` tokens in the source, the marking with `k` tokens in the sink stays
reachable. -/
def KSound (N : PetriNet Place Transition) (i o : Place) (k : ℕ) : Prop :=
  ∀ M, (k • token i) ⇝[N] M → M ⇝[N] (k • token o)

/-- Up-to-`k` soundness: `l`-soundness for every `l ≤ k`. -/
def UpToKSound (N : PetriNet Place Transition) (i o : Place) (k : ℕ) : Prop :=
  ∀ l ≤ k, N.KSound i o l

/-- Generalized soundness: `k`-soundness for every `k`. -/
def GeneralizedSound (N : PetriNet Place Transition) (i o : Place) : Prop :=
  ∀ k, N.KSound i o k

/-- Weak soundness is `1`-soundness: the option to complete. -/
abbrev WeakSound (N : PetriNet Place Transition) (i o : Place) : Prop := N.KSound i o 1

/-- Relaxed soundness: every transition fires on some firing sequence from the initial marking that
can still be completed. -/
def RelaxedSound (N : PetriNet Place Transition) (i o : Place) : Prop :=
  ∀ t, ∃ M M', token i ⇝[N] M ∧ M [t⟩[N] M' ∧ M' ⇝[N] token o

/-- Lazy soundness: the sink can always be marked, and never holds more than one token. -/
def LazySound (N : PetriNet Place Transition) (i o : Place) : Prop :=
  (∀ M, token i ⇝[N] M → ∃ M', M ⇝[N] M' ∧ M' o = 1) ∧
    ∀ M, token i ⇝[N] M → M o ≤ 1

/-- Easy soundness: the final marking is reachable from the initial marking. -/
def EasySound (N : PetriNet Place Transition) (i o : Place) : Prop :=
  token i ⇝[N] token o

theorem weakSound_iff : N.WeakSound i o ↔
    ∀ M, token i ⇝[N] M → M ⇝[N] token o := by
  simp [WeakSound, KSound]

theorem GeneralizedSound.upToK (h : N.GeneralizedSound i o) (k : ℕ) : N.UpToKSound i o k :=
  fun l _ => h l

theorem UpToKSound.kSound (h : N.UpToKSound i o k) : N.KSound i o k := h k le_rfl

theorem generalizedSound_iff_forall_upToKSound :
    N.GeneralizedSound i o ↔ ∀ k, N.UpToKSound i o k :=
  ⟨fun h k => h.upToK k, fun h k => (h k).kSound⟩

/-- Generalized soundness is refuted by a single `k` for which the net is not `k`-sound. -/
theorem not_generalizedSound_of_not_kSound (h : ¬ N.KSound i o k) : ¬ N.GeneralizedSound i o :=
  fun hg => h (hg k)

/-- Generalized soundness is refuted by failing up-to-`k` soundness for some `k`. -/
theorem not_generalizedSound_of_not_upToKSound (h : ¬ N.UpToKSound i o k) :
    ¬ N.GeneralizedSound i o :=
  fun hg => h (hg.upToK k)

theorem GeneralizedSound.weak (h : N.GeneralizedSound i o) : N.WeakSound i o := h 1

/-- Classical soundness implies weak soundness. -/
theorem Sound.weak (h : N.Sound i o) : N.WeakSound i o :=
  weakSound_iff.2 h.completion

/-- Classical soundness implies relaxed soundness. -/
theorem Sound.relaxed (h : N.Sound i o) : N.RelaxedSound i o := fun t => by
  obtain ⟨M, hM, hen⟩ := h.noDead t
  obtain ⟨M', hf⟩ := enabled_iff_exists_fires.1 hen
  exact ⟨M, M', hM, hf, h.completion M' (hM.trans hf.reachable)⟩

/-- Weak soundness implies easy soundness. -/
theorem WeakSound.easy (h : N.WeakSound i o) : N.EasySound i o :=
  weakSound_iff.1 h _ (.refl _ _)

/-- Relaxed soundness implies easy soundness, if there is a transition. -/
theorem RelaxedSound.easy [Nonempty Transition] (h : N.RelaxedSound i o) : N.EasySound i o :=
  let ⟨_, _, hM, hf, hc⟩ := h (Classical.arbitrary Transition)
  hM.trans (hf.reachable.trans hc)

/-- Tokens in a place that no transition consumes from are never lost. -/
theorem Reachable.le_apply {M M' : Marking Place} {p : Place} (hp : ∀ t, N.pre t p = 0)
    (h : M ⇝[N] M') : M p ≤ M' p :=
  h.invariant (P := fun K => M p ≤ K p) (fun {K t K'} hf hK => by
    obtain ⟨R, rfl, rfl⟩ := hf
    simp only [Finsupp.add_apply, hp t] at hK ⊢
    omega) le_rfl

/-- If the sink has no output transition, weak soundness implies lazy soundness. -/
theorem LazySound.of_weak (hout : ∀ t, N.pre t o = 0) (h : N.WeakSound i o) :
    N.LazySound i o :=
  ⟨fun M hM => ⟨token o, weakSound_iff.1 h M hM, token_apply_self o⟩, fun M hM => by
    have := (weakSound_iff.1 h M hM).le_apply hout
    simpa [token_apply_self] using this⟩

/-- In a workflow net, a net is sound iff it is weakly sound and has no dead transition. -/
theorem IsWFNet.sound_iff (h : N.IsWFNet i o) :
    N.Sound i o ↔ N.WeakSound i o ∧ ∀ t, ∃ M, token i ⇝[N] M ∧ M [t⟩[N] :=
  ⟨fun hs => ⟨hs.weak, hs.noDead⟩, fun ⟨hw, hd⟩ =>
    ⟨weakSound_iff.1 hw, h.proper_of_completion (weakSound_iff.1 hw), hd⟩⟩

end PetriNet

end Cslib
