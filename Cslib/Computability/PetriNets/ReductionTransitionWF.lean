/-
Copyright (c) 2026 Morten Schou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Morten Schou
-/

module

public import Cslib.Computability.PetriNets.ReductionTransition
public import Cslib.Computability.PetriNets.SoundnessNotions

/-! # Fusion of parallel transitions in workflow nets

Deleting one of two parallel transitions (`PetriNet.ParallelTransitions`) preserves and reflects
the structure of a workflow net and its soundness, for the same source and sink. A path through the
deleted transition runs through its twin instead, as they have the same preset and postset, and
the reachable markings are unchanged.

## Main statements

- `PetriNet.ParallelTransitions.isWFNet_removeTransition_iff`: `N.removeTransition t₂` is a
  workflow net iff `N` is.
- `PetriNet.ParallelTransitions.sound_removeTransition_iff`: it is sound iff `N` is.

Eliminating a self-loop transition with a twin, which preserves reachable markings as well, does
not preserve the workflow structure: the transition `t : {a, b} → {a, b}` can be the only way from
`a` to `b`.
-/

@[expose] public section

namespace Cslib

namespace PetriNet

open LTS
open scoped PetriNet

variable {Place Transition : Type*}

/-- The arcs of the net with a transition deleted are the arcs of the net between the remaining
nodes. -/
theorem arc_removeTransition_iff (N : PetriNet Place Transition) (t₀ : Transition)
    (a b : Place ⊕ {t // t ≠ t₀}) :
    (N.removeTransition t₀).Arc a b ↔
      N.Arc (Sum.map id Subtype.val a) (Sum.map id Subtype.val b) := by
  rcases a with p | t <;> rcases b with q | u <;> exact Iff.rfl

namespace ParallelTransitions

variable {N : PetriNet Place Transition} {t₁ t₂ : Transition} {i o : Place}
  (h : N.ParallelTransitions t₁ t₂)
include h

/-- A path of the net lifts to a path of the net with `t₂` deleted, with `t₂` replaced by its
twin. -/
theorem reflTransGen_arc_removeTransition {a b : Place ⊕ Transition}
    (hab : Relation.ReflTransGen N.Arc a b) {a' b' : Place ⊕ {t // t ≠ t₂}}
    (ha : Sum.map id Subtype.val a' = a) (hb : Sum.map id Subtype.val b' = b) :
    Relation.ReflTransGen (N.removeTransition t₂).Arc a' b' := by
  classical
  let ψ : Place ⊕ Transition → Place ⊕ {t // t ≠ t₂} :=
    Sum.map id fun t => if ht : t = t₂ then ⟨t₁, h.1⟩ else ⟨t, ht⟩
  have hψφ : ∀ n, ψ (Sum.map id Subtype.val n) = n := by
    rintro (p | ⟨t, ht⟩)
    · rfl
    · simp [ψ, ht]
  have harc : ∀ x y, N.Arc x y → (N.removeTransition t₂).Arc (ψ x) (ψ y) := by
    intro x y hxy
    rcases x with p | t <;> rcases y with q | u
    · exact hxy.elim
    · by_cases hu : u = t₂
      · subst hu
        have : N.Arc (.inl p) (.inr t₁) := by
          change p ∈ N.pre t₁
          rw [h.2.1]
          exact hxy
        simpa [ψ, arc_removeTransition_iff] using this
      · simpa [ψ, hu, arc_removeTransition_iff] using hxy
    · by_cases ht : t = t₂
      · subst ht
        have : N.Arc (.inr t₁) (.inl q) := by
          change q ∈ N.post t₁
          rw [h.2.2]
          exact hxy
        simpa [ψ, arc_removeTransition_iff] using this
      · simpa [ψ, ht, arc_removeTransition_iff] using hxy
    · exact hxy.elim
  have key := Relation.ReflTransGen.lift (p := (N.removeTransition t₂).Arc) ψ harc _ _ hab
  subst ha hb
  simp only [Function.onFun, hψφ] at key
  exact key

/-- Deleting a parallel transition preserves and reflects the structure of a workflow net. -/
theorem isWFNet_removeTransition_iff :
    (N.removeTransition t₂).IsWFNet i o ↔ N.IsWFNet i o := by
  have hne : t₁ ≠ t₂ := h.1
  have hpre : ∀ p, N.Arc (.inl p) (.inr t₁) ↔ N.Arc (.inl p) (.inr t₂) := fun p => by
    change p ∈ N.pre t₁ ↔ p ∈ N.pre t₂
    rw [h.2.1]
  have hpost : ∀ p, N.Arc (.inr t₁) (.inl p) ↔ N.Arc (.inr t₂) (.inl p) := fun p => by
    change p ∈ N.post t₁ ↔ p ∈ N.post t₂
    rw [h.2.2]
  constructor
  · intro hN
    have hlift : ∀ a b : Place ⊕ {t // t ≠ t₂},
        Relation.ReflTransGen (N.removeTransition t₂).Arc a b →
        Relation.ReflTransGen N.Arc (Sum.map id Subtype.val a) (Sum.map id Subtype.val b) :=
      fun a b hab => Relation.ReflTransGen.lift (Sum.map id Subtype.val)
        (fun x y hxy => (arc_removeTransition_iff N t₂ x y).1 hxy) _ _ hab
    refine ⟨fun t => ?_, fun t => ?_, fun n => ?_, fun n => ?_⟩
    · by_cases ht : t = t₂
      · subst ht
        rw [← h.2.2]
        exact hN.no_input_source ⟨t₁, hne⟩
      · exact hN.no_input_source ⟨t, ht⟩
    · by_cases ht : t = t₂
      · subst ht
        rw [← h.2.1]
        exact hN.no_output_sink ⟨t₁, hne⟩
      · exact hN.no_output_sink ⟨t, ht⟩
    · rcases n with p | t
      · exact hlift _ _ (hN.reach_from_source (.inl p))
      · by_cases ht : t = t₂
        · subst ht
          rcases (hlift _ _ (hN.reach_from_source (.inr ⟨t₁, hne⟩))).cases_tail with
            h' | ⟨c, hc, hca⟩
          · exact absurd h' (by simp)
          · rcases c with p | _
            · exact hc.tail ((hpre p).1 hca)
            · exact hca.elim
        · exact hlift _ _ (hN.reach_from_source (.inr ⟨t, ht⟩))
    · rcases n with p | t
      · exact hlift _ _ (hN.reach_to_sink (.inl p))
      · by_cases ht : t = t₂
        · subst ht
          rcases (hlift _ _ (hN.reach_to_sink (.inr ⟨t₁, hne⟩))).cases_head with h' | ⟨c, hca, hc⟩
          · exact absurd h'.symm (by simp)
          · rcases c with p | _
            · exact Relation.ReflTransGen.head ((hpost p).1 hca) hc
            · exact hca.elim
        · exact hlift _ _ (hN.reach_to_sink (.inr ⟨t, ht⟩))
  · intro hN
    refine ⟨fun t => hN.no_input_source t.1, fun t => hN.no_output_sink t.1, fun n => ?_,
      fun n => ?_⟩
    · exact h.reflTransGen_arc_removeTransition (hN.reach_from_source _) rfl rfl
    · exact h.reflTransGen_arc_removeTransition (hN.reach_to_sink _) rfl rfl

/-- Deleting a parallel transition preserves and reflects soundness, for the same source and
sink. -/
theorem sound_removeTransition_iff :
    (N.removeTransition t₂).Sound i o ↔ N.Sound i o := by
  have hr : ∀ M M', (M ⇝[N.removeTransition t₂] M') ↔ M ⇝[N] M' :=
    fun _ _ => h.reachable_removeTransition_iff
  constructor
  · intro hs
    refine ⟨fun M hM => (hr _ _).1 (hs.completion M ((hr _ _).2 hM)), fun M hM hle =>
      hs.proper M ((hr _ _).2 hM) hle, fun t => ?_⟩
    by_cases ht : t = t₂
    · subst ht
      obtain ⟨M, hM, he⟩ := hs.noDead ⟨t₁, h.1⟩
      exact ⟨M, (hr _ _).1 hM, h.enabled_iff.1 he⟩
    · obtain ⟨M, hM, he⟩ := hs.noDead ⟨t, ht⟩
      exact ⟨M, (hr _ _).1 hM, he⟩
  · intro hs
    refine ⟨fun M hM => (hr _ _).2 (hs.completion M ((hr _ _).1 hM)), fun M hM hle =>
      hs.proper M ((hr _ _).1 hM) hle, fun t => ?_⟩
    obtain ⟨M, hM, he⟩ := hs.noDead t.1
    exact ⟨M, (hr _ _).2 hM, he⟩

end ParallelTransitions

end PetriNet

end Cslib
