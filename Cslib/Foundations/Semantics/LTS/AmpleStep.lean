/-
Copyright (c) 2026 Morten Schou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Morten Schou
-/

module

public import Cslib.Foundations.Semantics.LTS.AmpleSets

/-! # Stepwise stubborn sets and ample selectors

`LTS.IsStubborn` (in `Cslib.Foundations.Semantics.LTS.Reduction`) quantifies over whole executions
that avoid the stubborn set. The results on infinite executions
(`Cslib.Foundations.Semantics.LTS.AmpleOmega`) need the diamond condition one step at a time, which
is what this file provides.

## Main definitions

- `LTS.AvoidReach`: a state is reached by an execution that avoids a set of labels.
- `LTS.StubbornStepAt`, `LTS.IsStubbornStep`: the stepwise stubbornness of a set of labels. It is
  stronger than `LTS.IsStubborn` (`IsStubbornStep.isStubborn`), and the same for a deterministic LTS
  (`IsStubborn.isStubbornStep`).
- `LTS.IsAmpleStep`: the conditions `C0`, `C1` and `C2` of `LTS.IsAmple` with the stepwise
  stubbornness as `C1`. It is more than `LTS.IsAmple` (`IsAmpleStep.toIsAmple`), and the same for a
  deterministic LTS (`IsAmple.toIsAmpleStep`).
-/

@[expose] public section

namespace Cslib.LTS

universe u v

variable {State : Type u} {Label : Type v} {lts : LTS State Label}

/-- The state `x` is reached from `s` by an execution that avoids `T`. -/
def AvoidReach (lts : LTS State Label) (T : Set Label) (s x : State) : Prop :=
  ∃ σ, lts.MTr s σ x ∧ ∀ u ∈ σ, u ∉ T

theorem AvoidReach.refl (T : Set Label) (s : State) : lts.AvoidReach T s s :=
  ⟨[], .refl, fun _ hu => absurd hu (List.not_mem_nil)⟩

theorem AvoidReach.tail {T : Set Label} {s x x' : State} {ν : Label} (h : lts.AvoidReach T s x)
    (hν : ν ∉ T) (htr : lts.Tr x ν x') : lts.AvoidReach T s x' :=
  let ⟨σ, hσ, hav⟩ := h
  ⟨σ ++ [ν], hσ.comp _ (.single _ htr), fun u hu => by
    rcases List.mem_append.1 hu with hu | hu
    · exact hav u hu
    · rw [List.mem_singleton.1 hu]
      exact hν⟩

/-- The stepwise condition for `T` at `x`: the members of `T` are deterministic at `x`, and for a
step of `x` that is not in `T`, a disabled member stays disabled, and an enabled member can be
taken after the step, to reach the state that the step reaches from the successor of `x` by the
member. -/
def StubbornStepAt (lts : LTS State Label) (T : Set Label) (x : State) : Prop :=
  ∀ t ∈ T, lts.DeterministicStateLabel x t ∧ ∀ ν, ν ∉ T → ∀ x', lts.Tr x ν x' →
    (¬ lts.Enabled x t → ¬ lts.Enabled x' t) ∧
    ∀ y, lts.Tr x t y → ∃ y', lts.Tr y ν y' ∧ lts.Tr x' t y'

/-- `T` is stubborn at `s` in the stepwise sense: the stepwise condition `StubbornStepAt` holds at
every state that is reached from `s` by an execution that avoids `T`.

This is stronger than `IsStubborn` (`IsStubbornStep.isStubborn`), and is the same for a
deterministic LTS (`IsStubborn.isStubbornStep`). It does not identify the intermediate states of
executions, and so also applies to LTSs that are not deterministic, if the members of `T` are
deterministic where they matter. -/
def IsStubbornStep (lts : LTS State Label) (s : State) (T : Set Label) : Prop :=
  ∀ x, lts.AvoidReach T s x → lts.StubbornStepAt T x

/-- The stepwise stubbornness implies stubbornness. -/
theorem IsStubbornStep.isStubborn {s : State} {T : Set Label} (hT : lts.IsStubbornStep s T) :
    lts.IsStubborn s T := by
  have key : ∀ (σ : List Label) (x₀ x : State), lts.AvoidReach T s x₀ → lts.MTr x₀ σ x →
      (∀ u ∈ σ, u ∉ T) → ∀ t ∈ T,
      (lts.Enabled x₀ t → lts.Enabled x t ∧ ∀ y y', lts.Tr x₀ t y → lts.Tr x t y' →
        lts.MTr y σ y') ∧ (¬ lts.Enabled x₀ t → ¬ lts.Enabled x t) := by
    intro σ
    induction σ with
    | nil =>
      intro x₀ x hx h _ t ht
      obtain rfl := MTr.nil_eq _ h
      exact ⟨fun hen => ⟨hen, fun y y' h₁ h₂ => by
        obtain rfl := (hT x₀ hx t ht).1 y y' h₁ h₂
        exact .refl⟩, id⟩
    | cons ν σ ih =>
      intro x₀ x hx h hav t ht
      obtain ⟨x₁, hν, h'⟩ := MTr.cons_iff.1 h
      have hνT : ν ∉ T := hav ν (List.mem_cons_self ..)
      have ih' := ih x₁ x (hx.tail hνT hν) h' (fun u hu => hav u (List.mem_cons_of_mem _ hu)) t ht
      have loc := ((hT x₀ hx t ht).2 ν hνT x₁ hν)
      refine ⟨fun ⟨y, hy⟩ => ?_, fun hn he => ih'.2 (loc.1 hn) he⟩
      obtain ⟨y₁, hy₁, hy₂⟩ := loc.2 y hy
      obtain ⟨hen, hc⟩ := ih'.1 ⟨_, hy₂⟩
      exact ⟨hen, fun z z' h₁ h₂ => by
        obtain rfl := (hT x₀ hx t ht).1 y z hy h₁
        exact .stepL hy₁ (hc y₁ z' hy₂ h₂)⟩
  intro σ s' hσ hav t ht
  exact key σ s s' (.refl T s) hσ hav t ht

/-- In a deterministic LTS, stubbornness implies the stepwise stubbornness. -/
theorem IsStubborn.isStubbornStep [lts.Deterministic] {s : State} {T : Set Label}
    (hT : lts.IsStubborn s T) : lts.IsStubbornStep s T := by
  intro x ⟨σ, hσ, hav⟩ t ht
  refine ⟨Deterministic.deterministic x t, fun ν hν x' hx' => ?_⟩
  have h₁ := hT σ x hσ hav t ht
  have hσ' : lts.MTr s (σ ++ [ν]) x' := hσ.comp _ (.single _ hx')
  have h₂ := hT (σ ++ [ν]) x' hσ' (fun u hu => by
    rcases List.mem_append.1 hu with hu | hu
    · exact hav u hu
    · rw [List.mem_singleton.1 hu]
      exact hν) t ht
  refine ⟨fun hn he => ?_, fun y hy => ?_⟩
  · by_cases hs : lts.Enabled s t
    · exact hn (h₁.1 hs).1
    · exact h₂.2 hs he
  · obtain ⟨u, hu⟩ : lts.Enabled s t := by
      by_contra hs
      exact h₁.2 hs ⟨y, hy⟩
    obtain ⟨y', hy'⟩ := (h₂.1 ⟨u, hu⟩).1
    have c₁ := (h₁.1 ⟨u, hu⟩).2 u y hu hy
    obtain ⟨m, hm, hm'⟩ := MTr.split ((h₂.1 ⟨u, hu⟩).2 u y' hu hy')
    obtain rfl := Deterministic.eq_of_mTr c₁ hm
    exact ⟨y', (MTr.singleton_iff _ _ _ _).1 hm', hy'⟩

/-- The conditions `C0`, `C1` and `C2` with the stepwise stubbornness `LTS.IsStubbornStep` as `C1`.
This is more than `IsAmple` (`IsAmpleStep.toIsAmple`), and the same for a deterministic LTS
(`IsAmple.toIsAmpleStep`). It is the hypothesis of the results on infinite executions, which then
also hold for LTSs that are not deterministic. -/
structure IsAmpleStep (lts : LTS State Label) (A : State → Set Label) (Inv : Label → Prop) :
    Prop where
  /-- `C0`: at a nonterminal state some selected label is enabled. -/
  nonempty : ∀ s, ¬ lts.IsTerminal s → ∃ μ ∈ A s, lts.Enabled s μ
  /-- `C1`: the selected set is stubborn in the stepwise sense. -/
  stubborn : ∀ s, lts.IsStubbornStep s (A s)
  /-- `C2`: unless the state is fully expanded, the enabled selected labels are invisible. -/
  invisible : ∀ s, ¬ lts.IsExpanded A s → ∀ μ ∈ A s, lts.Enabled s μ → Inv μ

theorem IsAmpleStep.toIsAmple {A : State → Set Label} {Inv : Label → Prop}
    (h : lts.IsAmpleStep A Inv) : lts.IsAmple A Inv :=
  ⟨h.nonempty, fun s => (h.stubborn s).isStubborn, h.invisible⟩

theorem IsAmple.toIsAmpleStep [lts.Deterministic] {A : State → Set Label} {Inv : Label → Prop}
    (h : lts.IsAmple A Inv) : lts.IsAmpleStep A Inv :=
  ⟨h.nonempty, fun s => (h.stubborn s).isStubbornStep, h.invisible⟩

end Cslib.LTS
