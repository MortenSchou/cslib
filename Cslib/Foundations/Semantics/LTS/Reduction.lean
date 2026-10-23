/-
Copyright (c) 2026 Morten Schou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Morten Schou
-/

module

public import Cslib.Foundations.Semantics.LTS.Basic

/-! # State-dependent reduction of an LTS and stubborn sets

Partial-order reduction explores only some of the transitions at each state. A set of labels `T` is
*stubborn* at a state `s` if executions from `s` that avoid `T` neither disable an enabled label of
`T`, nor enable a disabled one, and the enabled labels of `T` commute with such executions.
Exploring only a stubborn set at each state preserves the reachable terminal states. The LTS need
not be deterministic: the commutation clause of `IsStubborn`, applied to the empty execution, makes
every enabled member of a stubborn set have a unique successor (`IsStubborn.eq_of_tr`).

## Main definitions

- `LTS.Enabled`: a label can be taken from a state (an alias of `LTS.HasOutLabel`).
- `LTS.reduced`: the LTS restricted to the labels selected at each state.
- `LTS.IsStubborn`: stubborn sets at a state.

## Main statements

- `LTS.exists_reduced_mTr_of_isTerminal`: if a terminal state is reachable by an execution, then it
  is reachable by one of the same length in the reduced LTS, provided that a stubborn set containing
  an enabled label is selected at every nonterminal state.
- `LTS.canReach_isTerminal_iff_reduced`: the reachability of a terminal state is the same in the
  LTS and in the reduced LTS.
- `LTS.IsStubborn.exists_split`: the first label of a stubborn set in an execution can be taken
  first.

Only the preservation of terminal states is proved here. There is no cycle proviso and no
visibility condition.

## References

* [A. Valmari, *Stubborn sets for reduced state space generation*][Valmari1991]
* [P. Godefroid, *Partial-Order Methods for the Verification of Concurrent Systems*][Godefroid1996]
-/

@[expose] public section

namespace Cslib.LTS

universe u v

variable {State : Type u} {Label : Type v} {lts : LTS State Label}

/-- The label `μ` is enabled at the state `s`: it can be taken from `s`. This is `LTS.HasOutLabel`
under the name customary for partial-order reduction. -/
abbrev Enabled (lts : LTS State Label) (s : State) (μ : Label) : Prop :=
  lts.HasOutLabel s μ

/-- `T` is stubborn at `s`: for every execution `σ` from `s` that avoids `T`, each label of `T`
that is enabled at `s` is enabled after `σ` and commutes with `σ`, and each label of `T` that is
disabled at `s` is disabled after `σ`.

This combines two conditions from the literature. The clause for enabled labels is Godefroid's
persistence: an enabled member stays enabled along executions outside `T`, and can be taken before
or after such an execution with the same result. The clause for disabled labels is Valmari's: a
disabled member cannot be enabled by an execution outside `T`. The latter is what makes a stubborn
set preserve terminal states. -/
def IsStubborn (lts : LTS State Label) (s : State) (T : Set Label) : Prop :=
  ∀ σ s', lts.MTr s σ s' → (∀ u ∈ σ, u ∉ T) → ∀ t ∈ T,
    (lts.Enabled s t → lts.Enabled s' t ∧
      ∀ s₁ s₁', lts.Tr s t s₁ → lts.Tr s' t s₁' → lts.MTr s₁ σ s₁') ∧
    (¬ lts.Enabled s t → ¬ lts.Enabled s' t)

/-- The LTS restricted to the labels selected by `S` at each state. -/
def reduced (lts : LTS State Label) (S : State → Set Label) : LTS State Label where
  Tr s μ s' := μ ∈ S s ∧ lts.Tr s μ s'

/-- Executions of the reduced LTS are executions of the LTS. -/
theorem MTr.of_reduced {S : State → Set Label} {s s' : State} {ρ : List Label}
    (h : (lts.reduced S).MTr s ρ s') : lts.MTr s ρ s' := by
  induction h with
  | refl => exact .refl
  | stepL htr _ ih => exact .stepL htr.2 ih

/-- An enabled member of a stubborn set has a unique successor. -/
theorem IsStubborn.eq_of_tr {s s₁ s₂ : State} {T : Set Label} {t : Label}
    (hT : lts.IsStubborn s T) (ht : t ∈ T) (h₁ : lts.Tr s t s₁) (h₂ : lts.Tr s t s₂) : s₁ = s₂ :=
  MTr.nil_eq _ (((hT [] s .refl (by simp only [List.not_mem_nil, false_imp_iff, implies_true]) t
    ht).1 ⟨_, h₁⟩).2 s₁ s₂ h₁ h₂)

/-- Selecting every label is stubborn in a deterministic LTS: the only execution that avoids all
labels is the empty one. -/
theorem isStubborn_univ [lts.Deterministic] (s : State) : lts.IsStubborn s Set.univ := by
  intro σ s' hσ hav t _
  obtain rfl : σ = [] := by
    cases σ with
    | nil => rfl
    | cons u _ => exact absurd (Set.mem_univ u) (hav u (List.mem_cons_self ..))
  obtain rfl := MTr.nil_eq _ hσ
  exact ⟨fun hen => ⟨hen, fun _ _ h₁ h₂ => by
    obtain rfl := Deterministic.deterministic _ _ _ _ h₁ h₂
    exact .refl⟩, fun h => h⟩

/-- The first label of a stubborn set `T` in an execution from `s` can be taken first: it is enabled
at `s`, and the rest of the execution is still possible after it. -/
theorem IsStubborn.exists_split {s s' : State} {T : Set Label} {σ : List Label}
    (hT : lts.IsStubborn s T) (h : lts.MTr s σ s') (hex : ∃ a ∈ σ, a ∈ T) :
    ∃ σ₁ a σ₂ sa, σ = σ₁ ++ a :: σ₂ ∧ a ∈ T ∧ (∀ u ∈ σ₁, u ∉ T) ∧ lts.Tr s a sa ∧
      lts.MTr sa (σ₁ ++ σ₂) s' := by
  classical
  obtain ⟨a, hfind⟩ : ∃ a, σ.find? (fun a => decide (a ∈ T)) = some a := by
    obtain ⟨a, ha, haT⟩ := hex
    exact Option.isSome_iff_exists.1 (List.find?_isSome.2 ⟨a, ha, decide_eq_true haT⟩)
  obtain ⟨haT, σ₁, σ₂, rfl, hσ₁⟩ := List.find?_eq_some_iff_append.1 hfind
  have haT := of_decide_eq_true haT
  have hσ₁ : ∀ u ∈ σ₁, u ∉ T := fun u hu hu' => by
    have := hσ₁ u hu
    rw [decide_eq_true hu'] at this
    exact absurd this (by decide)
  obtain ⟨s₁, h₁, h₂⟩ := MTr.split h
  obtain ⟨s₁', hs₁, h₃⟩ := MTr.cons_iff.1 h₂
  have hS := hT σ₁ s₁ h₁ hσ₁ a haT
  obtain ⟨sa, hsa⟩ : lts.Enabled s a := by
    by_contra hna
    exact hS.2 hna ⟨_, hs₁⟩
  exact ⟨σ₁, a, σ₂, sa, rfl, haT, hσ₁, hsa, ((hS.1 ⟨_, hsa⟩).2 sa s₁' hsa hs₁).comp _ h₃⟩

/-- Preservation of terminal states. If `S` selects a stubborn set at every state, and at every
nonterminal state the selected set contains an enabled label, then every terminal state reachable by
an execution is reachable by an execution of the same length in the reduced LTS. -/
theorem exists_reduced_mTr_of_isTerminal (S : State → Set Label)
    (hS : ∀ s, lts.IsStubborn s (S s))
    (hne : ∀ s, ¬ lts.IsTerminal s → ∃ t ∈ S s, lts.Enabled s t)
    {D : State} (hD : lts.IsTerminal D) (σ : List Label) (s : State)
    (h : lts.MTr s σ D) : ∃ ρ, (lts.reduced S).MTr s ρ D ∧ ρ.length = σ.length := by
  induction hn : σ.length generalizing σ s with
  | zero =>
    obtain rfl := List.length_eq_zero_iff.1 hn
    obtain rfl := MTr.nil_eq _ h
    exact ⟨[], .refl, rfl⟩
  | succ n ih =>
    have hnd : ¬ lts.IsTerminal s := by
      obtain _ | ⟨a, σ⟩ := σ
      · simp only [List.length_nil] at hn
        omega
      · obtain ⟨_, htr, _⟩ := MTr.cons_iff.1 h
        exact fun hd => hd a _ htr
    obtain ⟨t, htS, hten⟩ := hne s hnd
    by_cases hex : ∃ a ∈ σ, a ∈ S s
    · obtain ⟨σ₁, a, σ₂, sa, rfl, haS, -, hsa, hc⟩ := (hS s).exists_split h hex
      obtain ⟨ρ, hρ, hlen'⟩ := ih (σ₁ ++ σ₂) sa hc (by
        simp only [List.length_append, List.length_cons] at hn ⊢
        omega)
      exact ⟨a :: ρ, .stepL ⟨haS, hsa⟩ hρ, by
        simp only [List.length_cons] at hlen' ⊢
        omega⟩
    · push Not at hex
      exact absurd ((hS s σ D h hex t htS).1 hten).1 fun ⟨_, h'⟩ => hD _ _ h'

/-- A terminal state is reachable in the LTS iff it is reachable in the reduced LTS, if `S` selects
a stubborn set that contains an enabled label at every nonterminal state. -/
theorem canReach_isTerminal_iff_reduced (S : State → Set Label)
    (hS : ∀ s, lts.IsStubborn s (S s))
    (hne : ∀ s, ¬ lts.IsTerminal s → ∃ t ∈ S s, lts.Enabled s t) {s : State} :
    (∃ D, lts.IsTerminal D ∧ lts.CanReach s D) ↔
      ∃ D, lts.IsTerminal D ∧ (lts.reduced S).CanReach s D :=
  ⟨fun ⟨D, hD, σ, hσ⟩ =>
    let ⟨ρ, hρ, _⟩ := exists_reduced_mTr_of_isTerminal S hS hne hD σ s hσ
    ⟨D, hD, ρ, hρ⟩,
   fun ⟨D, hD, ρ, hρ⟩ => ⟨D, hD, ρ, hρ.of_reduced⟩⟩

end Cslib.LTS
