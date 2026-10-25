/-
Copyright (c) 2026 Morten Schou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Morten Schou
-/

module

public import Cslib.Foundations.Semantics.LTS.AmpleOmega

/-! # Ample sets and maximal paths

A *maximal path* of an LTS is an infinite sequence of states, each step of which is a transition,
or a stutter at a terminal state. This is the notion of path of the temporal logics of
`Cslib.Logics.Temporal`, and it includes the finite maximal executions, which end in a terminal
state. `Cslib.Foundations.Semantics.LTS.AmpleOmega` treats infinite executions. To also cover the
paths that end in a terminal state we add a loop with a fresh label at each terminal state, so that
a maximal path becomes an infinite execution, and check that the ample selector still satisfies
the conditions for the new LTS.

## Main definitions

- `LTS.IsMaxPath`: maximal paths.
- `LTS.stutterClosure`: the LTS with a loop labelled `none` at each terminal state.

## Main statements

- `LTS.IsAmpleStep.exists_reduced_isMaxPath`: every maximal path of an LTS has a maximal path in
  the reduction by an ample selector with the stepwise stubbornness and the cycle proviso, from the
  same state and with stuttering equivalent observations. `LTS.exists_reduced_isMaxPath` is the
  case of a deterministic LTS with `LTS.IsAmple`.
- `LTS.forall_isMaxPath_iff_reduced`, `LTS.exists_isMaxPath_iff_reduced`: a property of the
  sequences of observations that is invariant under stuttering holds on all, respectively on some,
  maximal path from a state iff it does in the reduced LTS. This is the form used for LTL without
  next-time in `Cslib.Logics.Temporal.LTL.AmpleSets`.
-/

@[expose] public section

namespace Cslib.LTS

open Cslib Cslib.ωSequence

universe u v w

variable {State : Type u} {Label : Type v} {lts : LTS State Label}

/-- A maximal path: each step is a transition, or a stutter at a terminal state. -/
def IsMaxPath (lts : LTS State Label) (f : ℕ → State) : Prop :=
  ∀ n, lts.UnlabelledTr (f n) (f (n + 1)) ∨ (lts.IsTerminal (f n) ∧ f (n + 1) = f n)

/-- The LTS with a loop labelled `none` at each terminal state. -/
def stutterClosure (lts : LTS State Label) : LTS State (Option Label) where
  Tr s μ s' := match μ with
    | some μ => lts.Tr s μ s'
    | none => lts.IsTerminal s ∧ s' = s

/-- The selector that extends `A` by the loop at the terminal states. -/
def stutterSel (lts : LTS State Label) (A : State → Set Label) (s : State) :
    Set (Option Label) :=
  {μ | match μ with
    | some μ => μ ∈ A s
    | none => lts.IsTerminal s}

/-- The invisible labels of the extension: those of `Inv` and the loops. -/
def stutterInv (Inv : Label → Prop) : Option Label → Prop
  | some μ => Inv μ
  | none => True

namespace stutterClosure

theorem tr_some {s s' : State} {μ : Label} :
    (stutterClosure lts).Tr s (some μ) s' ↔ lts.Tr s μ s' := Iff.rfl

theorem tr_none {s s' : State} :
    (stutterClosure lts).Tr s none s' ↔ lts.IsTerminal s ∧ s' = s := Iff.rfl

theorem enabled_none {s : State} :
    (stutterClosure lts).Enabled s none ↔ lts.IsTerminal s :=
  ⟨fun ⟨_, h, _⟩ => h, fun h => ⟨s, h, rfl⟩⟩

instance [lts.Deterministic] : (stutterClosure lts).Deterministic where
  deterministic _ μ s₁ s₂ h₁ h₂ := by
    cases μ with
    | none => exact h₁.2.trans h₂.2.symm
    | some μ => exact Deterministic.eq_of_tr (lts := lts) (tr_some.1 h₁) (tr_some.1 h₂)

/-- Multistep transitions of `lts` are multistep transitions of the extension. -/
theorem mTr_map_some {s s' : State} {σ : List Label} (h : lts.MTr s σ s') :
    (stutterClosure lts).MTr s (σ.map some) s' := by
  induction h with
  | refl => exact .refl
  | stepL htr _ ih => exact .stepL htr ih

variable {A : State → Set Label} {Inv : Label → Prop}

/-- A state is expanded for the extension of the selector iff it is expanded for the selector. -/
theorem isExpanded_iff {s : State} :
    (stutterClosure lts).IsExpanded (stutterSel lts A) s ↔ lts.IsExpanded A s := by
  refine ⟨fun h ν hν => h (some ν) hν, fun h μ hμ => ?_⟩
  cases μ with
  | none => exact enabled_none.1 hμ
  | some ν => exact h ν hμ

/-- An execution of the extension from a nonterminal state that avoids the selected labels of the
state is one of `lts`: the loop is not taken, since the selected enabled labels stay enabled. -/
theorem exists_mTr_map_some (hA : lts.IsAmple A Inv) {s : State} (hs : ¬ lts.IsTerminal s)
    (σ : List (Option Label)) {s' : State} (h : (stutterClosure lts).MTr s σ s')
    (hav : ∀ u ∈ σ, u ∉ stutterSel lts A s) :
    ∃ σ' : List Label, σ = σ'.map some ∧ lts.MTr s σ' s' ∧ ∀ u ∈ σ', u ∉ A s := by
  induction σ using List.reverseRecOn generalizing s' with
  | nil =>
    obtain rfl := MTr.nil_eq _ h
    exact ⟨[], rfl, .refl, by simp only [List.not_mem_nil, false_imp_iff, implies_true]⟩
  | append_singleton σ μ ih =>
    obtain ⟨s₁, h₁, h₂⟩ := MTr.split h
    obtain ⟨σ', rfl, hσ', hav'⟩ := ih h₁ fun u hu => hav u (List.mem_append_left _ hu)
    have htr := (MTr.singleton_iff _ _ _ _).1 h₂
    cases μ with
    | none =>
      obtain ⟨hterm, -⟩ := tr_none.1 htr
      obtain ⟨a, haA, hen⟩ := hA.nonempty s hs
      obtain ⟨w, hw⟩ := ((hA.stubborn s σ' s₁ hσ' hav' a haA).1 hen).1
      exact absurd hw (hterm _ _)
    | some ν =>
      have hν : ν ∉ A s := hav (some ν) (List.mem_append_right _ (List.mem_singleton_self _))
      refine ⟨σ' ++ [ν], by simp only [List.map_append, List.map_cons, List.map_nil],
        hσ'.comp _ (.single _ htr), fun u hu => ?_⟩
      rcases List.mem_append.1 hu with hu | hu
      · exact hav' u hu
      · rw [List.mem_singleton.1 hu]
        exact hν

/-- The extension of an ample selector is an ample selector for the extended LTS. -/
theorem isAmple (hA : lts.IsAmple A Inv) :
    (stutterClosure lts).IsAmple (stutterSel lts A) (stutterInv Inv) := by
  refine ⟨fun s hs => ?_, fun s => ?_, fun s hne μ hμ hen => ?_⟩
  · by_cases ht : lts.IsTerminal s
    · exact ⟨none, ht, enabled_none.2 ht⟩
    · obtain ⟨μ, hμ, hen⟩ := hA.nonempty s ht
      exact ⟨some μ, hμ, hen⟩
  · by_cases ht : lts.IsTerminal s
    · -- At a terminal state the only selected label that is taken is the loop.
      intro σ s' hσ hav t ht'
      have hσ0 : σ = [] ∧ s' = s := by
        cases σ with
        | nil => exact ⟨rfl, (MTr.nil_eq _ hσ).symm⟩
        | cons μ σ =>
          obtain ⟨s₂, htr, -⟩ := MTr.cons_iff.1 hσ
          cases μ with
          | none => exact absurd ht (hav none (List.mem_cons_self ..))
          | some ν => exact absurd htr (ht ν _)
      obtain ⟨rfl, rfl⟩ := hσ0
      refine ⟨fun hen => ⟨hen, fun s₁ s₁' h₁ h₂ => ?_⟩, fun h => h⟩
      cases t with
      | none =>
        obtain rfl := h₁.2.trans h₂.2.symm
        exact .refl
      | some ν => exact absurd h₁ (ht ν _)
    · intro σ s' hσ hav t ht'
      obtain ⟨σ', rfl, hσ', hav'⟩ := exists_mTr_map_some hA ht σ hσ hav
      cases t with
      | none => exact absurd ht' ht
      | some ν =>
        obtain ⟨h1, h2⟩ := (hA.stubborn s) σ' s' hσ' hav' ν ht'
        exact ⟨fun hen => ⟨(h1 hen).1, fun s₁ s₁' h₁ h₂' =>
          mTr_map_some ((h1 hen).2 s₁ s₁' h₁ h₂')⟩, h2⟩
  · cases μ with
    | none => exact trivial
    | some ν =>
      refine hA.invisible s (fun he => hne ?_) ν hμ hen
      exact isExpanded_iff.2 he

/-- The extension of a stepwise ample selector is a stepwise ample selector for the extended
LTS. -/
theorem isAmpleStep (hA : lts.IsAmpleStep A Inv) :
    (stutterClosure lts).IsAmpleStep (stutterSel lts A) (stutterInv Inv) := by
  refine ⟨(isAmple hA.toIsAmple).nonempty, fun s => ?_, (isAmple hA.toIsAmple).invisible⟩
  by_cases ht : lts.IsTerminal s
  · -- At a terminal state only the loop is taken, and it is deterministic.
    intro x ⟨σ, hσ, hav⟩
    obtain rfl : x = s := by
      cases σ with
      | nil => exact (MTr.nil_eq _ hσ).symm
      | cons μ σ =>
        obtain ⟨s₂, htr, -⟩ := MTr.cons_iff.1 hσ
        cases μ with
        | none => exact absurd ht (hav none (List.mem_cons_self ..))
        | some ν => exact absurd htr (ht ν _)
    intro t ht'
    refine ⟨fun s₁ s₂ h₁ h₂ => ?_, fun ν hν x' htr => ?_⟩
    · cases t with
      | none => exact h₁.2.trans h₂.2.symm
      | some ν => exact absurd h₁ (ht ν _)
    · cases ν with
      | none => exact absurd ht hν
      | some ν => exact absurd htr (ht ν _)
  · intro x ⟨σ, hσ, hav⟩
    obtain ⟨σ', rfl, hσ', hav'⟩ := exists_mTr_map_some hA.toIsAmple ht σ hσ hav
    intro t ht'
    cases t with
    | none => exact absurd ht' ht
    | some t =>
      obtain ⟨hdet, hloc⟩ := hA.stubborn s x ⟨σ', hσ', hav'⟩ t ht'
      refine ⟨fun y y' h₁ h₂ => hdet y y' h₁ h₂, fun ν hν x' htr => ?_⟩
      cases ν with
      | none =>
        obtain ⟨hterm, -⟩ := tr_none.1 htr
        obtain ⟨a, haA, hen⟩ := hA.nonempty s ht
        obtain ⟨w, hw⟩ := ((hA.toIsAmple.stubborn s σ' x hσ' hav' a haA).1 hen).1
        exact absurd hw (hterm _ _)
      | some ν => exact hloc ν hν x' htr

/-- The states that the reduced extension reaches are reached by the reduced LTS: the loops stay at
the same state. -/
theorem canReach_reduced {s t : State}
    (h : ((stutterClosure lts).reduced (stutterSel lts A)).CanReach s t) :
    (lts.reduced A).CanReach s t := by
  obtain ⟨ρ, hρ⟩ := h
  induction hρ with
  | refl => exact CanReach.refl _ _
  | @stepL s₁ μ s₂ _ _ htr _ ih =>
    cases μ with
    | none =>
      obtain rfl := htr.2.2
      exact ih
    | some ν =>
      obtain ⟨ρ', hρ'⟩ := ih
      exact ⟨ν :: ρ', .stepL htr hρ'⟩

/-- The cycle proviso for the extension: the loops are taken at terminal states, which are
expanded. -/
theorem cycleProviso {s₀ : State} (h3 : lts.CycleProviso A s₀) :
    (stutterClosure lts).CycleProviso (stutterSel lts A) s₀ := by
  intro t ht
  refine Subrelation.accessible (fun {s' s} h => ?_) (h3 t (canReach_reduced ht))
  obtain ⟨hne, μ, hμ, htr⟩ := h
  refine ⟨fun he => hne (isExpanded_iff.2 he), ?_⟩
  cases μ with
  | none => exact absurd (isExpanded_iff.2 fun ν ⟨s', h⟩ => absurd h (hμ ν s')) hne
  | some ν => exact ⟨ν, hμ, htr⟩

end stutterClosure

section MaxPath

variable {α : Type w} {ℓ : State → α} {A : State → Set Label} {Inv : Label → Prop}

/-- Maximal paths of the reduced LTS are maximal paths of the LTS, if the selector satisfies
`C0`. -/
theorem IsMaxPath.of_reduced (hA : lts.IsAmple A Inv) {f : ℕ → State}
    (hf : (lts.reduced A).IsMaxPath f) : lts.IsMaxPath f := fun n => by
  rcases hf n with ⟨μ, h⟩ | ⟨ht, he⟩
  · exact Or.inl ⟨μ, h.2⟩
  · have hterm : lts.IsTerminal (f n) := by
      by_contra hnt
      obtain ⟨a, haA, s', hs'⟩ := hA.nonempty (f n) hnt
      exact ht a s' ⟨haA, hs'⟩
    exact Or.inr ⟨hterm, he⟩

/-- Every maximal path of an LTS has a maximal path in the reduction by an ample selector with the
stepwise stubbornness and the cycle proviso, from the same state and with stuttering equivalent
observations `ℓ`, where `ℓ` is not changed by the invisible labels. This covers the paths that end
in a terminal state, which stutter there forever. The LTS need not be deterministic. -/
theorem IsAmpleStep.exists_reduced_isMaxPath {f : ℕ → State} (hA : lts.IsAmpleStep A Inv)
    (h3 : lts.CycleProviso A (f 0)) (hℓ : ∀ s μ s', lts.Tr s μ s' → Inv μ → ℓ s = ℓ s')
    (hf : lts.IsMaxPath f) :
    ∃ g : ℕ → State, (lts.reduced A).IsMaxPath g ∧ g 0 = f 0 ∧
      StutterEq ((f : ωSequence State).map ℓ) ((g : ωSequence State).map ℓ) := by
  have hex : ∀ n, ∃ μ : Option Label, (stutterClosure lts).Tr (f n) μ (f (n + 1)) := fun n => by
    rcases hf n with ⟨μ, h⟩ | ⟨ht, he⟩
    · exact ⟨some μ, h⟩
    · exact ⟨none, ht, he⟩
  choose μs hμs using hex
  have hℓ' : ∀ s μ s', (stutterClosure lts).Tr s μ s' → stutterInv Inv μ → ℓ s = ℓ s' := by
    intro s μ s' h hi
    cases μ with
    | none =>
      obtain ⟨-, rfl⟩ := h
      rfl
    | some μ => exact hℓ s μ s' h hi
  obtain ⟨gs, νs, hg, hg0, hst⟩ := (stutterClosure.isAmpleStep hA).exists_reduced_omegaExecution
    (stutterClosure.cycleProviso h3) hℓ'
    (ss := (f : ωSequence State)) (μs := (μs : ωSequence (Option Label))) hμs
  refine ⟨gs, fun n => ?_, hg0, hst⟩
  have hn := hg n
  cases hν : νs n with
  | none =>
    rw [hν] at hn
    obtain ⟨hmem, htr⟩ := hn
    exact Or.inr ⟨fun μ s' h => hmem μ s' h.2, htr.2⟩
  | some ν =>
    rw [hν] at hn
    exact Or.inl ⟨ν, hn⟩

/-- Every maximal path of a deterministic LTS has a maximal path in the reduction by an ample
selector with the cycle proviso, from the same state and with stuttering equivalent observations
`ℓ`, where `ℓ` is not changed by the invisible labels. -/
theorem exists_reduced_isMaxPath [lts.Deterministic] {f : ℕ → State} (hA : lts.IsAmple A Inv)
    (h3 : lts.CycleProviso A (f 0)) (hℓ : ∀ s μ s', lts.Tr s μ s' → Inv μ → ℓ s = ℓ s')
    (hf : lts.IsMaxPath f) :
    ∃ g : ℕ → State, (lts.reduced A).IsMaxPath g ∧ g 0 = f 0 ∧
      StutterEq ((f : ωSequence State).map ℓ) ((g : ωSequence State).map ℓ) :=
  hA.toIsAmpleStep.exists_reduced_isMaxPath h3 hℓ hf

/-- A property of sequences of observations that is invariant under stuttering holds on all
maximal paths from a state of an LTS iff it does on all maximal paths of the reduction by an ample
selector with the stepwise stubbornness and the cycle proviso. -/
theorem IsAmpleStep.forall_isMaxPath_iff_reduced {s : State} (hA : lts.IsAmpleStep A Inv)
    (h3 : lts.CycleProviso A s) (hℓ : ∀ s μ s', lts.Tr s μ s' → Inv μ → ℓ s = ℓ s')
    {P : ωSequence α → Prop} (hP : ∀ {x y}, StutterEq x y → (P x ↔ P y)) :
    (∀ f : ℕ → State, lts.IsMaxPath f → f 0 = s → P ((f : ωSequence State).map ℓ)) ↔
      ∀ g : ℕ → State, (lts.reduced A).IsMaxPath g → g 0 = s →
        P ((g : ωSequence State).map ℓ) := by
  refine ⟨fun h g hg hg0 => h g (IsMaxPath.of_reduced hA.toIsAmple hg) hg0, fun h f hf hf0 => ?_⟩
  obtain ⟨g, hg, hg0, hst⟩ := hA.exists_reduced_isMaxPath (hf0 ▸ h3) hℓ hf
  exact (hP hst).2 (h g hg (hg0.trans hf0))

/-- The existential version of `IsAmpleStep.forall_isMaxPath_iff_reduced`. -/
theorem IsAmpleStep.exists_isMaxPath_iff_reduced {s : State} (hA : lts.IsAmpleStep A Inv)
    (h3 : lts.CycleProviso A s) (hℓ : ∀ s μ s', lts.Tr s μ s' → Inv μ → ℓ s = ℓ s')
    {P : ωSequence α → Prop} (hP : ∀ {x y}, StutterEq x y → (P x ↔ P y)) :
    (∃ f : ℕ → State, lts.IsMaxPath f ∧ f 0 = s ∧ P ((f : ωSequence State).map ℓ)) ↔
      ∃ g : ℕ → State, (lts.reduced A).IsMaxPath g ∧ g 0 = s ∧
        P ((g : ωSequence State).map ℓ) := by
  refine ⟨fun ⟨f, hf, hf0, hP'⟩ => ?_, fun ⟨g, hg, hg0, hP'⟩ =>
    ⟨g, IsMaxPath.of_reduced hA.toIsAmple hg, hg0, hP'⟩⟩
  obtain ⟨g, hg, hg0, hst⟩ := hA.exists_reduced_isMaxPath (hf0 ▸ h3) hℓ hf
  exact ⟨g, hg, hg0.trans hf0, (hP hst).1 hP'⟩

/-- A property of sequences of observations that is invariant under stuttering holds on all
maximal paths from a state of a deterministic LTS iff it does on all maximal paths of the reduction
by an ample selector with the cycle proviso. -/
theorem forall_isMaxPath_iff_reduced [lts.Deterministic] {s : State} (hA : lts.IsAmple A Inv)
    (h3 : lts.CycleProviso A s) (hℓ : ∀ s μ s', lts.Tr s μ s' → Inv μ → ℓ s = ℓ s')
    {P : ωSequence α → Prop} (hP : ∀ {x y}, StutterEq x y → (P x ↔ P y)) :
    (∀ f : ℕ → State, lts.IsMaxPath f → f 0 = s → P ((f : ωSequence State).map ℓ)) ↔
      ∀ g : ℕ → State, (lts.reduced A).IsMaxPath g → g 0 = s →
        P ((g : ωSequence State).map ℓ) :=
  hA.toIsAmpleStep.forall_isMaxPath_iff_reduced h3 hℓ hP

/-- The existential version of `forall_isMaxPath_iff_reduced`. -/
theorem exists_isMaxPath_iff_reduced [lts.Deterministic] {s : State} (hA : lts.IsAmple A Inv)
    (h3 : lts.CycleProviso A s) (hℓ : ∀ s μ s', lts.Tr s μ s' → Inv μ → ℓ s = ℓ s')
    {P : ωSequence α → Prop} (hP : ∀ {x y}, StutterEq x y → (P x ↔ P y)) :
    (∃ f : ℕ → State, lts.IsMaxPath f ∧ f 0 = s ∧ P ((f : ωSequence State).map ℓ)) ↔
      ∃ g : ℕ → State, (lts.reduced A).IsMaxPath g ∧ g 0 = s ∧
        P ((g : ωSequence State).map ℓ) :=
  hA.toIsAmpleStep.exists_isMaxPath_iff_reduced h3 hℓ hP

end MaxPath

end Cslib.LTS
