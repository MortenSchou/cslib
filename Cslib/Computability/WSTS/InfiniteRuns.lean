/-
Copyright (c) 2026 Morten Schou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Morten Schou
-/

module

public import Cslib.Computability.WSTS.Basic

/-! # Infinite runs of well-structured transition systems

A well-quasi-order forces every infinite sequence of states to contain an increasing pair. Applied
to an infinite run, this gives a state that reaches, in at least one step, a larger state; by
monotonicity such a state can be iterated forever. This characterises the existence of an infinite
run, which is the basis of the decidability of termination for WSTS.

## Main statements

- `Cslib.WSTS.exists_increasing_of_run`: an infinite run contains `s₁ ⇝⁺ s₂` with `s₁ ≤ s₂`.
- `Cslib.WSTS.exists_run_iff`: a state starts an infinite run exactly when it reaches some `s₁`
  with `s₁ ⇝⁺ s₂` and `s₁ ≤ s₂`.

## References

* [A. Finkel, P. Schnoebelen, *Well-structured transition systems everywhere!*]
  [FinkelSchnoebelen2001]
-/

@[expose] public section

namespace Cslib

namespace WSTS

open Relation

variable {State : Type*} {Label : Type*} [Preorder State] {lts : LTS State Label}

/-- Monotonicity lifts to one or more unlabelled steps. -/
theorem transGen_mono [StronglyMonotone lts] {s₁ s₁' s₂ : State}
    (h : TransGen lts.UnlabelledTr s₁ s₁')
    (hle : s₁ ≤ s₂) : ∃ s₂', TransGen lts.UnlabelledTr s₂ s₂' ∧ s₁' ≤ s₂' := by
  induction h generalizing s₂ with
  | single hstep =>
    obtain ⟨s₂', h₂, hle'⟩ := unlabelledTr_mono hstep hle
    exact ⟨s₂', .single h₂, hle'⟩
  | tail _ hstep ih =>
    obtain ⟨s₂', h₂, hle'⟩ := ih hle
    obtain ⟨s₃', h₃, hle''⟩ := unlabelledTr_mono hstep hle'
    exact ⟨s₃', h₂.tail h₃, hle''⟩

omit [Preorder State] in
/-- Along an infinite run, a later state is reachable in at least one step from an earlier one. -/
theorem transGen_of_run {f : ℕ → State} (hf : ∀ n, lts.UnlabelledTr (f n) (f (n + 1))) {i j : ℕ}
    (hij : i < j) : TransGen lts.UnlabelledTr (f i) (f j) := by
  induction j, hij using Nat.le_induction with
  | base => exact .single (hf i)
  | succ j _ ih => exact ih.tail (hf j)

/-- Every infinite run of a WSTS contains two positions `i < j` with `f i ≤ f j`. -/
theorem exists_increasing_of_run [WellQuasiOrderedLE State] {f : ℕ → State}
    (hf : ∀ n, lts.UnlabelledTr (f n) (f (n + 1))) :
    ∃ i j, TransGen lts.UnlabelledTr (f i) (f j) ∧ f i ≤ f j :=
  let ⟨i, j, hij, hle⟩ := wellQuasiOrdered_le f
  ⟨i, j, transGen_of_run hf hij, hle⟩

/-- A state starts an infinite run exactly when it reaches a state that reaches, in at least one
step, a larger state. -/
theorem exists_run_iff [WSTS lts] (s₀ : State) :
    (∃ f : ℕ → State, f 0 = s₀ ∧ ∀ n, lts.UnlabelledTr (f n) (f (n + 1))) ↔
      ∃ s₁ s₂, ReflTransGen lts.UnlabelledTr s₀ s₁ ∧ TransGen lts.UnlabelledTr s₁ s₂ ∧ s₁ ≤ s₂ := by
  constructor
  · rintro ⟨f, rfl, hf⟩
    obtain ⟨i, j, hij, hle⟩ := exists_increasing_of_run hf
    have hreach : ∀ i, ReflTransGen lts.UnlabelledTr (f 0) (f i) := fun i => by
      induction i with
      | zero => exact .refl
      | succ i ih => exact ih.tail (hf i)
    exact ⟨f i, f j, hreach i, hij, hle⟩
  · rintro ⟨s₁, s₂, h₀, h₁, hle⟩
    -- `Q s`: `s` reaches a state that reaches a larger state in at least one step
    let Q : State → Prop := fun s =>
      ∃ w w', ReflTransGen lts.UnlabelledTr s w ∧ TransGen lts.UnlabelledTr w w' ∧ w ≤ w'
    have hQ : ∀ s, Q s → ∃ s', lts.UnlabelledTr s s' ∧ Q s' := by
      rintro s ⟨w, w', hsw, hww', hle⟩
      -- the larger state `w'` again reaches a larger state
      obtain ⟨w'', hw'w'', hle'⟩ := transGen_mono hww' hle
      rcases hsw.cases_head with rfl | ⟨u, hsu, huw⟩
      · obtain ⟨u, hwu, huw'⟩ := TransGen.head'_iff.1 hww'
        exact ⟨u, hwu, w', w'', huw', hw'w'', hle'⟩
      · exact ⟨u, hsu, w, w', huw, hww', hle⟩
    have hQ₀ : Q s₀ := ⟨s₁, s₂, h₀, h₁, hle⟩
    have : Nonempty State := ⟨s₀⟩
    choose! next hstep hnext using hQ
    let f : ℕ → State := fun n => next^[n] s₀
    have hfQ : ∀ n, Q (f n) := fun n => by
      induction n with
      | zero => exact hQ₀
      | succ n ih =>
        rw [show f (n + 1) = next (f n) from Function.iterate_succ_apply' next n s₀]
        exact hnext _ ih
    refine ⟨f, rfl, fun n => ?_⟩
    rw [show f (n + 1) = next (f n) from Function.iterate_succ_apply' next n s₀]
    exact hstep _ (hfQ n)

end WSTS

end Cslib
