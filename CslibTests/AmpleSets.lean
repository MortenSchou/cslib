/-
Copyright (c) 2026 Morten Schou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Morten Schou
-/

import Cslib.Foundations.Semantics.LTS.AmpleSets

/-! # An ample selector on two independent counters

The generic partial-order reduction theory of `Cslib.Foundations.Semantics.LTS.AmpleSets`
applied to a toy LTS: two counters bounded by `n`, which are incremented independently. The
selector explores the left counter first, as long as it can be incremented. Incrementing the left
counter is invisible to the property "the right counter is full", so the reduced LTS reaches a
state with a full right counter iff the full LTS does.
-/

namespace CslibTests

namespace AmpleSets

open Cslib LTS

/-- Two counters bounded by `n`. The label `false` increments the left counter, and the label `true`
increments the right one. -/
def counters (n : ℕ) : LTS (ℕ × ℕ) Bool where
  Tr s μ s' := (μ = false ∧ s.1 < n ∧ s' = (s.1 + 1, s.2)) ∨
    (μ = true ∧ s.2 < n ∧ s' = (s.1, s.2 + 1))

/-- Increment the left counter while it can be incremented, and then the right one. -/
def sel (n : ℕ) (s : ℕ × ℕ) : Set Bool := if s.1 < n then {false} else {true}

/-- Right increments from a state `s` to `s'` leave the left counter unchanged and are possible
from the same right counter with any left counter. -/
private theorem mTr_right {n : ℕ} {s s' : ℕ × ℕ} {σ : List Bool}
    (h : (counters n).MTr s σ s') (hσ : ∀ u ∈ σ, u ∉ ({false} : Set Bool)) :
    s'.1 = s.1 ∧ ∀ c, (counters n).MTr (c, s.2) σ (c, s'.2) := by
  induction h with
  | refl => exact ⟨rfl, fun c => .refl⟩
  | @stepL s₁ μ s₂ μs s₃ htr _ ih =>
    obtain ⟨h₁, h₂⟩ := ih fun u hu => hσ u (List.mem_cons_of_mem _ hu)
    have hμ : μ = true := by simpa using hσ μ (List.mem_cons_self ..)
    obtain ⟨-, hlt, rfl⟩ : μ = true ∧ s₁.2 < n ∧ s₂ = (s₁.1, s₁.2 + 1) := by
      rcases htr with ⟨rfl, -⟩ | h
      · simp at hμ
      · exact h
    exact ⟨h₁, fun c => .stepL (Or.inr ⟨hμ, hlt, rfl⟩) (h₂ c)⟩

/-- The selector `sel n` satisfies `C0`–`C2`, with the left increments as invisible labels. -/
theorem isAmple (n : ℕ) : (counters n).IsAmple (sel n) (· = false) where
  nonempty s hs := by
    by_cases h1 : s.1 < n
    · exact ⟨false, by simp [sel, h1], (s.1 + 1, s.2), Or.inl ⟨rfl, h1, rfl⟩⟩
    · by_cases h2 : s.2 < n
      · exact ⟨true, by simp [sel, h1], (s.1, s.2 + 1), Or.inr ⟨rfl, h2, rfl⟩⟩
      · exact absurd (fun μ s' htr => by cases μ <;> grind [counters]) hs
  stubborn s := by
    intro σ s' hσ hav t ht
    by_cases h1 : s.1 < n
    · obtain rfl : t = false := by simpa [sel, h1] using ht
      obtain ⟨hs', hc⟩ := mTr_right hσ (by simpa [sel, h1] using hav)
      refine ⟨fun _ => ⟨⟨(s'.1 + 1, s'.2), Or.inl ⟨rfl, hs' ▸ h1, rfl⟩⟩, ?_⟩,
        fun hn => absurd ⟨(s.1 + 1, s.2), Or.inl ⟨rfl, h1, rfl⟩⟩ hn⟩
      rintro _ _ (⟨-, -, rfl⟩ | ⟨h, -⟩) (⟨-, -, rfl⟩ | ⟨h, -⟩)
      · simpa [hs'] using hc (s.1 + 1)
      all_goals simp at h
    · obtain rfl : t = true := by simpa [sel, h1] using ht
      obtain rfl : σ = [] := by
        cases σ with
        | nil => rfl
        | cons u σ =>
          obtain ⟨_, htr, -⟩ := MTr.cons_iff.1 hσ
          have hu : u = false := by simpa [sel, h1] using hav u (List.mem_cons_self ..)
          grind [counters]
      obtain rfl := MTr.nil_eq _ hσ
      refine ⟨fun hen => ⟨hen, ?_⟩, id⟩
      rintro _ _ (⟨h, -⟩ | ⟨-, -, rfl⟩) (⟨h, -⟩ | ⟨-, -, rfl⟩)
      · simp at h
      · simp at h
      · simp at h
      · exact .refl
  invisible s hne μ hμ hen := by
    by_cases h1 : s.1 < n
    · simpa [sel, h1] using hμ
    · refine absurd (fun μ' ⟨s', htr⟩ => ?_) hne
      have : μ' = true := by cases μ' <;> grind [counters]
      simp [sel, h1, this]

/-- `C3`: every step of the reduced counters from an unexpanded state increases a counter below its
bound, so the measure of the remaining increments decreases. -/
theorem cycleProviso (n : ℕ) (s₀ : ℕ × ℕ) : (counters n).CycleProviso (sel n) s₀ :=
  .of_measure (fun s => (n - s.1) + (n - s.2)) fun s s' _ ⟨_, μ, hμ, htr⟩ => by
    rcases htr with ⟨-, h, rfl⟩ | ⟨-, h, rfl⟩ <;> simp only <;> omega

/-- The reduced counters reach a state with a full right counter iff the counters do. -/
example (n : ℕ) (s : ℕ × ℕ) :
    (∃ s', (counters n).CanReach s s' ∧ n ≤ s'.2) ↔
      ∃ s', ((counters n).reduced (sel n)).CanReach s s' ∧ n ≤ s'.2 :=
  canReach_iff_reduced (isAmple n) (cycleProviso n s) fun s μ s' htr hμ => by
    rcases htr with ⟨-, -, rfl⟩ | ⟨h, -⟩
    · exact Iff.rfl
    · simp [hμ] at h

end AmpleSets

end CslibTests
