/-
Copyright (c) 2026 Morten Schou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Morten Schou
-/

module

public import Cslib.Computability.PetriNets.Decision.Coverability
public import Cslib.Foundations.Data.Search
public import Cslib.Computability.PetriNets.Unboundedness

/-! # Decidable boundedness

For a net over finitely many places and transitions, boundedness is decidable. Search
level by level through the markings reachable in at most `n` steps, until either

* one more step adds no new marking (the reachable set is finite, so the net is bounded), or
* some marking reachable within `n` steps reaches a strictly larger one within `n` steps (a
  pumping pair, so the net is unbounded).

By the characterisation of unbounded nets via pumping pairs and by finiteness of reachable sets in
bounded nets, one of the two conditions eventually holds.

## Main definitions

- `PetriNet.reachSet`: the markings reachable in at most `n` steps.

## Main statements

- `PetriNet.instDecidableBounded`: boundedness is decidable.
-/

@[expose] public section

namespace Cslib

namespace PetriNet

variable {Place Transition : Type*} [DecidableEq Place] (N : PetriNet Place Transition)

/-- The markings reached by one more firing from some marking in `S`. -/
def stepSet [Fintype Transition] (S : Finset (Marking Place)) : Finset (Marking Place) :=
  S.biUnion fun M => Finset.univ.biUnion fun t => (N.fire? M t).toFinset

/-- The markings reachable from `M₀` in at most `n` steps. -/
def reachSet [Fintype Transition] (M₀ : Marking Place) : ℕ → Finset (Marking Place)
  | 0 => {M₀}
  | n + 1 => reachSet M₀ n ∪ N.stepSet (reachSet M₀ n)

theorem mem_reachSet_iff [Fintype Transition] {M₀ M : Marking Place} {n : ℕ} :
    M ∈ N.reachSet M₀ n ↔ ∃ ts : List Transition, ts.length ≤ n ∧ N.run M₀ ts = some M := by
  induction n generalizing M with
  | zero =>
    simp only [reachSet, Finset.mem_singleton, nonpos_iff_eq_zero, List.length_eq_zero_iff]
    constructor
    · rintro rfl; exact ⟨[], rfl, rfl⟩
    · rintro ⟨ts, rfl, h⟩; simpa [run] using h.symm
  | succ n ih =>
    simp only [reachSet, Finset.mem_union, stepSet, Finset.mem_biUnion, Finset.mem_univ, true_and,
      Option.mem_toFinset]
    constructor
    · rintro (h | ⟨M', hM', t, ht⟩)
      · obtain ⟨ts, hlen, hrun⟩ := ih.1 h
        exact ⟨ts, by omega, hrun⟩
      · obtain ⟨ts, hlen, hrun⟩ := ih.1 hM'
        refine ⟨ts ++ [t], by simp; omega, ?_⟩
        rw [run_append, hrun]
        simpa [run] using ht
    · rintro ⟨ts, hlen, hrun⟩
      rcases Nat.lt_or_ge ts.length (n + 1) with hlt | hge
      · exact Or.inl (ih.2 ⟨ts, by omega, hrun⟩)
      · obtain rfl | ⟨L, t, rfl⟩ := List.eq_nil_or_concat ts
        · simp at hge
        · rw [List.concat_eq_append] at hlen hrun hge
          rw [run_append] at hrun
          cases hL : N.run M₀ L with
          | none => simp [hL] at hrun
          | some M' =>
            simp only [hL, Option.bind_some, run] at hrun
            refine Or.inr ⟨M', ih.2 ⟨L, by simp at hlen; omega, hL⟩, t, ?_⟩
            simpa using hrun

theorem reachSet_mono [Fintype Transition] {M₀ : Marking Place} {m n : ℕ} (h : m ≤ n) :
    N.reachSet M₀ m ⊆ N.reachSet M₀ n := fun _ hx => by
  obtain ⟨ts, hlen, hrun⟩ := (mem_reachSet_iff N).1 hx
  exact (mem_reachSet_iff N).2 ⟨ts, hlen.trans h, hrun⟩

/-- One more step from the markings reachable in at most `n` steps adds nothing new. -/
def Closed [Fintype Transition] (M₀ : Marking Place) (n : ℕ) : Prop :=
  N.stepSet (N.reachSet M₀ n) ⊆ N.reachSet M₀ n

/-- Within `n` steps, a reachable marking reaches a strictly larger one. -/
def PumpWithin [Fintype Transition] (M₀ : Marking Place) (n : ℕ) : Prop :=
  ∃ M₁ ∈ N.reachSet M₀ n, ∃ M₂ ∈ N.reachSet M₁ n, M₁ ≤ M₂ ∧ M₁ ≠ M₂

instance [Fintype Transition] (M₀ : Marking Place) (n : ℕ) : Decidable (N.Closed M₀ n) :=
  inferInstanceAs (Decidable (N.stepSet (N.reachSet M₀ n) ⊆ N.reachSet M₀ n))

instance [Fintype Transition] (M₀ : Marking Place) (n : ℕ) : Decidable (N.PumpWithin M₀ n) :=
  inferInstanceAs
    (Decidable (∃ M₁ ∈ N.reachSet M₀ n, ∃ M₂ ∈ N.reachSet M₁ n, M₁ ≤ M₂ ∧ M₁ ≠ M₂))

theorem reachable_of_mem_reachSet [Fintype Transition] {M₀ M : Marking Place} {n : ℕ}
    (h : M ∈ N.reachSet M₀ n) :
    M₀ ⇝[N] M :=
  let ⟨ts, _, hrun⟩ := (mem_reachSet_iff N).1 h
  ⟨ts, run_eq_some_iff.1 hrun⟩

/-- At a closed level, firing sequences from the reachable markings stay inside the level. -/
theorem run_mem_of_closed [Fintype Transition] {M₀ : Marking Place} {n : ℕ} (hc : N.Closed M₀ n) :
    ∀ (ts : List Transition) (M₁ M₂ : Marking Place),
      M₁ ∈ N.reachSet M₀ n → N.run M₁ ts = some M₂ → M₂ ∈ N.reachSet M₀ n := by
  intro ts
  induction ts with
  | nil => intro M₁ M₂ h1 h2; simp only [run, Option.some.injEq] at h2; exact h2 ▸ h1
  | cons t ts ih =>
    intro M₁ M₂ h1 h2
    cases hf : N.fire? M₁ t with
    | none => simp [run, hf] at h2
    | some m =>
      simp only [run, hf, Option.bind_some] at h2
      refine ih m M₂ (hc ?_) h2
      exact Finset.mem_biUnion.2 ⟨M₁, h1, Finset.mem_biUnion.2
        ⟨t, Finset.mem_univ _, by simp [hf]⟩⟩

/-- At a closed level, every reachable marking lies in the level. -/
theorem mem_reachSet_of_reachable [Fintype Transition] {M₀ M : Marking Place} {n : ℕ}
    (hc : N.Closed M₀ n) (hr : M₀ ⇝[N] M) : M ∈ N.reachSet M₀ n :=
  let ⟨ts, hts⟩ := hr
  run_mem_of_closed N hc ts M₀ M ((mem_reachSet_iff N).2 ⟨[], Nat.zero_le _, rfl⟩)
    (run_eq_some_iff.2 hts)

/-- A closed level means the reachable set is finite, so the net is bounded. -/
theorem bounded_of_closed [Fintype Transition] {M₀ : Marking Place} {n : ℕ}
    (hc : N.Closed M₀ n) : N.Bounded M₀ :=
  bounded_of_finite_reachable
    ((N.reachSet M₀ n).finite_toSet.subset fun _ hX => mem_reachSet_of_reachable N hc hX)

/-- A pumping pair found within `n` steps shows the net is unbounded. -/
theorem not_bounded_of_pumpWithin [Fintype Transition] {M₀ : Marking Place} {n : ℕ}
    (hp : N.PumpWithin M₀ n) : ¬ N.Bounded M₀ :=
  let ⟨_, h₁, _, h₂, hle, hne⟩ := hp
  not_bounded_of_pump (reachable_of_mem_reachSet N h₁) (reachable_of_mem_reachSet N h₂)
    (lt_of_le_of_ne hle hne)

/-- Over finitely many places, a bounded net eventually has a closed level. -/
theorem exists_closed [Finite Place] [Fintype Transition] {M₀ : Marking Place}
    (hb : N.Bounded M₀) : ∃ n, N.Closed M₀ n := by
  have hex : ∀ M ∈ {M | M₀ ⇝[N] M}, ∃ n, M ∈ N.reachSet M₀ n := by
    rintro M ⟨ts, hts⟩
    exact ⟨ts.length, (mem_reachSet_iff N).2 ⟨ts, le_rfl, run_eq_some_iff.2 hts⟩⟩
  choose! g hg using hex
  obtain ⟨K, hK⟩ := Set.Finite.bddAbove (hb.finite_reachable.image g)
  refine ⟨K, fun x hx => ?_⟩
  obtain ⟨M, hM, hx⟩ := Finset.mem_biUnion.1 hx
  obtain ⟨t, -, hxt⟩ := Finset.mem_biUnion.1 hx
  have hxt' : N.fire? M t = some x := by simpa using hxt
  have hxr : M₀ ⇝[N] x :=
    (reachable_of_mem_reachSet N hM).trans (fire?_eq_some_iff.1 hxt').reachable
  exact reachSet_mono N (hK ⟨x, hxr, rfl⟩) (hg x hxr)

/-- Over finitely many places and transitions, an unbounded net has a pumping pair within some
number of steps. -/
theorem exists_pumpWithin [Finite Place] [Fintype Transition] {M₀ : Marking Place}
    (hb : ¬ N.Bounded M₀) : ∃ n, N.PumpWithin M₀ n := by
  obtain ⟨M₁, M₂, ⟨ts₁, h₁⟩, ⟨ts₂, h₂⟩, hlt⟩ := exists_pump_of_not_bounded hb
  refine ⟨max ts₁.length ts₂.length, M₁, ?_, M₂, ?_, hlt.le, hlt.ne⟩
  · exact reachSet_mono N (le_max_left _ _)
      ((mem_reachSet_iff N).2 ⟨ts₁, le_rfl, run_eq_some_iff.2 h₁⟩)
  · exact reachSet_mono N (le_max_right _ _)
      ((mem_reachSet_iff N).2 ⟨ts₂, le_rfl, run_eq_some_iff.2 h₂⟩)

/-- Over finitely many places, either some level is closed or some level contains a pumping
pair. -/
theorem exists_level [Finite Place] [Fintype Transition] (M₀ : Marking Place) :
    ∃ n, N.Closed M₀ n ∨ N.PumpWithin M₀ n := by
  by_cases hb : N.Bounded M₀
  · exact (exists_closed N hb).imp fun _ h => Or.inl h
  · exact (exists_pumpWithin N hb).imp fun _ h => Or.inr h

/-- Boundedness is decidable over finitely many places and transitions: search
for a level that is closed, which shows boundedness, or that contains a pumping pair, which shows
unboundedness. -/
instance instDecidableBounded [Fintype Place] [Fintype Transition] (M₀ : Marking Place) :
    Decidable (N.Bounded M₀) :=
  decidable_of_iff (N.Closed M₀ (searchNat (fun n => N.Closed M₀ n ∨ N.PumpWithin M₀ n)
    (exists_level N M₀))) (by
      refine ⟨bounded_of_closed N, fun hb => ?_⟩
      rcases searchNat_spec (fun n => N.Closed M₀ n ∨ N.PumpWithin M₀ n)
        (exists_level N M₀) with h | h
      · exact h
      · exact absurd hb (not_bounded_of_pumpWithin N h))

end PetriNet

end Cslib
