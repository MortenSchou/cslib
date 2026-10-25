/-
Copyright (c) 2026 Morten Schou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Morten Schou
-/

module

public import Cslib.Computability.WSTS.Basic
public import Cslib.Foundations.Semantics.LTS.Relation

/-! # Infinitely many reachable states give a pumping pair

In a finitely branching transition system on a well-quasi-ordered partial order, an infinite set of
reachable states forces a *pumping pair*: a reachable state `s₁` that reaches a strictly larger
state `s₂`. This is the König-style half of the characterisation of unbounded Petri nets and
vector addition systems.

Assume there is no pumping pair. Strongly connected components of reachable states are then
finite, since an infinite one would contain a comparable pair by the well-quasi-order. Hence a
reachable state with infinitely many successors reaches another such state that cannot reach it
back, which builds an infinite chain of reachable states leaving its strongly connected component
at every step. The well-quasi-order applied to this chain yields the contradiction.

The argument uses only the well-quasi-order and the finite branching, not monotonicity. The
converse (a pumping pair gives infinitely many reachable states) needs monotonicity and a
*strictly* increasing pump, and does not hold in general: in the system on `{0, 1}` with `0 < 1`
and steps `0 → 1` and `1 → 1`, the state `0` reaches the strictly larger `1`, but only finitely
many states are reachable.

## Main statements

- `Cslib.WSTS.finite_unlabelledTr`: a finitely branching state has finitely many successors.
- `Cslib.WSTS.exists_pump_of_infinite_reachable`: infinitely many reachable states give a pumping
  pair.

## References

* [R. M. Karp, R. E. Miller, *Parallel Program Schemata*][KarpMiller1969]
-/

@[expose] public section

namespace Cslib

namespace WSTS

variable {State : Type*} {Label : Type*} {lts : LTS State Label}

/-- In a finitely branching LTS, a state has finitely many successors. -/
theorem finite_unlabelledTr [lts.FinitelyBranching] (s : State) :
    {s' | lts.UnlabelledTr s s'}.Finite := by
  have : Finite (lts.outgoingLabels s) := inferInstance
  refine (Set.finite_iUnion fun μ : lts.outgoingLabels s => (lts.image s μ).toFinite).subset ?_
  rintro s' ⟨μ, h⟩
  exact Set.mem_iUnion.2 ⟨⟨μ, s', h⟩, h⟩

/-- A single unlabelled step is a reachability step. -/
theorem canReach_of_unlabelledTr {s s' : State} (h : lts.UnlabelledTr s s') : lts.CanReach s s' :=
  let ⟨_, h⟩ := h
  canReach_of_tr h

variable [PartialOrder State] [WellQuasiOrderedLE State]

/-- Without a pumping pair, the states mutually reachable with a reachable state `s` are finite:
otherwise the well-quasi-order would yield two comparable ones. -/
theorem scc_finite {s₀ s : State}
    (hnp : ∀ s₁ s₂, lts.CanReach s₀ s₁ → lts.CanReach s₁ s₂ → ¬ s₁ < s₂)
    (hs : lts.CanReach s₀ s) : {s' | lts.CanReach s s' ∧ lts.CanReach s' s}.Finite := by
  by_contra hinf
  let f := Set.Infinite.natEmbedding _ hinf
  obtain ⟨i, j, hij, hle⟩ := wellQuasiOrdered_le fun n => (f n).1
  have hne : (f i).1 ≠ (f j).1 := fun h => hij.ne (f.injective (Subtype.ext h))
  refine hnp (f i).1 (f j).1 (canReach_trans hs (f i).2.1)
    (canReach_trans (f i).2.2 (f j).2.1) ?_
  exact lt_of_le_of_ne hle hne

/-- Without a pumping pair, a reachable state with infinitely many successors can reach another
state with infinitely many successors that cannot reach it back. -/
theorem exists_next [lts.FinitelyBranching] {s₀ s : State}
    (hnp : ∀ s₁ s₂, lts.CanReach s₀ s₁ → lts.CanReach s₁ s₂ → ¬ s₁ < s₂)
    (hs : lts.CanReach s₀ s) (hinf : {z | lts.CanReach s z}.Infinite) :
    ∃ y, lts.CanReach s y ∧ ¬ lts.CanReach y s ∧ {z | lts.CanReach y z}.Infinite := by
  by_contra hcon
  push Not at hcon
  have hscc := scc_finite hnp hs
  have hsub : {z | lts.CanReach s z} ⊆ {s' | lts.CanReach s s' ∧ lts.CanReach s' s} ∪
      ⋃ s' ∈ {s' | lts.CanReach s s' ∧ lts.CanReach s' s},
        ⋃ y ∈ {y | lts.UnlabelledTr s' y ∧ ¬ lts.CanReach y s}, {z | lts.CanReach y z} := by
    intro z hz
    have key : ∀ z, Relation.ReflTransGen lts.UnlabelledTr s z →
        (lts.CanReach s z ∧ lts.CanReach z s) ∨
        ∃ s', (lts.CanReach s s' ∧ lts.CanReach s' s) ∧ ∃ y, lts.UnlabelledTr s' y ∧
          ¬ lts.CanReach y s ∧ lts.CanReach y z := by
      intro z hz
      induction hz with
      | refl => exact Or.inl ⟨.refl lts s, .refl lts s⟩
      | tail hz hstep ih =>
        rename_i z' w
        rcases ih with hs | ⟨s', hs', y, hy, hn, hyz⟩
        · by_cases hw : lts.CanReach w s
          · exact Or.inl ⟨canReach_trans hs.1 (canReach_of_unlabelledTr hstep), hw⟩
          · exact Or.inr ⟨z', hs, w, hstep, hw, .refl lts w⟩
        · exact Or.inr ⟨s', hs', y, hy, hn, canReach_trans hyz (canReach_of_unlabelledTr hstep)⟩
    rcases key z ((LTS.reflTransGen_unlabelledTr_iff lts).2 hz) with
        hs | ⟨s', hs', y, hy, hn, hyz⟩
    · exact Or.inl hs
    · exact Or.inr (Set.mem_biUnion hs' (Set.mem_biUnion ⟨hy, hn⟩ hyz))
  refine hinf (((hscc.union (hscc.biUnion fun s' hs' => ?_))).subset hsub)
  refine ((finite_unlabelledTr s').subset
    fun y (hy : y ∈ {y | lts.UnlabelledTr s' y ∧ ¬ lts.CanReach y s}) => hy.1).biUnion
    fun y hy => ?_
  exact hcon y (canReach_trans hs'.1 (canReach_of_unlabelledTr hy.1)) hy.2

/-- In a finitely branching transition system on a well-quasi-ordered partial order, infinitely
many reachable states give a pumping pair: a reachable state that reaches a strictly larger one. -/
theorem exists_pump_of_infinite_reachable [lts.FinitelyBranching] {s₀ : State}
    (hR : {s | lts.CanReach s₀ s}.Infinite) :
    ∃ s₁ s₂, lts.CanReach s₀ s₁ ∧ lts.CanReach s₁ s₂ ∧ s₁ < s₂ := by
  by_contra hex
  have hnp : ∀ s₁ s₂, lts.CanReach s₀ s₁ → lts.CanReach s₁ s₂ → ¬ s₁ < s₂ :=
    fun s₁ s₂ h1 h2 hlt => hex ⟨s₁, s₂, h1, h2, hlt⟩
  let S : Set State := {s | lts.CanReach s₀ s ∧ {z | lts.CanReach s z}.Infinite}
  have hS : ∀ s ∈ S, ∃ y ∈ S, lts.CanReach s y ∧ ¬ lts.CanReach y s := by
    rintro s ⟨hs, hinf⟩
    obtain ⟨y, hy, hn, hyinf⟩ := exists_next hnp hs hinf
    exact ⟨y, ⟨canReach_trans hs hy, hyinf⟩, hy, hn⟩
  choose! next hnextS hnextR hnextN using hS
  let g : ℕ → S := fun n =>
    Nat.rec ⟨s₀, .refl lts s₀, hR⟩
      (fun _ x => ⟨next x.1, hnextS x.1 x.2⟩) n
  let f : ℕ → State := fun n => (g n).1
  have hf0 : ∀ n, lts.CanReach s₀ (f n) := fun n => (g n).2.1
  have hstep : ∀ n, lts.CanReach (f n) (f (n + 1)) := fun n => hnextR _ (g n).2
  have hstepN : ∀ n, ¬ lts.CanReach (f (n + 1)) (f n) := fun n => hnextN _ (g n).2
  have hfwd : ∀ i j, i ≤ j → lts.CanReach (f i) (f j) := by
    intro i j hij
    induction j, hij using Nat.le_induction with
    | base => exact .refl lts _
    | succ j _ ih => exact canReach_trans ih (hstep j)
  obtain ⟨i, j, hij, hle⟩ := wellQuasiOrdered_le f
  have heq : f i = f j := by
    by_contra hne
    exact hnp _ _ (hf0 i) (hfwd i j hij.le) (lt_of_le_of_ne hle hne)
  have hback : lts.CanReach (f (i + 1)) (f i) := by
    refine canReach_trans (hfwd (i + 1) j hij) ?_
    rw [← heq]
    exact .refl lts _
  exact hstepN i hback

end WSTS

end Cslib
