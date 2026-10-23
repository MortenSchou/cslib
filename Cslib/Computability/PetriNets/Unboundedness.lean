/-
Copyright (c) 2026 Morten Schou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Morten Schou
-/

module

public import Cslib.Computability.PetriNets.Coverability
public import Cslib.Foundations.Semantics.LTS.Relation
public import Mathlib.Data.Finsupp.PWO

/-! # Characterisation of unbounded nets

A net with finitely many places and transitions is unbounded at `M₀` exactly when some marking
reachable from `M₀` can reach a strictly larger marking. The easy direction is
`not_bounded_of_pump`. For the converse, assume there is no such pair. Strongly connected
components of reachable markings are then finite, since an infinite one would contain a pair
`M₁ < M₂` by Dickson's lemma. Hence an unbounded net has an infinite chain of reachable markings
that leaves its strongly connected component at every step. Dickson's lemma applied to this chain
yields the contradiction.

## Main statements

- `PetriNet.exists_pump_of_not_bounded`: an unbounded net has a pumping pair.
- `PetriNet.bounded_iff_no_pump`: the characterisation.

## References

* [R. M. Karp, R. E. Miller, *Parallel Program Schemata*][KarpMiller1969]
* [T. Murata, *Petri nets: Properties, analysis and applications*][Murata1989]
-/

@[expose] public section

namespace Cslib

namespace PetriNet

variable {Place : Type*} {Transition : Type*} {N : PetriNet Place Transition}

/-- A single firing step is a reachability step. -/
theorem unlabelledTr_reachable {M M' : Marking Place} (h : N.lts.UnlabelledTr M M') :
    M ⇝[N] M' :=
  let ⟨_, h⟩ := h
  h.reachable

/-- A marking has finitely many successors when there are finitely many transitions. -/
theorem step_finite [Finite Transition] (M : Marking Place) :
    {M' | N.lts.UnlabelledTr M M'}.Finite := by
  refine (Set.finite_range fun t => N.fire M t).subset ?_
  rintro M' ⟨t, ht⟩
  exact ⟨t, (fires_iff.1 ht).2.symm⟩

/-- Without a pumping pair, the markings mutually reachable with a reachable marking `M` are
finite: otherwise Dickson's lemma would yield two comparable ones. -/
theorem scc_finite [Finite Place] {M₀ M : Marking Place}
    (hnp : ∀ M₁ M₂, M₀ ⇝[N] M₁ → M₁ ⇝[N] M₂ → ¬ M₁ < M₂)
    (hM : M₀ ⇝[N] M) : {M' | M ⇝[N] M' ∧ M' ⇝[N] M}.Finite := by
  by_contra hinf
  let f := Set.Infinite.natEmbedding _ hinf
  obtain ⟨i, j, hij, hle⟩ := wellQuasiOrdered_le fun n => (f n).1
  have hne : (f i).1 ≠ (f j).1 := fun h => hij.ne (f.injective (Subtype.ext h))
  refine hnp (f i).1 (f j).1 (hM.trans (f i).2.1) ((f i).2.2.trans (f j).2.1) ?_
  exact lt_of_le_of_ne hle hne

/-- Without a pumping pair, a reachable marking with infinitely many successors can reach another
marking with infinitely many successors that cannot reach it back. -/
theorem exists_next [Finite Place] [Finite Transition] {M₀ M : Marking Place}
    (hnp : ∀ M₁ M₂, M₀ ⇝[N] M₁ → M₁ ⇝[N] M₂ → ¬ M₁ < M₂)
    (hM : M₀ ⇝[N] M) (hinf : {z | M ⇝[N] z}.Infinite) :
    ∃ y, M ⇝[N] y ∧ ¬ y ⇝[N] M ∧ {z | y ⇝[N] z}.Infinite := by
  by_contra hcon
  push Not at hcon
  have hscc := scc_finite hnp hM
  have hsub : {z | M ⇝[N] z} ⊆ {M' | M ⇝[N] M' ∧ M' ⇝[N] M} ∪
      ⋃ M' ∈ {M' | M ⇝[N] M' ∧ M' ⇝[N] M},
        ⋃ y ∈ {y | N.lts.UnlabelledTr M' y ∧ ¬ y ⇝[N] M}, {z | y ⇝[N] z} := by
    intro z hz
    have key : ∀ z, Relation.ReflTransGen N.lts.UnlabelledTr M z →
        (M ⇝[N] z ∧ z ⇝[N] M) ∨
        ∃ M', (M ⇝[N] M' ∧ M' ⇝[N] M) ∧ ∃ y, N.lts.UnlabelledTr M' y ∧
          ¬ y ⇝[N] M ∧ y ⇝[N] z := by
      intro z hz
      induction hz with
      | refl => exact Or.inl ⟨.refl _ _, .refl _ _⟩
      | tail hz hstep ih =>
        rename_i z' w
        rcases ih with hs | ⟨M', hM', y, hy, hn, hyz⟩
        · by_cases hw : w ⇝[N] M
          · exact Or.inl ⟨hs.1.trans (unlabelledTr_reachable hstep), hw⟩
          · exact Or.inr ⟨z', hs, w, hstep, hw, .refl _ _⟩
        · exact Or.inr ⟨M', hM', y, hy, hn, hyz.trans (unlabelledTr_reachable hstep)⟩
    rcases key z ((LTS.reflTransGen_unlabelledTr_iff N.lts).2 hz) with
        hs | ⟨M', hM', y, hy, hn, hyz⟩
    · exact Or.inl hs
    · exact Or.inr (Set.mem_biUnion hM' (Set.mem_biUnion ⟨hy, hn⟩ hyz))
  refine hinf (((hscc.union (hscc.biUnion fun M' hM' => ?_))).subset hsub)
  refine ((step_finite M').subset fun y (hy : y ∈ {y | N.lts.UnlabelledTr M' y ∧ ¬ y ⇝[N] M}) =>
    hy.1).biUnion fun y hy => ?_
  exact hcon y (hM'.1.trans (unlabelledTr_reachable hy.1)) hy.2

/-- An unbounded net over finitely many places and transitions has a pumping pair. -/
theorem exists_pump_of_not_bounded [Finite Place] [Finite Transition] {M₀ : Marking Place}
    (h : ¬ N.Bounded M₀) :
    ∃ M₁ M₂, M₀ ⇝[N] M₁ ∧ M₁ ⇝[N] M₂ ∧ M₁ < M₂ := by
  by_contra hex
  have hnp : ∀ M₁ M₂, M₀ ⇝[N] M₁ → M₁ ⇝[N] M₂ → ¬ M₁ < M₂ :=
    fun M₁ M₂ h1 h2 hlt => hex ⟨M₁, M₂, h1, h2, hlt⟩
  have hR : {M | M₀ ⇝[N] M}.Infinite := fun hfin => h (bounded_of_finite_reachable hfin)
  let S : Set (Marking Place) := {M | M₀ ⇝[N] M ∧ {z | M ⇝[N] z}.Infinite}
  have hS : ∀ M ∈ S, ∃ y ∈ S, M ⇝[N] y ∧ ¬ y ⇝[N] M := by
    rintro M ⟨hM, hinf⟩
    obtain ⟨y, hy, hn, hyinf⟩ := exists_next hnp hM hinf
    exact ⟨y, ⟨hM.trans hy, hyinf⟩, hy, hn⟩
  choose! next hnextS hnextR hnextN using hS
  let g : ℕ → S := fun n =>
    Nat.rec ⟨M₀, .refl _ _, hR⟩
      (fun _ x => ⟨next x.1, hnextS x.1 x.2⟩) n
  let f : ℕ → Marking Place := fun n => (g n).1
  have hf0 : ∀ n, M₀ ⇝[N] f n := fun n => (g n).2.1
  have hstep : ∀ n, f n ⇝[N] f (n + 1) := fun n => hnextR _ (g n).2
  have hstepN : ∀ n, ¬ f (n + 1) ⇝[N] f n := fun n => hnextN _ (g n).2
  have hfwd : ∀ i j, i ≤ j → f i ⇝[N] f j := by
    intro i j hij
    induction j, hij using Nat.le_induction with
    | base => exact .refl _ _
    | succ j _ ih => exact ih.trans (hstep j)
  obtain ⟨i, j, hij, hle⟩ := wellQuasiOrdered_le f
  have heq : f i = f j := by
    by_contra hne
    exact hnp _ _ (hf0 i) (hfwd i j hij.le) (lt_of_le_of_ne hle hne)
  have hback : f (i + 1) ⇝[N] f i := by
    refine (hfwd (i + 1) j hij).trans ?_
    rw [← heq]
    exact .refl _ _
  exact hstepN i hback

/-- A net over finitely many places and transitions is bounded exactly when no reachable marking
can reach a strictly larger one. -/
theorem bounded_iff_no_pump [Finite Place] [Finite Transition] {M₀ : Marking Place} :
    N.Bounded M₀ ↔ ¬ ∃ M₁ M₂, M₀ ⇝[N] M₁ ∧ M₁ ⇝[N] M₂ ∧ M₁ < M₂ :=
  ⟨fun hb ⟨_, _, h1, h2, hlt⟩ => not_bounded_of_pump h1 h2 hlt hb,
    fun hno => by_contra fun hb => hno (exists_pump_of_not_bounded hb)⟩

end PetriNet

end Cslib
