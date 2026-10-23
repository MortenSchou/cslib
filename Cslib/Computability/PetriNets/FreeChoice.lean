/-
Copyright (c) 2026 Morten Schou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Morten Schou
-/

module

public import Cslib.Computability.PetriNets.PlaceInvariants
public import Cslib.Foundations.Data.Set.Ranking
public import Cslib.Computability.PetriNets.Structure
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Ring.GeomSum
public import Mathlib.Data.Set.Card
public import Mathlib.Order.WellFounded
public import Mathlib.Data.Set.Finite.Basic

/-! # Free-choice nets and Commoner's theorem

A net is *free-choice* if transitions sharing an input place have the same preset: whenever a place
is a choice between transitions, it is a choice for all of them at once. For ordinary free-choice
nets, liveness is characterised by siphons and traps (Commoner, Hack).

**Sufficiency.** If every nonempty siphon contains a trap that is marked initially, then the net is
live. The argument looks at a reachable marking `M` at which the set of dead transitions is
maximal. If a transition `u` is dead at `M`, then by the free-choice property no live transition can
remove tokens from its input places, so the tokens of these places persist, and `u` can only be dead
if some input place of `u` stays empty forever. The places that stay empty forever form a siphon
that is unmarked at `M`, which cannot contain a marked trap.

**Necessity.** Let `S` be a siphon and `Q` the largest trap in `S`, and suppose `Q` is unmarked at
`M₀`. The places `Z = S \ Q` can be ranked so that every place `z` of `Z` has a transition `e z`
that consumes from `z` and puts tokens into `S` only on places of `Z` of smaller rank, and none
into `Q`. The weight `∑ 2 ^ rank · tokens` over `Z` then drops whenever such a transition fires.
By liveness, from any reachable marking some `e z` can be enabled. Look at the first transition of
the path that consumes from `S`: it consumes from a marked place `s` of `Z`, and by free-choice
`e s` has the same preset, so it is enabled there as well. Firing it lowers the weight. So the
weight can be driven to zero, which empties `S` while `Q` stays unmarked. But a live net keeps its
siphons marked (`PetriNet.Live.marked_siphon`).

## Main definitions

- `PetriNet.IsFreeChoice`: transitions sharing an input place have equal presets.
- `PetriNet.DeadAt`: a transition can never be enabled again from a marking.
- `PetriNet.IsExitRanking`: a ranking of the places outside the largest trap of a siphon, with an
  exit transition for each.

## Main statements

- `PetriNet.live_of_siphons_contain_marked_trap`: for ordinary free-choice nets with finitely many
  transitions, if every nonempty siphon contains a marked trap, then the net is live.
- `PetriNet.siphonTrap_of_live`: conversely, a live ordinary free-choice net over finitely many
  places, in which every place has an output transition, has a marked trap in every nonempty siphon.
- `PetriNet.live_iff_siphonTrap`: Commoner's theorem.

## References

* [T. Murata, *Petri nets: Properties, analysis and applications*][Murata1989]
-/

@[expose] public section

namespace Cslib

namespace PetriNet

variable {Place : Type*} {Transition : Type*} {N : PetriNet Place Transition}

/-- A net is free-choice if two transitions that share an input place have the same preset. -/
def IsFreeChoice (N : PetriNet Place Transition) : Prop :=
  ∀ t t' p, 0 < N.pre t p → 0 < N.pre t' p → •[N] t = •[N] t'

/-- A transition is dead at `M` if it is not enabled at any marking reachable from `M`. -/
def DeadAt (N : PetriNet Place Transition) (M : Marking Place) (t : Transition) : Prop :=
  ∀ M', M ⇝[N] M' → ¬ M' [t⟩[N]

theorem DeadAt.mono {M M' : Marking Place} {t : Transition} (h : N.DeadAt M t)
    (hr : M ⇝[N] M') : N.DeadAt M' t :=
  fun _ h' => h _ (hr.trans h')

/-- A transition that is not live at `M₀` is dead at some marking reachable from `M₀`. -/
theorem exists_deadAt_of_not_liveAt {M₀ : Marking Place} {t : Transition}
    (h : ¬ N.LiveAt M₀ t) : ∃ M, M₀ ⇝[N] M ∧ N.DeadAt M t := by
  simp only [LiveAt, not_forall, not_exists, not_and] at h
  obtain ⟨M, hM, h⟩ := h
  exact ⟨M, hM, fun M' hr he => h M' hr he⟩

/-- In a free-choice net, a place that is an input of a dead transition keeps its tokens: the only
transitions that could remove them have the same preset, hence are dead too. -/
theorem DeadAt.persist (hfc : N.IsFreeChoice) {M : Marking Place} {u : Transition}
    (hu : N.DeadAt M u) {p : Place} (hp : 0 < N.pre u p) {M₁ M₂ : Marking Place}
    (h₁ : M ⇝[N] M₁) (hmark : 0 < M₁ p) (h₂ : M₁ ⇝[N] M₂) : 0 < M₂ p := by
  have key := h₂.invariant (P := fun K => M ⇝[N] K ∧ 0 < K p)
    (fun {K t K'} hf ⟨hK, hKp⟩ => ?_) ⟨h₁, hmark⟩
  · exact key.2
  · refine ⟨hK.trans hf.reachable, ?_⟩
    obtain ⟨R, rfl, rfl⟩ := hf
    by_cases hc : 0 < N.pre t p
    · exfalso
      have heq := hfc t u p hc hp
      exact hu _ hK (by rw [Enabled, ← heq]; exact le_self_add)
    · have : N.pre t p = 0 := by omega
      simp only [Finsupp.add_apply] at hKp ⊢
      omega

/-- If a place is empty at `M` but marked at a marking reachable from `M`, then some transition
that is enabled at a marking reachable from `M` produces into it. -/
theorem exists_producer {M M' : Marking Place} {q : Place} (hr : M ⇝[N] M')
    (h0 : M q = 0) (hpos : 0 < M' q) :
    ∃ K v K', M ⇝[N] K ∧ K [v⟩[N] K' ∧ 0 < N.post v q := by
  by_contra hno
  push Not at hno
  have key := hr.invariant (P := fun K => M ⇝[N] K ∧ K q = 0)
    (fun {K v K'} hf ⟨hK, hKq⟩ => ?_) ⟨.refl _ _, h0⟩
  · omega
  · refine ⟨hK.trans hf.reachable, ?_⟩
    have := hno K v K' hK hf
    obtain ⟨R, rfl, rfl⟩ := hf
    simp only [Finsupp.add_apply] at hKq ⊢
    omega

/-- At a marking where no further transition becomes dead, a dead transition has an input place
that stays empty forever. -/
theorem DeadAt.exists_unmarked_input (hord : N.Ordinary) (hfc : N.IsFreeChoice)
    {M : Marking Place} (hmax : ∀ M', M ⇝[N] M' → ∀ t, N.DeadAt M' t → N.DeadAt M t)
    {u : Transition} (hu : N.DeadAt M u) :
    ∃ p, 0 < N.pre u p ∧ ∀ M', M ⇝[N] M' → M' p = 0 := by
  classical
  by_contra hcon
  push Not at hcon
  -- every input place of `u` can be marked from `M`; marking them one by one keeps the others
  have hall : ∀ F : Finset Place, ∃ M₁, M ⇝[N] M₁ ∧ ∀ p ∈ F, 0 < N.pre u p → 0 < M₁ p := by
    intro F
    induction F using Finset.induction_on with
    | empty => exact ⟨M, .refl _ _, by simp⟩
    | insert q F hq ih =>
      obtain ⟨M₁, hM₁, hF⟩ := ih
      by_cases hqu : 0 < N.pre u q
      · obtain ⟨M_q, hMq, hpos⟩ := hcon q hqu
        by_cases h0 : M q = 0
        · obtain ⟨K, v, K', hK, hf, hv⟩ := exists_producer hMq h0 (Nat.pos_of_ne_zero hpos)
          have hvlive : ¬ N.DeadAt M₁ v := fun hd =>
            hmax M₁ hM₁ v hd K hK (enabled_iff_exists_fires.2 ⟨K', hf⟩)
          simp only [DeadAt, not_forall, not_not] at hvlive
          obtain ⟨M₂, hM₂, hen⟩ := hvlive
          obtain ⟨M₃, hf₃⟩ := enabled_iff_exists_fires.1 hen
          refine ⟨M₃, hM₁.trans (hM₂.trans hf₃.reachable), ?_⟩
          intro p hp hpu
          rcases Finset.mem_insert.1 hp with rfl | hp
          · obtain ⟨R, rfl, rfl⟩ := hf₃
            simp only [Finsupp.add_apply]
            omega
          · exact hu.mono hM₁ |>.persist hfc hpu (.refl _ _) (hF p hp hpu)
              (hM₂.trans hf₃.reachable)
        · refine ⟨M₁, hM₁, fun p hp hpu => ?_⟩
          rcases Finset.mem_insert.1 hp with rfl | hp
          · exact hu.persist hfc hqu (M₁ := M) (.refl _ _) (by omega) hM₁
          · exact hF p hp hpu
      · exact ⟨M₁, hM₁, fun p hp hpu => by
          rcases Finset.mem_insert.1 hp with rfl | hp
          · exact absurd hpu hqu
          · exact hF p hp hpu⟩
  obtain ⟨M₁, hM₁, hF⟩ := hall (•[N] u).support
  refine hu M₁ hM₁ ?_
  intro p
  by_cases hp : 0 < N.pre u p
  · have := hF p (Finsupp.mem_support_iff.2 (by omega)) hp
    have := (hord u p).1
    omega
  · omega

/-- **Commoner's criterion**: in an ordinary free-choice net with finitely many transitions, if
every nonempty siphon contains a trap that is marked at `M₀`, then the net is live at `M₀`. -/
theorem live_of_siphons_contain_marked_trap [Finite Transition] (hord : N.Ordinary)
    (hfc : N.IsFreeChoice) {M₀ : Marking Place} (hst : N.SiphonTrap M₀) : N.Live M₀ := by
  by_contra hnl
  simp only [Live, not_forall] at hnl
  obtain ⟨t, ht⟩ := hnl
  obtain ⟨M₁, hM₁, hd⟩ := exists_deadAt_of_not_liveAt ht
  -- choose a marking after `M₁` at which the set of dead transitions is maximal
  let D : Marking Place → Set Transition := fun M => {u | N.DeadAt M u}
  obtain ⟨_, ⟨M, hM, rfl⟩, hmaxD⟩ := wellFounded_gt.has_min (D '' {M | M₁ ⇝[N] M})
    ⟨D M₁, M₁, .refl _ _, rfl⟩
  have hmax : ∀ M', M ⇝[N] M' → ∀ u, N.DeadAt M' u → N.DeadAt M u := by
    intro M' hr u hu
    have hsub : D M ⊆ D M' := fun v hv => hv.mono hr
    have : D M' = D M := by
      by_contra hne
      exact hmaxD (D M') ⟨M', hM.trans hr, rfl⟩ (lt_of_le_of_ne hsub (Ne.symm hne))
    have hu' : u ∈ D M' := hu
    rw [this] at hu'
    exact hu'
  have hdM : N.DeadAt M t := hd.mono hM
  -- the places that stay empty forever form an unmarked siphon
  let S : Set Place := {p | ∀ M', M ⇝[N] M' → M' p = 0}
  obtain ⟨p₀, hp₀, hS₀⟩ := hdM.exists_unmarked_input hord hfc hmax
  have hsiphon : N.IsSiphon S := by
    intro v ⟨q, hq, hpost⟩
    have hv : N.DeadAt M v := fun M' hr hen => by
      obtain ⟨M'', hf⟩ := enabled_iff_exists_fires.1 hen
      have := hq M'' (hr.trans hf.reachable)
      obtain ⟨R, rfl, rfl⟩ := hf
      simp only [Finsupp.add_apply] at this
      omega
    obtain ⟨p, hp, hS⟩ := hv.exists_unmarked_input hord hfc hmax
    exact ⟨p, hS, hp⟩
  obtain ⟨T, hTS, hT, hmark⟩ := hst S hsiphon ⟨p₀, hS₀⟩
  obtain ⟨p, hp, hpos⟩ := hT.marked_of_reachable (hM₁.trans hM) hmark
  have := hTS hp M (.refl _ _)
  omega

/-- A ranking of the places `Z` with an exit transition `e z` for each of them: `e z` consumes from
`z` and produces, within `Z`, only on places of smaller rank, and nothing in `Q`. -/
structure IsExitRanking (N : PetriNet Place Transition) (Z Q : Set Place) (f : Place → ℕ)
    (e : Place → Transition) : Prop where
  /-- Distinct places have distinct ranks. -/
  injOn : Set.InjOn f Z
  /-- The exit of `z` consumes from `z`. -/
  pre_pos : ∀ z ∈ Z, 0 < N.pre (e z) z
  /-- The exit of `z` produces nothing in `Q`, and only on places of smaller rank in `Z`. -/
  post : ∀ z ∈ Z, ∀ s, 0 < N.post (e z) s → s ∉ Q ∧ (s ∈ Z → f s < f z)

open Classical in
/-- The weight of a place of `Z`: two to the power of its rank. -/
noncomputable def rankWeight (Z : Set Place) (f : Place → ℕ) (p : Place) : ℕ :=
  if p ∈ Z then 2 ^ f p else 0

/-- An exit transition produces strictly less weight than it consumes, in an ordinary net. -/
theorem IsExitRanking.weight_lt (hord : N.Ordinary) {Z Q : Set Place} {f : Place → ℕ}
    {e : Place → Transition} (hR : IsExitRanking N Z Q f e) {z : Place} (hz : z ∈ Z) :
    Marking.weight (rankWeight Z f) (N.post (e z)) <
      Marking.weight (rankWeight Z f) (N.pre (e z)) := by
  classical
  have hge : 2 ^ f z ≤ Marking.weight (rankWeight Z f) (N.pre (e z)) := by
    have := Marking.mul_le_weight (rankWeight Z f) (N.pre (e z)) z
    have hpos := hR.pre_pos z hz
    simp only [rankWeight, hz, ite_true] at this
    calc 2 ^ f z = 2 ^ f z * 1 := (mul_one _).symm
      _ ≤ 2 ^ f z * N.pre (e z) z := Nat.mul_le_mul_left _ hpos
      _ ≤ _ := this
  refine lt_of_lt_of_le ?_ hge
  rw [Marking.weight_apply, Finsupp.sum]
  calc ∑ p ∈ (N.post (e z)).support, rankWeight Z f p * N.post (e z) p
      ≤ ∑ p ∈ (N.post (e z)).support, if p ∈ Z then 2 ^ f p else 0 := by
        refine Finset.sum_le_sum fun p _ => ?_
        by_cases hp : p ∈ Z
        · simp only [rankWeight, hp, ite_true]
          simpa using Nat.mul_le_mul_left (2 ^ f p) ((hord (e z) p).2)
        · simp [rankWeight, hp]
    _ = ∑ p ∈ (N.post (e z)).support.filter (· ∈ Z), 2 ^ f p := by
        rw [Finset.sum_filter]
    _ = ∑ i ∈ ((N.post (e z)).support.filter (· ∈ Z)).image f, 2 ^ i := by
        rw [Finset.sum_image]
        intro a ha b hb hab
        exact hR.injOn (Finset.mem_filter.1 ha).2 (Finset.mem_filter.1 hb).2 hab
    _ < 2 ^ f z := by
        refine Nat.geomSum_lt le_rfl fun i hi => ?_
        obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hi
        obtain ⟨hpsupp, hpZ⟩ := Finset.mem_filter.1 hp
        exact (hR.post z hz p (Finsupp.mem_support_iff.1 hpsupp |> Nat.pos_of_ne_zero)).2 hpZ

section Descent

variable {S Z Q : Set Place} {f : Place → ℕ} {e : Place → Transition}

/-- Firing an exit transition of a place of `Z` lowers the weight. -/
theorem IsExitRanking.fires_lt (hord : N.Ordinary) (hR : IsExitRanking N Z Q f e) {z : Place}
    (hz : z ∈ Z) {K K' : Marking Place} (hf : N.Fires K (e z) K') :
    Marking.weight (rankWeight Z f) K' < Marking.weight (rankWeight Z f) K := by
  obtain ⟨R, rfl, rfl⟩ := hf
  simp only [map_add]
  have := hR.weight_lt hord hz
  omega

/-- Firing an exit transition keeps `Q` unmarked. -/
theorem IsExitRanking.fires_unmarked (hR : IsExitRanking N Z Q f e) {z : Place} (hz : z ∈ Z)
    {K K' : Marking Place} (hf : N.Fires K (e z) K') (hQ : ∀ q ∈ Q, K q = 0) :
    ∀ q ∈ Q, K' q = 0 := by
  obtain ⟨R, rfl, rfl⟩ := hf
  intro q hq
  have hpost : N.post (e z) q = 0 := by
    by_contra hne
    exact (hR.post z hz q (Nat.pos_of_ne_zero hne)).1 hq
  have := hQ q hq
  simp only [Finsupp.add_apply] at this ⊢
  omega

/-- From a marking at which `Q` is unmarked, if an exit transition of a place of `Z` can be enabled
by a firing sequence, then some reachable marking has lower weight and `Q` still unmarked. -/
theorem exists_lower (hord : N.Ordinary) (hfc : N.IsFreeChoice) (hS : N.IsSiphon S)
    (hZS : Z ⊆ S) (hSZ : S ⊆ Z ∪ Q) (hQS : Q ⊆ S) (hR : IsExitRanking N Z Q f e) {z₀ : Place}
    (hz₀ : z₀ ∈ Z) {K K₁ : Marking Place} {ts : List Transition} (h : N.lts.MTr K ts K₁)
    (hen : N.Enabled K₁ (e z₀)) (hQ : ∀ q ∈ Q, K q = 0) :
    ∃ K', N.Reachable K K' ∧ (∀ q ∈ Q, K' q = 0) ∧
      Marking.weight (rankWeight Z f) K' < Marking.weight (rankWeight Z f) K := by
  revert hen hQ
  induction h with
  | refl =>
    intro hen hQ
    obtain ⟨K', hf⟩ := enabled_iff_exists_fires.1 hen
    exact ⟨K', hf.reachable, hR.fires_unmarked hz₀ hf hQ, hR.fires_lt hord hz₀ hf⟩
  | @stepL K t K₂ ts' K₁' htr hrest ih =>
    intro hen hQ
    have htr' : N.Fires K t K₂ := htr
    by_cases hcons : ∃ s ∈ S, 0 < N.pre t s
    · obtain ⟨s, hsS, hpos⟩ := hcons
      have hen_t : N.Enabled K t := (fires_iff.1 htr').1
      have hKs : 0 < K s := lt_of_lt_of_le hpos (hen_t s)
      have hsZ : s ∈ Z := by
        rcases hSZ hsS with h | h
        · exact h
        · have := hQ s h
          omega
      have hpre : N.pre t = N.pre (e s) := hfc t (e s) s hpos (hR.pre_pos s hsZ)
      have hen' : N.Enabled K (e s) := by rw [Enabled, ← hpre]; exact hen_t
      obtain ⟨K', hf'⟩ := enabled_iff_exists_fires.1 hen'
      exact ⟨K', hf'.reachable, hR.fires_unmarked hsZ hf' hQ, hR.fires_lt hord hsZ hf'⟩
    · push Not at hcons
      have hpre0 : ∀ s ∈ S, N.pre t s = 0 := fun s hs => by
        have := hcons s hs
        omega
      have hpost0 : ∀ s ∈ S, N.post t s = 0 := by
        intro s hs
        by_contra hne
        obtain ⟨q, hq, hqpos⟩ := hS t ⟨s, hs, Nat.pos_of_ne_zero hne⟩
        have := hpre0 q hq
        omega
      obtain ⟨R, hK, hK₂⟩ := htr'
      have hQ₂ : ∀ q ∈ Q, K₂ q = 0 := by
        intro q hq
        have h1 := hQ q hq
        have h2 := hpre0 q (hQS hq)
        have h3 := hpost0 q (hQS hq)
        rw [hK] at h1
        rw [hK₂]
        simp only [Finsupp.add_apply] at h1 ⊢
        omega
      have hw0 : ∀ M : Marking Place, (∀ s ∈ S, M s = 0) →
          Marking.weight (rankWeight Z f) M = 0 := fun M hM =>
        weight_eq_zero_of fun p => by
          by_cases hp : p ∈ Z
          · exact Or.inr (hM p (hZS hp))
          · exact Or.inl (by simp [rankWeight, hp])
      have hw : Marking.weight (rankWeight Z f) K₂ = Marking.weight (rankWeight Z f) K := by
        rw [hK, hK₂, map_add, map_add, hw0 _ hpre0, hw0 _ hpost0]
        omega
      obtain ⟨K', hr, hQ', hlt⟩ := ih hen hQ₂
      exact ⟨K', (show N.Fires K t K₂ from ⟨R, hK, hK₂⟩).reachable.trans hr, hQ', hw ▸ hlt⟩

/-- In a live net, from a reachable marking with `Q` unmarked, the weight can be driven to zero. -/
theorem exists_zero_weight {M₀ : Marking Place} (hord : N.Ordinary) (hfc : N.IsFreeChoice)
    (hl : N.Live M₀) (hS : N.IsSiphon S) (hZS : Z ⊆ S) (hSZ : S ⊆ Z ∪ Q) (hQS : Q ⊆ S)
    (hR : IsExitRanking N Z Q f e) (n : ℕ) :
    ∀ K : Marking Place, N.Reachable M₀ K → (∀ q ∈ Q, K q = 0) →
      Marking.weight (rankWeight Z f) K = n →
      ∃ K', N.Reachable M₀ K' ∧ (∀ q ∈ Q, K' q = 0) ∧
        Marking.weight (rankWeight Z f) K' = 0 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro K hKr hQ hKn
    by_cases h0 : Marking.weight (rankWeight Z f) K = 0
    · exact ⟨K, hKr, hQ, h0⟩
    · obtain ⟨z₀, hz₀⟩ : Z.Nonempty := by
        by_contra hne
        rw [Set.not_nonempty_iff_eq_empty] at hne
        exact h0 (weight_eq_zero_of fun p => Or.inl (by simp [rankWeight, hne]))
      obtain ⟨K₁, ⟨ts, hts⟩, hen⟩ := hl (e z₀) K hKr
      obtain ⟨K', hr, hQ', hlt⟩ := exists_lower hord hfc hS hZS hSZ hQS hR hz₀ hts hen hQ
      exact ih _ (hKn ▸ hlt) K' (hKr.trans hr) hQ' rfl

end Descent

/-- **The converse of Commoner's criterion**: a live ordinary free-choice net over finitely many
places, in which every place has an output transition, has a marked trap in every nonempty
siphon. -/
theorem siphonTrap_of_live [Finite Place] {M₀ : Marking Place} (hord : N.Ordinary)
    (hfc : N.IsFreeChoice) (hl : N.Live M₀) (hout : ∀ p, ∃ t, 0 < N.pre t p) :
    N.SiphonTrap M₀ := by
  classical
  intro S hS hne
  by_contra hno
  push Not at hno
  obtain ⟨p₀, hp₀⟩ := hne
  have : Nonempty Transition := let ⟨t, _⟩ := hout p₀; ⟨t⟩
  have hQ0 : ∀ q ∈ N.maxTrap S, M₀ q = 0 := by
    intro q hq
    obtain ⟨T, hT, hTS, hqT⟩ := hq
    by_contra hne
    exact hno T hTS hT ⟨q, hqT, Nat.pos_of_ne_zero hne⟩
  obtain ⟨f, e, hinj, hprops⟩ := Cslib.exists_rank (S \ N.maxTrap S) (N.maxTrap S)
    (fun u p => 0 < N.pre u p) (fun u p => 0 < N.post u p) fun Y hY hYne => by
      obtain ⟨u, y, hy, hpre, hpost⟩ := exists_exit S hY hYne
      exact ⟨u, y, hy, hpre, hpost⟩
  have hR : IsExitRanking N (S \ N.maxTrap S) (N.maxTrap S) f e :=
    ⟨hinj, fun z hz => (hprops z hz).1, fun z hz => (hprops z hz).2⟩
  have hSZ : S ⊆ (S \ N.maxTrap S) ∪ N.maxTrap S := fun p hp => by
    by_cases h : p ∈ N.maxTrap S
    · exact Or.inr h
    · exact Or.inl ⟨hp, h⟩
  obtain ⟨K, hKr, hKQ, hK0⟩ := exists_zero_weight hord hfc hl hS Set.sdiff_subset hSZ
    (maxTrap_subset S) hR _ M₀ (Reachable.refl N M₀) hQ0 rfl
  have hKS : ¬ MarkedOn K S := by
    rintro ⟨p, hp, hpos⟩
    by_cases hpQ : p ∈ N.maxTrap S
    · have := hKQ p hpQ
      omega
    · have hpZ : p ∈ S \ N.maxTrap S := ⟨hp, hpQ⟩
      have := Marking.mul_le_weight (rankWeight (S \ N.maxTrap S) f) K p
      simp only [rankWeight, hpZ, ite_true, hK0] at this
      have h2 : 0 < 2 ^ f p := Nat.two_pow_pos _
      have := Nat.mul_pos h2 hpos
      omega
  exact hKS (hl.marked_siphon hout hS ⟨p₀, hp₀⟩ hKr)

/-- **Commoner's theorem**: an ordinary free-choice net over finitely many places and transitions,
in which every place has an output transition, is live exactly when every nonempty siphon contains
a trap that is marked initially. -/
theorem live_iff_siphonTrap [Finite Place] [Finite Transition] {M₀ : Marking Place}
    (hord : N.Ordinary) (hfc : N.IsFreeChoice) (hout : ∀ p, ∃ t, 0 < N.pre t p) :
    N.Live M₀ ↔ N.SiphonTrap M₀ :=
  ⟨fun hl => siphonTrap_of_live hord hfc hl hout,
    fun hst => live_of_siphons_contain_marked_trap hord hfc hst⟩

end PetriNet

end Cslib
