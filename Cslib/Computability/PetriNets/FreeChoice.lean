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
  ∀ t t' p, p ∈ •[N] t → p ∈ •[N] t' → •[N] t = •[N] t'

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
    (hu : N.DeadAt M u) {p : Place} (hp : p ∈ •[N] u) {M₁ M₂ : Marking Place}
    (h₁ : M ⇝[N] M₁) (hmark : p ∈ M₁) (h₂ : M₁ ⇝[N] M₂) : p ∈ M₂ := by
  have key := h₂.invariant (P := fun K => M ⇝[N] K ∧ p ∈ K)
    (fun {K t K'} hf ⟨hK, hKp⟩ => ?_) ⟨h₁, hmark⟩
  · exact key.2
  · refine ⟨hK.trans hf.reachable, ?_⟩
    obtain ⟨R, rfl, rfl⟩ := hf
    obtain hc | hR := Multiset.mem_add.1 hKp
    · exfalso
      have heq := hfc t u p hc hp
      exact hu _ hK (by rw [Enabled, ← heq]; exact le_self_add)
    · exact Multiset.mem_add.2 (.inl hR)

/-- If a place is empty at `M` but marked at a marking reachable from `M`, then some transition
that is enabled at a marking reachable from `M` produces into it. -/
theorem exists_producer {M M' : Marking Place} {q : Place} (hr : M ⇝[N] M')
    (h0 : q ∉ M) (hpos : q ∈ M') :
    ∃ K v K', M ⇝[N] K ∧ K [v⟩[N] K' ∧ q ∈ v •[N] := by
  by_contra hno
  push Not at hno
  have key := hr.invariant (P := fun K => M ⇝[N] K ∧ q ∉ K)
    (fun {K v K'} hf ⟨hK, hKq⟩ => ?_) ⟨.refl _ _, h0⟩
  · exact key.2 hpos
  · refine ⟨hK.trans hf.reachable, ?_⟩
    have hv := hno K v K' hK hf
    obtain ⟨R, rfl, rfl⟩ := hf
    exact fun hq => (Multiset.mem_add.1 hq).elim (fun hR => hKq (Multiset.mem_add.2 (.inr hR))) hv

/-- At a marking where no further transition becomes dead, a dead transition has an input place
that stays empty forever. -/
theorem DeadAt.exists_unmarked_input (hord : N.Ordinary) (hfc : N.IsFreeChoice)
    {M : Marking Place} (hmax : ∀ M', M ⇝[N] M' → ∀ t, N.DeadAt M' t → N.DeadAt M t)
    {u : Transition} (hu : N.DeadAt M u) :
    ∃ p ∈ •[N] u, ∀ M', M ⇝[N] M' → p ∉ M' := by
  by_contra hcon
  push Not at hcon
  -- every input place of `u` can be marked from `M`; marking them one by one keeps the others
  have hall : ∀ F : Multiset Place, ∃ M₁, M ⇝[N] M₁ ∧ ∀ p ∈ F, p ∈ •[N] u → p ∈ M₁ := by
    intro F
    induction F using Multiset.induction_on with
    | empty => exact ⟨M, .refl _ _, by simp⟩
    | cons q F ih =>
      obtain ⟨M₁, hM₁, hF⟩ := ih
      by_cases hqu : q ∈ •[N] u
      · obtain ⟨M_q, hMq, hpos⟩ := hcon q hqu
        by_cases h0 : q ∈ M
        · refine ⟨M₁, hM₁, fun p hp hpu => ?_⟩
          rcases Multiset.mem_cons.1 hp with rfl | hp
          · exact hu.persist hfc hqu (M₁ := M) (.refl _ _) h0 hM₁
          · exact hF p hp hpu
        · obtain ⟨K, v, K', hK, hf, hv⟩ := exists_producer hMq h0 hpos
          have hvlive : ¬ N.DeadAt M₁ v := fun hd =>
            hmax M₁ hM₁ v hd K hK (enabled_iff_exists_fires.2 ⟨K', hf⟩)
          simp only [DeadAt, not_forall, not_not] at hvlive
          obtain ⟨M₂, hM₂, hen⟩ := hvlive
          obtain ⟨M₃, hf₃⟩ := enabled_iff_exists_fires.1 hen
          refine ⟨M₃, hM₁.trans (hM₂.trans hf₃.reachable), fun p hp hpu => ?_⟩
          rcases Multiset.mem_cons.1 hp with rfl | hp
          · obtain ⟨R, rfl, rfl⟩ := hf₃
            exact Multiset.mem_add.2 (.inr hv)
          · exact hu.mono hM₁ |>.persist hfc hpu (.refl _ _) (hF p hp hpu)
              (hM₂.trans hf₃.reachable)
      · exact ⟨M₁, hM₁, fun p hp hpu => by
          rcases Multiset.mem_cons.1 hp with rfl | hp
          · exact absurd hpu hqu
          · exact hF p hp hpu⟩
  obtain ⟨M₁, hM₁, hF⟩ := hall (•[N] u)
  exact hu M₁ hM₁ ((Multiset.le_iff_subset (hord u).1).2 fun p hp => hF p hp hp)

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
  let S : Set Place := {p | ∀ M', M ⇝[N] M' → p ∉ M'}
  obtain ⟨p₀, hp₀, hS₀⟩ := hdM.exists_unmarked_input hord hfc hmax
  have hsiphon : N.IsSiphon S := by
    intro v ⟨q, hq, hpost⟩
    have hv : N.DeadAt M v := fun M' hr hen => by
      obtain ⟨M'', hf⟩ := enabled_iff_exists_fires.1 hen
      refine hq M'' (hr.trans hf.reachable) ?_
      obtain ⟨R, rfl, rfl⟩ := hf
      exact Multiset.mem_add.2 (.inr hpost)
    obtain ⟨p, hp, hS⟩ := hv.exists_unmarked_input hord hfc hmax
    exact ⟨p, hS, hp⟩
  obtain ⟨T, hTS, hT, hmark⟩ := hst S hsiphon ⟨p₀, hS₀⟩
  obtain ⟨p, hp, hpM⟩ := hT.marked_of_reachable (hM₁.trans hM) hmark
  exact hTS hp M (.refl _ _) hpM

/-- A ranking of the places `Z` with an exit transition `e z` for each of them: `e z` consumes from
`z` and produces, within `Z`, only on places of smaller rank, and nothing in `Q`. -/
structure IsExitRanking (N : PetriNet Place Transition) (Z Q : Set Place) (f : Place → ℕ)
    (e : Place → Transition) : Prop where
  /-- Distinct places have distinct ranks. -/
  injOn : Set.InjOn f Z
  /-- The exit of `z` consumes from `z`. -/
  mem_pre : ∀ z ∈ Z, z ∈ •[N] (e z)
  /-- The exit of `z` produces nothing in `Q`, and only on places of smaller rank in `Z`. -/
  post : ∀ z ∈ Z, ∀ s ∈ (e z) •[N], s ∉ Q ∧ (s ∈ Z → f s < f z)

/-- The weight of a place of `Z`: two to the power of its rank. -/
noncomputable def rankWeight (Z : Set Place) (f : Place → ℕ) : Place → ℕ :=
  Z.indicator (2 ^ f ·)

/-- An exit transition produces strictly less weight than it consumes, in an ordinary net. -/
theorem IsExitRanking.weight_lt (hord : N.Ordinary) {Z Q : Set Place} {f : Place → ℕ}
    {e : Place → Transition} (hR : IsExitRanking N Z Q f e) {z : Place} (hz : z ∈ Z) :
    Marking.weight (rankWeight Z f) (N.post (e z)) <
      Marking.weight (rankWeight Z f) (N.pre (e z)) := by
  classical
  have hge : 2 ^ f z ≤ Marking.weight (rankWeight Z f) (N.pre (e z)) := by
    simpa [rankWeight, hz] using Marking.le_weight_of_mem (rankWeight Z f) (hR.mem_pre z hz)
  refine lt_of_lt_of_le ?_ hge
  -- the postset has no duplicates, so its weight is a sum over a finite set
  let F : Finset Place := ⟨N.post (e z), (hord (e z)).2⟩
  calc Marking.weight (rankWeight Z f) (N.post (e z))
      = ∑ p ∈ F.filter (· ∈ Z), 2 ^ f p := by
        rw [Finset.sum_filter, Marking.weight_apply]
        rfl
    _ = ∑ i ∈ (F.filter (· ∈ Z)).image f, 2 ^ i := by
        rw [Finset.sum_image]
        intro a ha b hb hab
        exact hR.injOn (Finset.mem_filter.1 ha).2 (Finset.mem_filter.1 hb).2 hab
    _ < 2 ^ f z := by
        refine Nat.geomSum_lt le_rfl fun i hi => ?_
        obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hi
        obtain ⟨hpF, hpZ⟩ := Finset.mem_filter.1 hp
        exact (hR.post z hz p hpF).2 hpZ

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
    {K K' : Marking Place} (hf : N.Fires K (e z) K') (hQ : ∀ q ∈ Q, q ∉ K) :
    ∀ q ∈ Q, q ∉ K' := by
  obtain ⟨R, rfl, rfl⟩ := hf
  intro q hq hqK'
  obtain hqR | hqpost := Multiset.mem_add.1 hqK'
  · exact hQ q hq (Multiset.mem_add.2 (.inr hqR))
  · exact (hR.post z hz q hqpost).1 hq

/-- From a marking at which `Q` is unmarked, if an exit transition of a place of `Z` can be enabled
by a firing sequence, then some reachable marking has lower weight and `Q` still unmarked. -/
theorem exists_lower (hord : N.Ordinary) (hfc : N.IsFreeChoice) (hS : N.IsSiphon S)
    (hZS : Z ⊆ S) (hSZ : S ⊆ Z ∪ Q) (hQS : Q ⊆ S) (hR : IsExitRanking N Z Q f e) {z₀ : Place}
    (hz₀ : z₀ ∈ Z) {K K₁ : Marking Place} {ts : List Transition} (h : N.lts.MTr K ts K₁)
    (hen : N.Enabled K₁ (e z₀)) (hQ : ∀ q ∈ Q, q ∉ K) :
    ∃ K', N.Reachable K K' ∧ (∀ q ∈ Q, q ∉ K') ∧
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
    by_cases hcons : ∃ s ∈ S, s ∈ •[N] t
    · obtain ⟨s, hsS, hst⟩ := hcons
      have hen_t : N.Enabled K t := (enabled_iff_exists_fires.2 ⟨K₂, htr'⟩)
      have hsZ : s ∈ Z := by
        rcases hSZ hsS with h | h
        · exact h
        · exact absurd (Multiset.mem_of_le hen_t hst) (hQ s h)
      have hpre : •[N] t = •[N] (e s) := hfc t (e s) s hst (hR.mem_pre s hsZ)
      have hen' : N.Enabled K (e s) := by rw [Enabled, ← hpre]; exact hen_t
      obtain ⟨K', hf'⟩ := enabled_iff_exists_fires.1 hen'
      exact ⟨K', hf'.reachable, hR.fires_unmarked hsZ hf' hQ, hR.fires_lt hord hsZ hf'⟩
    · push Not at hcons
      have hpost : ∀ s ∈ S, s ∉ t •[N] := fun s hs hpost =>
        let ⟨q, hq, hqpre⟩ := hS t ⟨s, hs, hpost⟩
        hcons q hq hqpre
      obtain ⟨R, hK, hK₂⟩ := htr'
      have hQ₂ : ∀ q ∈ Q, q ∉ K₂ := by
        intro q hq hqK₂
        rw [hK₂] at hqK₂
        obtain hqR | hqpost := Multiset.mem_add.1 hqK₂
        · exact hQ q hq (hK ▸ Multiset.mem_add.2 (.inr hqR))
        · exact hpost q (hQS hq) hqpost
      have hw0 : ∀ M : Marking Place, (∀ s ∈ S, s ∉ M) →
          Marking.weight (rankWeight Z f) M = 0 := fun M hM =>
        weight_eq_zero_of fun p hp => Set.indicator_of_notMem (fun hpZ => hM p (hZS hpZ) hp) _
      have hw : Marking.weight (rankWeight Z f) K₂ = Marking.weight (rankWeight Z f) K := by
        rw [hK, hK₂, map_add, map_add, hw0 _ hcons, hw0 _ hpost]
        omega
      obtain ⟨K', hr, hQ', hlt⟩ := ih hen hQ₂
      exact ⟨K', (show N.Fires K t K₂ from ⟨R, hK, hK₂⟩).reachable.trans hr, hQ', hw ▸ hlt⟩

/-- In a live net, from a reachable marking with `Q` unmarked, the weight can be driven to zero. -/
theorem exists_zero_weight {M₀ : Marking Place} (hord : N.Ordinary) (hfc : N.IsFreeChoice)
    (hl : N.Live M₀) (hS : N.IsSiphon S) (hZS : Z ⊆ S) (hSZ : S ⊆ Z ∪ Q) (hQS : Q ⊆ S)
    (hR : IsExitRanking N Z Q f e) (n : ℕ) :
    ∀ K : Marking Place, N.Reachable M₀ K → (∀ q ∈ Q, q ∉ K) →
      Marking.weight (rankWeight Z f) K = n →
      ∃ K', N.Reachable M₀ K' ∧ (∀ q ∈ Q, q ∉ K') ∧
        Marking.weight (rankWeight Z f) K' = 0 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro K hKr hQ hKn
    by_cases h0 : Marking.weight (rankWeight Z f) K = 0
    · exact ⟨K, hKr, hQ, h0⟩
    · obtain ⟨z₀, hz₀⟩ : Z.Nonempty := by
        by_contra hne
        rw [Set.not_nonempty_iff_eq_empty] at hne
        exact h0 (weight_eq_zero_of fun p _ => by simp [rankWeight, hne])
      obtain ⟨K₁, ⟨ts, hts⟩, hen⟩ := hl (e z₀) K hKr
      obtain ⟨K', hr, hQ', hlt⟩ := exists_lower hord hfc hS hZS hSZ hQS hR hz₀ hts hen hQ
      exact ih _ (hKn ▸ hlt) K' (hKr.trans hr) hQ' rfl

end Descent

/-- **The converse of Commoner's criterion**: a live ordinary free-choice net over finitely many
places, in which every place has an output transition, has a marked trap in every nonempty
siphon. -/
theorem siphonTrap_of_live [Finite Place] {M₀ : Marking Place} (hord : N.Ordinary)
    (hfc : N.IsFreeChoice) (hl : N.Live M₀) (hout : ∀ p, ∃ t, p ∈ •[N] t) :
    N.SiphonTrap M₀ := by
  intro S hS hne
  by_contra hno
  push Not at hno
  obtain ⟨p₀, hp₀⟩ := hne
  have : Nonempty Transition := let ⟨t, _⟩ := hout p₀; ⟨t⟩
  have hQ0 : ∀ q ∈ N.maxTrap S, q ∉ M₀ := fun q ⟨T, hT, hTS, hqT⟩ hqM₀ =>
    hno T hTS hT ⟨q, hqT, hqM₀⟩
  obtain ⟨f, e, hinj, hprops⟩ := Cslib.exists_rank (S \ N.maxTrap S) (N.maxTrap S)
    (fun u p => p ∈ •[N] u) (fun u p => p ∈ u •[N]) fun _ hY hYne => exists_exit S hY hYne
  have hR : IsExitRanking N (S \ N.maxTrap S) (N.maxTrap S) f e :=
    ⟨hinj, fun z hz => (hprops z hz).1, fun z hz => (hprops z hz).2⟩
  have hSZ : S ⊆ (S \ N.maxTrap S) ∪ N.maxTrap S := fun p hp => by
    by_cases h : p ∈ N.maxTrap S
    · exact Or.inr h
    · exact Or.inl ⟨hp, h⟩
  obtain ⟨K, hKr, hKQ, hK0⟩ := exists_zero_weight hord hfc hl hS Set.sdiff_subset hSZ
    (maxTrap_subset S) hR _ M₀ (Reachable.refl N M₀) hQ0 rfl
  have hKS : ¬ MarkedOn K S := by
    rintro ⟨p, hp, hpK⟩
    by_cases hpQ : p ∈ N.maxTrap S
    · exact hKQ p hpQ hpK
    · have hpZ : p ∈ S \ N.maxTrap S := ⟨hp, hpQ⟩
      have := Marking.le_weight_of_mem (rankWeight (S \ N.maxTrap S) f) hpK
      rw [hK0, rankWeight, Set.indicator_of_mem hpZ] at this
      exact (Nat.two_pow_pos _).ne' (Nat.le_zero.1 this)
  exact hKS (hl.marked_siphon hout hS ⟨p₀, hp₀⟩ hKr)

/-- **Commoner's theorem**: an ordinary free-choice net over finitely many places and transitions,
in which every place has an output transition, is live exactly when every nonempty siphon contains
a trap that is marked initially. -/
theorem live_iff_siphonTrap [Finite Place] [Finite Transition] {M₀ : Marking Place}
    (hord : N.Ordinary) (hfc : N.IsFreeChoice) (hout : ∀ p, ∃ t, p ∈ •[N] t) :
    N.Live M₀ ↔ N.SiphonTrap M₀ :=
  ⟨fun hl => siphonTrap_of_live hord hfc hl hout,
    fun hst => live_of_siphons_contain_marked_trap hord hfc hst⟩

end PetriNet

end Cslib
