/-
Copyright (c) 2026 Morten Schou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Morten Schou
-/

module

public import Cslib.Computability.PetriNets.Basic
public import Cslib.Foundations.Semantics.LTS.Basic
public import Mathlib.Data.Set.Finite.Lattice
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Data.Multiset.Interval
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! # Labelled transition system semantics of Petri nets

The *marking graph* of a Petri net is an `LTS` whose states are markings and whose labels are
transitions. This gives Petri nets reachability, bisimilarity, trace equivalence, and so on for
free from the generic `LTS` API.

## Main definitions

- `PetriNet.lts`: the marking graph of a net.
- `PetriNet.Reachable`: reachability of a marking from another.
- `PetriNet.KBounded`: every reachable marking has at most `k` tokens in each place.
- `PetriNet.Bounded`: a net is `k`-bounded for some `k`.
- `PetriNet.Safe`: a net is `1`-bounded.
- `PetriNet.Bounded.finite_reachable`: bounded nets over finitely many places have finitely many
  reachable markings.
- `PetriNet.LiveAt`: a transition can always become enabled again from a marking.
- `PetriNet.Live`: a net is live at a marking if every transition is live at it.

## Main statements

- `PetriNet.mTr_add`: multistep firing sequences are preserved when adding tokens.
-/

@[expose] public section

namespace Cslib

namespace PetriNet

variable {Place : Type*} {Transition : Type*}

/-- The marking graph of a Petri net. -/
def lts (N : PetriNet Place Transition) : LTS (Marking Place) Transition where
  Tr := N.Fires

/-- A marking `M'` is reachable from `M` by some firing sequence. -/
abbrev Reachable (N : PetriNet Place Transition) (M M' : Marking Place) : Prop :=
  N.lts.CanReach M M'

/-- `M ⇝[N] M'` says that `M'` is reachable from `M` in the net `N`. -/
scoped syntax:50 term:51 " ⇝[" term "] " term:51 : term

scoped macro_rules
  | `($M ⇝[$N] $M') => `(PetriNet.Reachable $N $M $M')

/-- Pretty-printer for the notation. -/
@[scoped app_unexpander PetriNet.Reachable]
meta def unexpandReachable : Lean.PrettyPrinter.Unexpander
  | `($_ $N $M $M') => `($M ⇝[$N] $M')
  | _ => throw ()

@[refl, grind .]
theorem Reachable.refl (N : PetriNet Place Transition) (M : Marking Place) : M ⇝[N] M :=
  LTS.CanReach.refl N.lts M

@[grind <=]
theorem Reachable.trans {N : PetriNet Place Transition} {M₁ M₂ M₃ : Marking Place}
    (h₁ : M₁ ⇝[N] M₂) (h₂ : M₂ ⇝[N] M₃) : M₁ ⇝[N] M₃ :=
  let ⟨ts₁, h₁⟩ := h₁
  let ⟨ts₂, h₂⟩ := h₂
  ⟨ts₁ ++ ts₂, LTS.MTr.comp _ h₁ h₂⟩

/-- A single firing is a reachability step. -/
@[grind →]
theorem Fires.reachable {N : PetriNet Place Transition} {M M' : Marking Place} {t : Transition}
    (h : M [t⟩[N] M') : M ⇝[N] M' :=
  ⟨[t], .single _ h⟩

/-- Induction along reachability: a property preserved by every firing is preserved by
reachability. -/
theorem Reachable.invariant {N : PetriNet Place Transition} {P : Marking Place → Prop}
    (hP : ∀ {M t M'}, M [t⟩[N] M' → P M → P M') {M M' : Marking Place}
    (h : M ⇝[N] M') (hM : P M) : P M' := by
  obtain ⟨ts, h⟩ := h
  induction h with
  | refl => exact hM
  | stepL htr _ ih => exact ih (hP htr hM)

/-- A net is `k`-bounded at `M₀` if no reachable marking has more than `k` tokens in any place,
that is, contains `k + 1` copies of a place. It is stated without counting tokens, so that it does
not depend on decidable equality of places; `kBounded_iff` states it with `Multiset.count`. -/
def KBounded (N : PetriNet Place Transition) (M₀ : Marking Place) (k : ℕ) : Prop :=
  ∀ M, M₀ ⇝[N] M → ∀ p, ¬ Multiset.replicate (k + 1) p ≤ M

/-- A net is bounded at `M₀` if it is `k`-bounded at `M₀` for some `k`. -/
def Bounded (N : PetriNet Place Transition) (M₀ : Marking Place) : Prop :=
  ∃ k, N.KBounded M₀ k

/-- A net is safe at `M₀` if it is `1`-bounded at `M₀`. -/
def Safe (N : PetriNet Place Transition) (M₀ : Marking Place) : Prop :=
  N.KBounded M₀ 1

theorem kBounded_iff [DecidableEq Place] {N : PetriNet Place Transition} {M₀ : Marking Place}
    {k : ℕ} : N.KBounded M₀ k ↔ ∀ M, M₀ ⇝[N] M → ∀ p, M.count p ≤ k := by
  simp only [KBounded, ← Multiset.le_count_iff_replicate_le, not_le, Nat.lt_succ_iff]

/-- In a `k`-bounded net, every reachable marking has at most `k` tokens in each place. -/
theorem KBounded.count_le [DecidableEq Place] {N : PetriNet Place Transition}
    {M₀ M : Marking Place} {k : ℕ} (h : N.KBounded M₀ k) (hM : M₀ ⇝[N] M) (p : Place) :
    M.count p ≤ k :=
  kBounded_iff.1 h M hM p

/-- Over finitely many places, there are finitely many markings with at most `n` tokens. -/
theorem Marking.finite_card_le [Finite Place] (n : ℕ) :
    {M : Marking Place | M.card ≤ n}.Finite := by
  classical
  have := Fintype.ofFinite Place
  refine (Set.finite_Iic (n • (Finset.univ : Finset Place).val)).subset fun M hM => ?_
  simp only [Set.mem_Iic, Multiset.le_iff_count, Multiset.count_nsmul,
    Multiset.count_eq_one_of_mem Finset.univ.nodup (Finset.mem_univ _), mul_one]
  exact fun a => (Multiset.count_le_card a M).trans hM

section Bounded

theorem KBounded.mono {N : PetriNet Place Transition} {M₀ : Marking Place} {k l : ℕ}
    (h : N.KBounded M₀ k) (hkl : k ≤ l) : N.KBounded M₀ l :=
  fun M hM p hp => h M hM p ((Multiset.replicate_le_replicate _).2 (by omega) |>.trans hp)

theorem KBounded.bounded {N : PetriNet Place Transition} {M₀ : Marking Place} {k : ℕ}
    (h : N.KBounded M₀ k) : N.Bounded M₀ :=
  ⟨k, h⟩

theorem Safe.bounded {N : PetriNet Place Transition} {M₀ : Marking Place} (h : N.Safe M₀) :
    N.Bounded M₀ :=
  KBounded.bounded h

/-- With finitely many places, a `k`-bounded net has at most `|Place| * k` tokens in total. -/
theorem KBounded.card_le [Finite Place] {N : PetriNet Place Transition} {M₀ M : Marking Place}
    {k : ℕ} (h : N.KBounded M₀ k) (hM : M₀ ⇝[N] M) :
    M.card ≤ Nat.card Place * k := by
  classical
  have := Fintype.ofFinite Place
  rw [← Multiset.toFinset_sum_count_eq, Nat.card_eq_fintype_card]
  calc ∑ p ∈ M.toFinset, M.count p ≤ ∑ p, M.count p :=
        Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    _ ≤ ∑ _p : Place, k := Finset.sum_le_sum fun p _ => h.count_le hM p
    _ = Fintype.card Place * k := by simp

/-- A `k`-bounded net over finitely many places has finitely many reachable markings. -/
theorem KBounded.finite_reachable [Finite Place] {N : PetriNet Place Transition}
    {M₀ : Marking Place} {k : ℕ} (h : N.KBounded M₀ k) : {M | M₀ ⇝[N] M}.Finite :=
  (Marking.finite_card_le (Nat.card Place * k)).subset fun _ hM => h.card_le hM

/-- A bounded net over finitely many places has finitely many reachable markings. -/
theorem Bounded.finite_reachable [Finite Place] {N : PetriNet Place Transition}
    {M₀ : Marking Place} (h : N.Bounded M₀) : {M | M₀ ⇝[N] M}.Finite :=
  let ⟨_, hk⟩ := h
  hk.finite_reachable

/-- A net with finitely many reachable markings is bounded. -/
theorem bounded_of_finite_reachable {N : PetriNet Place Transition} {M₀ : Marking Place}
    (h : {M | M₀ ⇝[N] M}.Finite) : N.Bounded M₀ := by
  obtain ⟨k, hk⟩ := Set.Finite.bddAbove (h.image Multiset.card)
  refine ⟨k, fun M hM p hp => ?_⟩
  have := (Multiset.card_le_card hp).trans (hk ⟨M, hM, rfl⟩)
  simp at this

/-- Boundedness at a marking passes to the markings reachable from it. -/
theorem Bounded.of_reachable [Finite Place] {N : PetriNet Place Transition}
    {M₀ M : Marking Place} (h : N.Bounded M₀) (hr : M₀ ⇝[N] M) : N.Bounded M :=
  bounded_of_finite_reachable (h.finite_reachable.subset fun _ h' => hr.trans h')

/-- Over finitely many places, a net is bounded exactly when it has finitely many reachable
markings. -/
theorem bounded_iff_finite_reachable [Finite Place] {N : PetriNet Place Transition}
    {M₀ : Marking Place} : N.Bounded M₀ ↔ {M | M₀ ⇝[N] M}.Finite :=
  ⟨Bounded.finite_reachable, bounded_of_finite_reachable⟩

/-- The marking graph of a bounded net over finitely many places, restricted to the markings
reachable from `M₀`, is finite-state. -/
theorem Bounded.finite_generatedBy [Finite Place] {N : PetriNet Place Transition}
    {M₀ : Marking Place} (h : N.Bounded M₀) : Finite {M // N.lts.CanReach M₀ M} :=
  h.finite_reachable.to_subtype

/-- The marking graph of a bounded net over finitely many places, restricted to the markings
reachable from `M₀`, is image-finite. -/
theorem Bounded.imageFinite_generatedBy [Finite Place] {N : PetriNet Place Transition}
    {M₀ : Marking Place} (h : N.Bounded M₀) : (N.lts.generatedBy M₀).ImageFinite :=
  have := h.finite_generatedBy
  inferInstance

end Bounded

/-- A net is conservative if every transition consumes as many tokens as it produces. -/
def Conservative (N : PetriNet Place Transition) : Prop :=
  ∀ t, (•[N] t).card = (t •[N]).card

/-- Conservative nets preserve the total number of tokens. -/
theorem Conservative.card_eq {N : PetriNet Place Transition} (hc : N.Conservative)
    {M M' : Marking Place} (h : M ⇝[N] M') : M'.card = M.card :=
  h.invariant (P := fun K => K.card = M.card) (fun {_ t _} htr hK => by
    have := htr.card_add
    have := hc t
    omega) rfl

/-- A conservative net is `M₀.card`-bounded at `M₀`. -/
theorem Conservative.kBounded {N : PetriNet Place Transition}
    (hc : N.Conservative) (M₀ : Marking Place) : N.KBounded M₀ M₀.card := fun M hM p hp => by
  have := (Multiset.card_le_card hp).trans (hc.card_eq hM).le
  simp at this

/-- The marking graph is deterministic: firing a transition at a marking has at most one result. -/
instance (N : PetriNet Place Transition) : N.lts.Deterministic where
  deterministic M t M₁ M₂ h₁ h₂ := by
    obtain ⟨R₁, h₁, rfl⟩ := h₁
    obtain ⟨R₂, rfl, rfl⟩ := h₂
    rw [add_left_cancel h₁]

/-- With finitely many transitions, the marking graph is finitely branching. -/
instance (N : PetriNet Place Transition) [Finite Transition] : N.lts.FinitelyBranching where

/-- A marking is dead if no transition is enabled. -/
def Dead (N : PetriNet Place Transition) (M : Marking Place) : Prop :=
  N.lts.IsTerminal M

/-- A transition `t` is live at `M₀` if from every marking reachable from `M₀`, some marking
reachable from it enables `t`. -/
def LiveAt (N : PetriNet Place Transition) (M₀ : Marking Place) (t : Transition) : Prop :=
  ∀ M, M₀ ⇝[N] M → ∃ M', M ⇝[N] M' ∧ M' [t⟩[N]

/-- A net is live at the marking `M₀` if every transition is live at `M₀`. -/
def Live (N : PetriNet Place Transition) (M₀ : Marking Place) : Prop :=
  ∀ t, N.LiveAt M₀ t

/-- A transition is enabled at `M` exactly when it can fire from `M`. -/
theorem enabled_iff_exists_fires {N : PetriNet Place Transition} {M : Marking Place}
    {t : Transition} : M [t⟩[N] ↔ ∃ M', M [t⟩[N] M' :=
  ⟨fun h => let ⟨R, hR⟩ := exists_add_of_le h; ⟨R + t •[N], R, hR, rfl⟩,
    fun ⟨_, _, hR, _⟩ => hR ▸ le_self_add⟩

/-- A marking is dead exactly when no transition is enabled at it. -/
theorem dead_iff {N : PetriNet Place Transition} {M : Marking Place} :
    N.Dead M ↔ ∀ t, ¬ M [t⟩[N] := by
  simp only [Dead, LTS.IsTerminal, enabled_iff_exists_fires, lts, not_exists]

/-- A net that is live at `M₀` never reaches a dead marking from `M₀`
(provided it has at least one transition). -/
theorem Live.not_dead [Nonempty Transition] {N : PetriNet Place Transition} {M₀ M : Marking Place}
    (hl : N.Live M₀) (hr : M₀ ⇝[N] M) : ¬ N.Dead M := by
  intro hd
  obtain ⟨t⟩ := ‹Nonempty Transition›
  obtain ⟨M', ⟨ts, hts⟩, hen⟩ := hl t M hr
  cases hts with
  | refl => exact dead_iff.1 hd t hen
  | stepL htr _ => exact hd _ _ htr

/-- Firing sequences are preserved when adding tokens (monotonicity). -/
theorem mTr_add {N : PetriNet Place Transition} {M M' : Marking Place} {ts : List Transition}
    (h : N.lts.MTr M ts M') (K : Marking Place) : N.lts.MTr (M + K) ts (M' + K) := by
  induction h with
  | refl => exact .refl
  | stepL htr _ ih => exact .stepL (htr.add K) ih

/-- The computable firing rule runs exactly the firing sequences of the marking graph. -/
theorem run_eq_some_iff [DecidableEq Place] {N : PetriNet Place Transition} {ts : List Transition}
    {M M' : Marking Place} : N.run M ts = some M' ↔ N.lts.MTr M ts M' := by
  induction ts generalizing M with
  | nil => simp [run, eq_comm]
  | cons t ts ih =>
    simp only [run, Option.bind_eq_some_iff, fire?_eq_some_iff, ih]
    exact ⟨fun ⟨_, h, hr⟩ => .stepL h hr, fun h => by cases h with | stepL h hr => exact ⟨_, h, hr⟩⟩

theorem Reachable.add {N : PetriNet Place Transition} {M M' : Marking Place}
    (h : M ⇝[N] M') (K : Marking Place) : (M + K) ⇝[N] (M' + K) :=
  let ⟨ts, hts⟩ := h
  ⟨ts, mTr_add hts K⟩

end PetriNet

end Cslib
