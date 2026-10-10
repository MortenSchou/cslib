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
  | `($M ⇝[$N] $M') => `(PetriNet.Reachable (net% $N) $M $M')

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

/-- A net is `k`-bounded at `M₀` if no reachable marking has more than `k` tokens in any place. -/
def KBounded (N : PetriNet Place Transition) (M₀ : Marking Place) (k : ℕ) : Prop :=
  ∀ M, M₀ ⇝[N] M → ∀ p, M p ≤ k

/-- A net is bounded at `M₀` if it is `k`-bounded at `M₀` for some `k`. -/
def Bounded (N : PetriNet Place Transition) (M₀ : Marking Place) : Prop :=
  ∃ k, N.KBounded M₀ k

/-- A net is safe at `M₀` if it is `1`-bounded at `M₀`. -/
def Safe (N : PetriNet Place Transition) (M₀ : Marking Place) : Prop :=
  N.KBounded M₀ 1

theorem KBounded.mono {N : PetriNet Place Transition} {M₀ : Marking Place} {k l : ℕ}
    (h : N.KBounded M₀ k) (hkl : k ≤ l) : N.KBounded M₀ l :=
  fun M hM p => (h M hM p).trans hkl

theorem KBounded.bounded {N : PetriNet Place Transition} {M₀ : Marking Place} {k : ℕ}
    (h : N.KBounded M₀ k) : N.Bounded M₀ :=
  ⟨k, h⟩

theorem Safe.bounded {N : PetriNet Place Transition} {M₀ : Marking Place} (h : N.Safe M₀) :
    N.Bounded M₀ :=
  KBounded.bounded h

/-- With finitely many places, a `k`-bounded net has at most `|Place| * k` tokens in total. -/
theorem KBounded.size_le [Finite Place] {N : PetriNet Place Transition} {M₀ M : Marking Place}
    {k : ℕ} (h : N.KBounded M₀ k) (hM : M₀ ⇝[N] M) :
    M.size ≤ Nat.card Place * k := by
  have := Fintype.ofFinite Place
  rw [Marking.size, Finsupp.degree_eq_sum, Nat.card_eq_fintype_card]
  calc ∑ p, M p ≤ ∑ _p : Place, k := Finset.sum_le_sum fun p _ => h M hM p
    _ = Fintype.card Place * k := by simp

/-- A `k`-bounded net over finitely many places has finitely many reachable markings. -/
theorem KBounded.finite_reachable [Finite Place] {N : PetriNet Place Transition}
    {M₀ : Marking Place} {k : ℕ} (h : N.KBounded M₀ k) : {M | M₀ ⇝[N] M}.Finite :=
  (Finsupp.finite_of_degree_le (Nat.card Place * k)).subset fun _ hM => h.size_le hM

/-- A bounded net over finitely many places has finitely many reachable markings. -/
theorem Bounded.finite_reachable [Finite Place] {N : PetriNet Place Transition}
    {M₀ : Marking Place} (h : N.Bounded M₀) : {M | M₀ ⇝[N] M}.Finite :=
  let ⟨_, hk⟩ := h
  hk.finite_reachable

/-- A net with finitely many reachable markings is bounded. -/
theorem bounded_of_finite_reachable {N : PetriNet Place Transition} {M₀ : Marking Place}
    (h : {M | M₀ ⇝[N] M}.Finite) : N.Bounded M₀ := by
  obtain ⟨k, hk⟩ := Set.Finite.bddAbove (h.image Marking.size)
  exact ⟨k, fun M hM p => (M.le_size p).trans (hk ⟨M, hM, rfl⟩)⟩

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

/-- A net is conservative if every transition consumes as many tokens as it produces. -/
def Conservative (N : PetriNet Place Transition) : Prop :=
  ∀ t, Marking.size (•[N] t) = Marking.size (t •[N])

/-- Conservative nets preserve the total number of tokens. -/
theorem Conservative.size_eq {N : PetriNet Place Transition} (hc : N.Conservative)
    {M M' : Marking Place} (h : M ⇝[N] M') : M'.size = M.size :=
  h.invariant (P := fun K => K.size = M.size) (fun {_ t _} htr hK => by
    have := htr.size_add
    have := hc t
    omega) rfl

/-- A conservative net is `M₀.size`-bounded at `M₀`. -/
theorem Conservative.kBounded {N : PetriNet Place Transition} (hc : N.Conservative)
    (M₀ : Marking Place) : N.KBounded M₀ M₀.size :=
  fun M hM p => (M.le_size p).trans (hc.size_eq hM).le

/-- The marking graph is deterministic: firing a transition at a marking has at most one result. -/
instance (N : PetriNet Place Transition) : N.lts.Deterministic where
  deterministic M t M₁ M₂ h₁ h₂ := by
    rw [(fires_iff.1 h₁).2, (fires_iff.1 h₂).2]

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
  ⟨fun h => ⟨_, fires_iff.2 ⟨h, rfl⟩⟩, fun ⟨_, h⟩ => (fires_iff.1 h).1⟩

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

theorem Reachable.add {N : PetriNet Place Transition} {M M' : Marking Place}
    (h : M ⇝[N] M') (K : Marking Place) : (M + K) ⇝[N] (M' + K) :=
  let ⟨ts, hts⟩ := h
  ⟨ts, mTr_add hts K⟩

end PetriNet

end Cslib
