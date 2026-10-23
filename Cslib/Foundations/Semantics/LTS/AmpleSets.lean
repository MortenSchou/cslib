/-
Copyright (c) 2026 Morten Schou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Morten Schou
-/

module

public import Cslib.Foundations.Semantics.LTS.Commutation
public import Cslib.Foundations.Semantics.LTS.Reduction
public import Mathlib.Order.WellFounded

/-! # Ample sets and partial-order reduction for safety properties

An *ample selector* chooses at each state a set of labels `A s`, which the reduced LTS
`LTS.reduced A` explores instead of all enabled labels. This file follows Peled's and Godefroid's
conditions, in a form that is checked by a state predicate rather than by a temporal formula.

* `C0` (`IsAmple.nonempty`): at a nonterminal state some selected label is enabled.
* `C1` (`IsAmple.stubborn`): `A s` is stubborn at `s` (`LTS.IsStubborn`): along any execution from
  `s` that avoids `A s`, the enabled labels of `A s` stay enabled and commute with the execution,
  and the disabled ones stay disabled. This is the generic form of the dependency condition. It is
  Peled's `C1` for the enabled labels (Godefroid's persistence), with Valmari's clause for the
  disabled labels, so that selected labels that occur in an execution are enabled at its start.
  Unlike Peled's ample sets, `A s` need not consist of enabled labels, so the stubborn sets of
  Valmari are ample sets as they are.
* `C2` (`IsAmple.invisible`): if `s` is not *expanded* (some enabled label is not selected), then
  every enabled selected label is invisible, for a set of labels `Inv` that the user has proved
  not to change the property of interest.
* `C3` (`LTS.CycleProviso A s₀`): there is no infinite path of the reduced LTS from `s₀` through
  states that are not expanded. This is the accessibility, for `LTS.UnexpandedStep`, of the states
  that the reduced LTS reaches from `s₀`, so only the reachable region matters
  (`CycleProviso.of_wellFounded` covers the whole state space). If the reduced LTS reaches
  finitely many states from `s₀`, it says that every cycle of the reduced graph contains an
  expanded state (`CycleProviso.of_finite`);
  `CycleProviso.of_measure` and `CycleProviso.of_level` give checkable sufficient conditions through
  a measure that decreases, or a level, bounded on the reachable states, that increases.

## Main statements

- `LTS.exists_reduced_mTr_of_mTr`: for an ample selector with the cycle proviso, every finite
  execution `s ⟶σ s'` has a counterpart `s ⟶ρ s''` in the reduced LTS, where `s''` is reached from
  `s'` by invisible labels only.
- `LTS.exists_reduced_mTr_traceEquiv`: if moreover the selected labels are independent, in the sense
  of a relation `I` used for `LTS.TraceEquiv`, of all labels outside the selected set, then `ρ` is
  Mazurkiewicz equivalent to `σ` followed by the invisible labels.
- `LTS.IsAmple.canReach_isTerminal_iff_reduced`: terminal states are preserved, which needs `C0`
  and `C1` only.
- `LTS.canReach_iff_reduced`, `LTS.invariant_iff_reduced`: reachability of a state satisfying a
  predicate that is insensitive to invisible labels, and hence invariants, are the same in the full
  and in the reduced LTS.

## What is and is not covered

This file treats *finite* executions only, which gives the safety fragment: reachability and
invariants of properties that invisible labels cannot change. Infinite executions and the
preservation of LTL without next-time are treated in
`Cslib.Foundations.Semantics.LTS.AmpleOmega` (infinite executions up to stuttering equivalence,
with the stepwise variant `IsAmpleStep` of `C0`–`C2`, which for a deterministic LTS is `IsAmple`,
in `Cslib.Foundations.Semantics.LTS.AmpleStep`),
`Cslib.Foundations.Semantics.LTS.AmplePaths` (maximal paths, which may end in a terminal state)
and `Cslib.Logics.Temporal.LTL.AmpleSets` (the LTL statement). The cycle proviso `C3` used there is
the one of this file.

## References

* [D. Peled, *All from one, one for all: on model checking using representatives*][Peled1993]
* [P. Godefroid, *Partial-Order Methods for the Verification of Concurrent Systems*][Godefroid1996]
* [A. Valmari, *Stubborn sets for reduced state space generation*][Valmari1991]
-/

@[expose] public section

namespace Cslib.LTS

universe u v

variable {State : Type u} {Label : Type v} {lts : LTS State Label}

/-- The selector `A` expands `s` fully: every enabled label is selected. -/
def IsExpanded (lts : LTS State Label) (A : State → Set Label) (s : State) : Prop :=
  ∀ μ, lts.Enabled s μ → μ ∈ A s

/-- The conditions `C0`, `C1` and `C2` on an ample selector `A`, where `Inv` is the set of
invisible labels. The cycle proviso `C3` is `LTS.CycleProviso`. -/
structure IsAmple (lts : LTS State Label) (A : State → Set Label) (Inv : Label → Prop) :
    Prop where
  /-- `C0`: at a nonterminal state some selected label is enabled. -/
  nonempty : ∀ s, ¬ lts.IsTerminal s → ∃ μ ∈ A s, lts.Enabled s μ
  /-- `C1`: the selected set is stubborn. -/
  stubborn : ∀ s, lts.IsStubborn s (A s)
  /-- `C2`: unless the state is fully expanded, the enabled selected labels are invisible. -/
  invisible : ∀ s, ¬ lts.IsExpanded A s → ∀ μ ∈ A s, lts.Enabled s μ → Inv μ

/-- `UnexpandedStep A s' s`: `s'` is reached from `s` by a step of the reduced LTS, and `s` is not
expanded. The arguments are in the order of a descending chain, so that `C3` is the
well-foundedness of this relation: there is no infinite reduced path through unexpanded states. -/
def UnexpandedStep (lts : LTS State Label) (A : State → Set Label) (s' s : State) : Prop :=
  ¬ lts.IsExpanded A s ∧ ∃ μ, (lts.reduced A).Tr s μ s'

/-- `C3`, the cycle proviso from the start state `s₀`: reduced paths cannot continue forever through
states that are not expanded. Only the states that the reduced LTS reaches from `s₀` matter, so
that the proviso can hold on a finite reachable region of an infinite state space. -/
def CycleProviso (lts : LTS State Label) (A : State → Set Label) (s₀ : State) : Prop :=
  ∀ s, (lts.reduced A).CanReach s₀ s → Acc (lts.UnexpandedStep A) s

/-- A selected transition from a state reached from `s₀` reaches a state reached from `s₀`. -/
theorem canReach_reduced_of_tr {A : State → Set Label} {s₀ s s' : State} {μ : Label}
    (hs : (lts.reduced A).CanReach s₀ s) (hμ : μ ∈ A s) (htr : lts.Tr s μ s') :
    (lts.reduced A).CanReach s₀ s' :=
  let ⟨ρ, hρ⟩ := hs
  ⟨ρ ++ [μ], hρ.comp _ (.single _ ⟨hμ, htr⟩)⟩

/-- An unexpanded step from a state reached from `s₀` reaches a state reached from `s₀`. -/
theorem UnexpandedStep.canReach {A : State → Set Label} {s₀ s s' : State}
    (h : lts.UnexpandedStep A s' s) (hs : (lts.reduced A).CanReach s₀ s) :
    (lts.reduced A).CanReach s₀ s' :=
  let ⟨_, _, hμ, htr⟩ := h
  canReach_reduced_of_tr hs hμ htr

/-- The cycle proviso holds from every state if the unexpanded steps are well-founded on the whole
state space. -/
theorem CycleProviso.of_wellFounded {A : State → Set Label}
    (h : WellFounded (lts.UnexpandedStep A)) {s₀ : State} : lts.CycleProviso A s₀ :=
  fun s _ => h.apply s

/-- A state is accessible for a relation if it is accessible in a subtype that contains all its
predecessors. -/
private theorem acc_of_subtype {r : State → State → Prop} {R : Set State}
    (hR : ∀ s y, s ∈ R → r y s → y ∈ R) (x : R) (hx : Acc (fun a b : R => r a b) x) :
    Acc r x.1 := by
  induction hx with
  | intro x _ ih => exact Acc.intro _ fun y hy => ih ⟨y, hR _ _ x.2 hy⟩ hy

/-- The cycle proviso on a finite reachable region: every cycle of the reduced graph that is
reachable from `s₀` contains an expanded state, that is, the unexpanded steps contain no
cycle. -/
theorem CycleProviso.of_finite {A : State → Set Label} {s₀ : State}
    (hfin : {s | (lts.reduced A).CanReach s₀ s}.Finite)
    (h : ∀ s, (lts.reduced A).CanReach s₀ s → ¬ Relation.TransGen (lts.UnexpandedStep A) s s) :
    lts.CycleProviso A s₀ := by
  have : Finite {s | (lts.reduced A).CanReach s₀ s} := hfin
  let T : {s | (lts.reduced A).CanReach s₀ s} → {s | (lts.reduced A).CanReach s₀ s} → Prop :=
    fun x y => Relation.TransGen (lts.UnexpandedStep A) x.1 y.1
  have : IsTrans _ T := ⟨fun _ _ _ => .trans⟩
  have : Std.Irrefl T := ⟨fun x => h x.1 x.2⟩
  have hwf : WellFounded fun a b : {s | (lts.reduced A).CanReach s₀ s} =>
      lts.UnexpandedStep A a.1 b.1 :=
    Subrelation.wf (fun {_ _} h => Relation.TransGen.single h)
      (Finite.wellFounded_of_trans_of_irrefl T)
  exact fun s hs => acc_of_subtype (fun _ _ hs' hy => hy.canReach hs') ⟨s, hs⟩ (hwf.apply _)

/-- The cycle proviso follows from a measure into a well-founded order that strictly decreases
along every step of the reduced LTS from a state that is not expanded and reached from `s₀`. -/
theorem CycleProviso.of_measure {β : Type*} [LT β] [WellFoundedLT β] {A : State → Set Label}
    {s₀ : State} (m : State → β)
    (h : ∀ s s', (lts.reduced A).CanReach s₀ s → lts.UnexpandedStep A s' s → m s' < m s) :
    lts.CycleProviso A s₀ := by
  intro s
  induction s using (InvImage.wf m wellFounded_lt).induction with
  | _ s ih =>
    exact fun hs => Acc.intro _ fun y hy => ih y (h s y hs hy) (hy.canReach hs)

/-- The cycle proviso follows from a level function that is bounded on the states reached from
`s₀` and strictly increases along every step of the reduced LTS from a state that is not expanded
and reached from `s₀`. -/
theorem CycleProviso.of_level {A : State → Set Label} {s₀ : State} (lvl : State → ℕ) (B : ℕ)
    (hB : ∀ s, (lts.reduced A).CanReach s₀ s → lvl s ≤ B)
    (h : ∀ s s', (lts.reduced A).CanReach s₀ s → lts.UnexpandedStep A s' s → lvl s < lvl s') :
    lts.CycleProviso A s₀ :=
  CycleProviso.of_measure (fun s => B - lvl s) fun s s' hs hss => by
    have := h s s' hs hss
    have := hB s' (hss.canReach hs)
    omega

/-- Invisible labels move a state predicate only trivially: `P` is unchanged by executions
consisting of invisible labels. -/
theorem MTr.iff_of_invisible {P : State → Prop} {Inv : Label → Prop}
    (hP : ∀ s μ s', lts.Tr s μ s' → Inv μ → (P s ↔ P s')) {s s' : State} {τ : List Label}
    (h : lts.MTr s τ s') (hτ : ∀ u ∈ τ, Inv u) : P s ↔ P s' := by
  induction h with
  | refl => exact Iff.rfl
  | stepL htr _ ih =>
    exact (hP _ _ _ htr (hτ _ (List.mem_cons_self ..))).trans
      (ih fun u hu => hτ u (List.mem_cons_of_mem _ hu))

/-- The relation `I` is respected by the selector `A`: every selected label is related to every
label that is not selected. -/
def IsIndependentOutside (A : State → Set Label) (I : Label → Label → Prop) : Prop :=
  ∀ s, ∀ a ∈ A s, ∀ u, u ∉ A s → I a u

section Main

variable {A : State → Set Label} {Inv : Label → Prop}

/-- The core of the reduction theorem, with the Mazurkiewicz refinement that holds when the
selector is independent of the labels outside it. -/
theorem exists_reduced_mTr_aux {s₀ : State} (hA : lts.IsAmple A Inv) (h3 : lts.CycleProviso A s₀)
    (I : Label → Label → Prop) :
    ∀ (n : ℕ) (s : State), (lts.reduced A).CanReach s₀ s →
      ∀ (σ : List Label) (s' : State), σ.length = n → lts.MTr s σ s' →
      ∃ ρ s'' τ, (lts.reduced A).MTr s ρ s'' ∧ lts.MTr s' τ s'' ∧ (∀ u ∈ τ, Inv u) ∧
        (IsIndependentOutside A I → TraceEquiv I (σ ++ τ) ρ) := by
  intro n
  induction n with
  | zero =>
    intro s _ σ s' hn h
    obtain rfl := List.length_eq_zero_iff.1 hn
    obtain rfl := MTr.nil_eq _ h
    exact ⟨[], s, [], .refl, .refl, by simp, fun _ => .refl _⟩
  | succ n ih =>
    intro s hs
    refine Acc.rec (motive := fun s _ => (lts.reduced A).CanReach s₀ s →
      ∀ σ s', σ.length = n + 1 → lts.MTr s σ s' →
        ∃ ρ s'' τ, (lts.reduced A).MTr s ρ s'' ∧ lts.MTr s' τ s'' ∧ (∀ u ∈ τ, Inv u) ∧
          (IsIndependentOutside A I → TraceEquiv I (σ ++ τ) ρ)) ?_ (h3 s hs) hs
    intro s _ ihs hs σ s' hn h
    by_cases hex : ∃ a ∈ σ, a ∈ A s
    · obtain ⟨σ₁, a, σ₂, sa, rfl, haS, hσ₁, hsa, hc⟩ := (hA.stubborn s).exists_split h hex
      obtain ⟨ρ, s'', τ, hρ, hτ, hinv, heq⟩ :=
        ih sa (canReach_reduced_of_tr hs haS hsa) (σ₁ ++ σ₂) s'
          (by simp only [List.length_append, List.length_cons] at hn ⊢; omega) hc
      refine ⟨a :: ρ, s'', τ, .stepL ⟨haS, hsa⟩ hρ, hτ, hinv, fun hI => ?_⟩
      rw [List.append_assoc]
      exact Relation.EqvGen.trans _ _ _
        (TraceEquiv.move_left a σ₁ (σ₂ ++ τ) fun u hu => hI s a haS u (hσ₁ u hu))
        (TraceEquiv.cons a (by simpa only [List.append_assoc] using heq hI))
    · push Not at hex
      obtain _ | ⟨b, σ'⟩ := σ
      · simp at hn
      obtain ⟨s₁, hb, -⟩ := MTr.cons_iff.1 h
      have hnexp : ¬ lts.IsExpanded A s := fun he => hex b (List.mem_cons_self ..) (he b ⟨_, hb⟩)
      obtain ⟨a, haA, hae⟩ := hA.nonempty s fun ht => ht _ _ hb
      have hinv := hA.invisible s hnexp a haA hae
      obtain ⟨sa, hsa⟩ := hae
      obtain ⟨⟨s'', hs''⟩, hc⟩ := (hA.stubborn s _ s' h hex a haA).1 ⟨_, hsa⟩
      obtain ⟨ρ, s₃, τ, hρ, hτ, hinv', heq⟩ :=
        ihs sa ⟨hnexp, a, haA, hsa⟩ (canReach_reduced_of_tr hs haA hsa) _ s'' hn
          (hc sa s'' hsa hs'')
      refine ⟨a :: ρ, s₃, a :: τ, .stepL ⟨haA, hsa⟩ hρ, .stepL hs'' hτ, ?_, fun hI => ?_⟩
      · intro u hu
        rcases List.mem_cons.1 hu with rfl | hu
        · exact hinv
        · exact hinv' u hu
      · exact Relation.EqvGen.trans _ _ _
          (TraceEquiv.move_left a _ τ fun u hu => hI s a haA u (hex u hu))
          (TraceEquiv.cons a (heq hI))

/-- Safety version of the reduction theorem. For an ample selector with the cycle proviso, every
finite execution `s ⟶σ s'` of the LTS has a counterpart `s ⟶ρ s''` in the reduced LTS, where `s''`
is reached from `s'` by invisible labels only.

This is a statement about finite executions. It does not relate infinite executions, and so does
not give preservation of LTL without next-time. -/
theorem exists_reduced_mTr_of_mTr {s s' : State} {σ : List Label} (hA : lts.IsAmple A Inv)
    (h3 : lts.CycleProviso A s) (h : lts.MTr s σ s') :
    ∃ ρ s'' τ, (lts.reduced A).MTr s ρ s'' ∧ lts.MTr s' τ s'' ∧ ∀ u ∈ τ, Inv u :=
  let ⟨ρ, s'', τ, h₁, h₂, h₃, _⟩ :=
    exists_reduced_mTr_aux hA h3 (fun _ _ => False) _ s (.refl _ _) σ s' rfl h
  ⟨ρ, s'', τ, h₁, h₂, h₃⟩

/-- Mazurkiewicz refinement of `exists_reduced_mTr_of_mTr`. If every selected label is related by
`I` to every label that is not selected, then the execution `ρ` of the reduced LTS is equivalent
under `TraceEquiv I` to `σ` followed by the invisible labels `τ`.

The hypothesis is static, so it is stronger than the state-dependent `IsAmple.stubborn`. -/
theorem exists_reduced_mTr_traceEquiv {s s' : State} {σ : List Label} (hA : lts.IsAmple A Inv)
    (h3 : lts.CycleProviso A s) {I : Label → Label → Prop} (hI : IsIndependentOutside A I)
    (h : lts.MTr s σ s') :
    ∃ ρ s'' τ, (lts.reduced A).MTr s ρ s'' ∧ lts.MTr s' τ s'' ∧ (∀ u ∈ τ, Inv u) ∧
      TraceEquiv I (σ ++ τ) ρ :=
  let ⟨ρ, s'', τ, h₁, h₂, h₃, h₄⟩ := exists_reduced_mTr_aux hA h3 I _ s (.refl _ _) σ s' rfl h
  ⟨ρ, s'', τ, h₁, h₂, h₃, h₄ hI⟩

/-- Terminal states are preserved by the reduction, which needs `C0` and `C1` only: the cycle
proviso and the visibility condition `C2` are not used. -/
theorem IsAmple.canReach_isTerminal_iff_reduced (hA : lts.IsAmple A Inv) {s : State} :
    (∃ D, lts.IsTerminal D ∧ lts.CanReach s D) ↔
      ∃ D, lts.IsTerminal D ∧ (lts.reduced A).CanReach s D :=
  Cslib.LTS.canReach_isTerminal_iff_reduced A hA.stubborn hA.nonempty

variable {P : State → Prop}

/-- Reachability of a state satisfying `P` is the same in the LTS and in its ample reduction,
provided that `P` is not changed by the invisible labels. -/
theorem canReach_iff_reduced {s : State} (hA : lts.IsAmple A Inv) (h3 : lts.CycleProviso A s)
    (hP : ∀ s μ s', lts.Tr s μ s' → Inv μ → (P s ↔ P s')) :
    (∃ s', lts.CanReach s s' ∧ P s') ↔ ∃ s', (lts.reduced A).CanReach s s' ∧ P s' := by
  refine ⟨fun ⟨s', ⟨σ, hσ⟩, hs'⟩ => ?_, fun ⟨s', ⟨ρ, hρ⟩, hs'⟩ => ⟨s', ⟨ρ, hρ.of_reduced⟩, hs'⟩⟩
  obtain ⟨ρ, s'', τ, hρ, hτ, hinv⟩ := exists_reduced_mTr_of_mTr hA h3 hσ
  exact ⟨s'', ⟨ρ, hρ⟩, (MTr.iff_of_invisible hP hτ hinv).1 hs'⟩

/-- An invariant that is not changed by the invisible labels holds on all states reachable in the
LTS if and only if it holds on all states reachable in the ample reduction. -/
theorem invariant_iff_reduced {s : State} (hA : lts.IsAmple A Inv) (h3 : lts.CycleProviso A s)
    (hP : ∀ s μ s', lts.Tr s μ s' → Inv μ → (P s ↔ P s')) :
    (∀ s', lts.CanReach s s' → P s') ↔ ∀ s', (lts.reduced A).CanReach s s' → P s' := by
  have key := canReach_iff_reduced hA h3 (P := fun s => ¬ P s) (s := s)
    (fun s μ s' h hi => not_congr (hP s μ s' h hi))
  refine ⟨fun h s' ⟨ρ, hρ⟩ => h s' ⟨ρ, hρ.of_reduced⟩, fun h s' hs' => ?_⟩
  by_contra hn
  obtain ⟨s'', hr, hp⟩ := key.1 ⟨s', hs', hn⟩
  exact hp (h s'' hr)

end Main

end Cslib.LTS
