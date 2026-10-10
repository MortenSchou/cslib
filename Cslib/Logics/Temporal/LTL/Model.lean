/-
Copyright (c) 2026 Morten Schou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Morten Schou
-/

module

public import Cslib.Logics.Temporal.LTL.Basic
public import Cslib.Logics.Temporal.CTL.Semantics

/-! # LTL on models

An LTL formula is evaluated on the traces of the maximal paths of a model. `⇓LTL[m,s ⊨∀ φ]` says
that all maximal paths from `s` satisfy `φ` (the usual LTL model checking problem) and
`⇓LTL[m,s ⊨∃ φ]` that some path does; they unfold to `AllPaths` and `SomePath`. Paths are maximal:
they are infinite, or stutter forever at a deadlock.

CTL is path quantifiers over LTL operators applied to state formulas. We make this precise by
taking CTL formulas as atoms: in `m.lift`, the atom `ψ` holds at the states satisfying `ψ`. Then
`E[φ U ψ]`, `EG φ`, `EF φ`, `AG φ`, `AF φ` and `A[φ U ψ]` are `⊨∃` or `⊨∀` of the corresponding
LTL formula over the atoms `φ` and `ψ`.
-/

@[expose] public section

namespace Cslib.Logic

open Cslib Cslib.ωSequence
open scoped Cslib.Logic.InferenceSystem

namespace CTL

variable {State : Type*} {Atom : Type*}

/-- The trace of a path: the set of atoms that hold at each state. -/
def Model.trace (m : Model State Atom) (f : ℕ → State) : ωSequence (Set Atom) :=
  ⟨fun i => {p | m.v (f i) p}⟩

open scoped InferenceSystem in
/-- The model in which the atoms are CTL formulas, holding at the states that satisfy them. -/
def Model.lift (m : Model State Atom) : Model State (Formula Atom) :=
  .ofRel m.tr fun s ψ => ⇓CTL[m,s ⊨ ψ]

theorem Model.isPath_lift {m : Model State Atom} {f : ℕ → State} :
    m.lift.IsPath f ↔ m.IsPath f := Iff.rfl

end CTL

namespace LTL

variable {State : Type*} {Atom : Type*}

/-- All maximal paths from `s` satisfy the formula. -/
def AllPaths (m : CTL.Model State Atom) (s : State) (φ : Formula Atom) : Prop :=
  ∀ f, m.IsPath f → f 0 = s → Satisfies (m.trace f) φ

/-- Some maximal path from `s` satisfies the formula. -/
def SomePath (m : CTL.Model State Atom) (s : State) (φ : Formula Atom) : Prop :=
  ∃ f, m.IsPath f ∧ f 0 = s ∧ Satisfies (m.trace f) φ

/-- Whether a formula must hold on all maximal paths from a state, or on some. -/
inductive Quantifier where
  /-- On all maximal paths. -/
  | universal
  /-- On some maximal path. -/
  | existential

/-- Judgement, representing the conclusions one reaches in LTL model checking. -/
structure ModelJudgement (State : Type u) (Atom : Type v) where
  /-- Constructs a judgement. -/
  mk ::
  /-- Model. -/
  m : CTL.Model State Atom
  /-- The state whose maximal paths are considered. -/
  s : State
  /-- Whether the formula holds on all paths or on some. -/
  q : Quantifier
  /-- The formula. -/
  φ : Formula Atom

/-- `LTL[m,s ⊨∀ φ]`: all maximal paths from `s` in `m` satisfy `φ`. -/
scoped notation "LTL[" m "," s " ⊨∀ " φ "]" =>
  ModelJudgement.mk m s Quantifier.universal φ

/-- `LTL[m,s ⊨∃ φ]`: some maximal path from `s` in `m` satisfies `φ`. -/
scoped notation "LTL[" m "," s " ⊨∃ " φ "]" =>
  ModelJudgement.mk m s Quantifier.existential φ

/-- Satisfaction for model checking judgements. This refers to `AllPaths` and `SomePath`. -/
def ModelJudgement.Holds : ModelJudgement State Atom → Prop
  | ⟨m, s, .universal, φ⟩ => AllPaths m s φ
  | ⟨m, s, .existential, φ⟩ => SomePath m s φ

instance : HasInferenceSystem (ModelJudgement State Atom) := ⟨ModelJudgement.Holds⟩

open scoped InferenceSystem Formula Cslib.Logic CTL CTL.Formula

theorem allPaths_def {m : CTL.Model State Atom} {s : State} {φ : Formula Atom} :
    ⇓LTL[m,s ⊨∀ φ] ↔ ∀ f, m.IsPath f → f 0 = s → ⇓LTL[m.trace f ⊨ φ] := Iff.rfl

theorem somePath_def {m : CTL.Model State Atom} {s : State} {φ : Formula Atom} :
    ⇓LTL[m,s ⊨∃ φ] ↔ ∃ f, m.IsPath f ∧ f 0 = s ∧ ⇓LTL[m.trace f ⊨ φ] := Iff.rfl

/-- A formula holds on all paths iff its negation holds on none. -/
theorem allPaths_iff_not_somePath {m : CTL.Model State Atom} {s : State} {φ : Formula Atom} :
    ⇓LTL[m,s ⊨∀ φ] ↔ ¬ ⇓LTL[m,s ⊨∃ ¬φ] := by
  rw [allPaths_def, somePath_def]
  simp only [Satisfies.not_iff]
  push Not
  exact ⟨fun h f hf h0 => h f hf h0, fun h f hf h0 => h f hf h0⟩

section CTL

variable {m : CTL.Model State Atom} {s : State} {φ ψ : CTL.Formula Atom}

theorem satisfies_atom_drop {f : ℕ → State} (n : ℕ) (χ : CTL.Formula Atom) :
    ⇓LTL[(m.lift.trace f).drop n ⊨ .atom χ] ↔ ⇓CTL[m,f n ⊨ χ] := by
  change χ ∈ {p | m.lift.v (f (0 + n)) p} ↔ _
  rw [Nat.zero_add]
  rfl

/-- `E[φ U ψ]` is some path satisfying `φ U ψ`. -/
theorem eu_iff_somePath :
    ⇓CTL[m,s ⊨ E[φ U ψ]] ↔ ⇓LTL[m.lift,s ⊨∃ (.atom φ) U (.atom ψ)] := by
  rw [CTL.Satisfies.eu_iff, somePath_def]
  simp only [Satisfies.until_iff, satisfies_atom_drop]
  rfl

/-- `EG φ` is some path satisfying `G φ`. -/
theorem eg_iff_somePath :
    ⇓CTL[m,s ⊨ EG φ] ↔ ⇓LTL[m.lift,s ⊨∃ G (.atom φ)] := by
  rw [CTL.Satisfies.eg_iff, somePath_def]
  simp only [Satisfies.always_iff, satisfies_atom_drop]
  rfl

/-- `EF φ` is some path satisfying `F φ`. -/
theorem ef_iff_somePath :
    ⇓CTL[m,s ⊨ EF φ] ↔ ⇓LTL[m.lift,s ⊨∃ F (.atom φ)] := by
  rw [CTL.Satisfies.ef_iff, somePath_def]
  simp only [Satisfies.eventually_iff, satisfies_atom_drop]
  rfl

/-- `AF φ` is all paths satisfying `F φ`. -/
theorem af_iff_allPaths :
    ⇓CTL[m,s ⊨ AF φ] ↔ ⇓LTL[m.lift,s ⊨∀ F (.atom φ)] := by
  rw [CTL.Satisfies.af_iff, allPaths_def]
  simp only [Satisfies.eventually_iff, satisfies_atom_drop]
  rfl

/-- `AG φ` is all paths satisfying `G φ`. -/
theorem ag_iff_allPaths :
    ⇓CTL[m,s ⊨ AG φ] ↔ ⇓LTL[m.lift,s ⊨∀ G (.atom φ)] := by
  rw [CTL.Satisfies.ag_iff, allPaths_def]
  simp only [Satisfies.always_iff, satisfies_atom_drop]
  rfl

/-- A sequence of facts fails to have `q` at a position with `p` before iff `q` first fails together
with `p`, or `q` never holds. -/
theorem not_until_seq (p q : ℕ → Prop) :
    ¬ (∃ n, q n ∧ ∀ k < n, p k) ↔
      (∃ n, (¬ p n ∧ ¬ q n) ∧ ∀ j < n, ¬ q j) ∨ ∀ n, ¬ q n := by
  classical
  constructor
  · intro h
    by_cases hq : ∃ n, q n
    · left
      let n := Nat.find hq
      have hn : q n := Nat.find_spec hq
      have hlt : ∀ j < n, ¬ q j := fun j hj => Nat.find_min hq hj
      have hex : ∃ k, k < n ∧ ¬ p k := by
        by_contra hcon
        push Not at hcon
        exact h ⟨n, hn, hcon⟩
      let k := Nat.find hex
      obtain ⟨hk, hpk⟩ := Nat.find_spec hex
      exact ⟨k, ⟨hpk, hlt k hk⟩, fun j hj => hlt j (lt_trans hj hk)⟩
    · right
      push Not at hq
      exact hq
  · rintro (⟨k, ⟨hpk, hqk⟩, hj⟩ | hq) ⟨n, hn, hp⟩
    · rcases lt_trichotomy n k with hlt | rfl | hgt
      · exact hj n hlt hn
      · exact hqk hn
      · exact hpk (hp k hgt)
    · exact hq n hn

/-- `A[φ U ψ]` is all paths satisfying `φ U ψ`. -/
theorem au_iff_allPaths :
    ⇓CTL[m,s ⊨ A[φ U ψ]] ↔ ⇓LTL[m.lift,s ⊨∀ (.atom φ) U (.atom ψ)] := by
  rw [allPaths_def]
  simp only [CTL.Formula.au, CTL.Satisfies.not_iff, CTL.Satisfies.or_iff, CTL.Satisfies.and_iff,
    CTL.Satisfies.eu_iff, CTL.Satisfies.eg_iff, Satisfies.until_iff, satisfies_atom_drop]
  constructor
  · intro h f hf h0
    by_contra hne
    rcases (not_until_seq (fun k => ⇓CTL[m,f k ⊨ φ])
      (fun k => ⇓CTL[m,f k ⊨ ψ])).1 hne with ⟨n, hn, hj⟩ | hall
    · exact h (Or.inl ⟨f, hf, h0, n, hn, hj⟩)
    · exact h (Or.inr ⟨f, hf, h0, hall⟩)
  · rintro h (⟨f, hf, h0, n, hn, hj⟩ | ⟨f, hf, h0, hall⟩)
    · exact (not_until_seq (fun k => ⇓CTL[m,f k ⊨ φ])
        (fun k => ⇓CTL[m,f k ⊨ ψ])).2 (Or.inl ⟨n, hn, hj⟩) (h f hf h0)
    · exact (not_until_seq (fun k => ⇓CTL[m,f k ⊨ φ])
        (fun k => ⇓CTL[m,f k ⊨ ψ])).2 (Or.inr hall) (h f hf h0)

end CTL

end LTL

end Cslib.Logic
