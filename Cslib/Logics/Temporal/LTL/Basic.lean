/-
Copyright (c) 2026 Morten Schou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Morten Schou
-/

module

public import Cslib.Foundations.Logic.InferenceSystem
public import Cslib.Foundations.Logic.Operators
public import Cslib.Computability.Languages.OmegaLanguage

/-! # Linear Temporal Logic (LTL)

LTL is a linear-time temporal logic: its formulas describe infinite sequences of observations,
using the temporal operators next (`X`), until (`U`), and the derived eventually (`F`) and always
(`G`). A formula defines an ω-language over the alphabet of sets of atoms that hold at a position.

## Main definitions

- `Formula`: LTL formulas, over the minimal basis `{⊥, ¬, ∨, X, U}`.
- `Satisfies`: an ω-sequence of sets of atoms satisfies a formula.
- `Formula.language`: the ω-language of a formula.

## Main statements

- `isLiveness_language_F`: eventually a satisfiable formula is a liveness property.
- `isSafety_language_G`: always a state formula is a safety property.

## References

* [A. Pnueli, *The temporal logic of programs*][Pnueli1977]
-/

@[expose] public section

namespace Cslib.Logic.LTL

/-- An LTL formula over the atoms `Atom`. -/
inductive Formula (Atom : Type u) where
  /-- Atomic proposition. -/
  | atom (p : Atom)
  /-- Falsehood. -/
  | false
  /-- Negation. -/
  | not (φ : Formula Atom)
  /-- Disjunction. -/
  | or (φ₁ φ₂ : Formula Atom)
  /-- `X φ`: `φ` holds at the next position. -/
  | next (φ : Formula Atom)
  /-- `φ₁ U φ₂`: `φ₂` holds at some position, and `φ₁` at all positions before. -/
  | until (φ₁ φ₂ : Formula Atom)
deriving DecidableEq

namespace Formula

variable {Atom : Type*}

instance : Bot (Formula Atom) := ⟨.false⟩
instance : HasNot (Formula Atom) := ⟨.not⟩
instance : HasOr (Formula Atom) := ⟨.or⟩
instance : Coe Atom (Formula Atom) := ⟨.atom⟩

open scoped Cslib.Logic in
/-- Truth. -/
instance : Top (Formula Atom) := ⟨¬⊥⟩

open scoped Cslib.Logic in
/-- Conjunction, defined by De Morgan's law. -/
instance : HasAnd (Formula Atom) := ⟨fun φ ψ => ¬(¬φ ∨ ¬ψ)⟩

open scoped Cslib.Logic in
/-- Implication. -/
instance : HasImp (Formula Atom) := ⟨fun φ ψ => ¬φ ∨ ψ⟩

open scoped Cslib.Logic in
/-- Bi-implication. -/
instance : HasIff (Formula Atom) := ⟨fun φ ψ => (φ → ψ) ∧ (ψ → φ)⟩

open scoped Cslib.Logic in
/-- `F φ`: `φ` holds at some position. -/
def eventually (φ : Formula Atom) : Formula Atom := .until ⊤ φ

open scoped Cslib.Logic in
/-- `G φ`: `φ` holds at all positions. -/
def always (φ : Formula Atom) : Formula Atom := ¬(eventually (¬φ))

open scoped Cslib.Logic in
/-- `φ₁ W φ₂`, weak until: `φ₁ U φ₂`, or `φ₁` holds forever. -/
def weakUntil (φ₁ φ₂ : Formula Atom) : Formula Atom := .until φ₁ φ₂ ∨ always φ₁

open scoped Cslib.Logic in
/-- `φ₁ R φ₂`, release: `φ₂` holds up to and including the first position where `φ₁` holds, if
any. -/
def release (φ₁ φ₂ : Formula Atom) : Formula Atom := ¬(.until (¬φ₁) (¬φ₂))

@[inherit_doc] scoped notation:max "X " φ:max => Formula.next φ
@[inherit_doc] scoped notation:max "F " φ:max => Formula.eventually φ
@[inherit_doc] scoped notation:max "G " φ:max => Formula.always φ
@[inherit_doc] scoped infixr:50 " U " => Formula.until
@[inherit_doc] scoped infixr:50 " W " => Formula.weakUntil
@[inherit_doc] scoped infixr:50 " R " => Formula.release

/-- A state formula has no temporal operators: it only looks at the current position. -/
def IsState : Formula Atom → Prop
  | .atom _ => True
  | .false => True
  | .not φ => IsState φ
  | .or φ ψ => IsState φ ∧ IsState ψ
  | .next _ => False
  | .until _ _ => False

end Formula

open Cslib Cslib.ωSequence

variable {Atom : Type*}

/-- Satisfaction: the ω-sequence `w` of sets of atoms satisfies a formula. At each position the
set contains the atoms that hold there. -/
def Satisfies (w : ωSequence (Set Atom)) : Formula Atom → Prop
  | .atom p => p ∈ w 0
  | .false => False
  | .not φ => ¬ Satisfies w φ
  | .or φ ψ => Satisfies w φ ∨ Satisfies w ψ
  | .next φ => Satisfies w.tail φ
  | .until φ ψ => ∃ n, Satisfies (w.drop n) ψ ∧ ∀ k < n, Satisfies (w.drop k) φ

/-- Judgement, representing the conclusions one reaches in LTL about an ω-sequence. -/
structure Judgement (Atom : Type u) where
  /-- Constructs a judgement. -/
  mk ::
  /-- The ω-sequence. -/
  w : ωSequence (Set Atom)
  /-- The formula satisfied by the ω-sequence. -/
  φ : Formula Atom

@[inherit_doc] scoped notation "LTL[" w " ⊨ " φ "]" => Judgement.mk w φ

/-- Satisfaction for judgements. This just refers to the unbundled `Satisfies`. -/
def Satisfies.Bundled (j : Judgement Atom) : Prop := Satisfies j.w j.φ

instance : HasInferenceSystem (Judgement Atom) := ⟨Satisfies.Bundled⟩

open scoped InferenceSystem Formula Cslib.Logic

theorem derivation_def {w : ωSequence (Set Atom)} {φ : Formula Atom} :
    Satisfies w φ = ⇓LTL[w ⊨ φ] := rfl

/-- The ω-language of a formula: the sequences satisfying it. -/
def Formula.language (φ : Formula Atom) : ωLanguage (Set Atom) := ⟨{w | ⇓LTL[w ⊨ φ]}⟩

variable {w : ωSequence (Set Atom)} {φ ψ : Formula Atom}

theorem drop_drop (m n : ℕ) (w : ωSequence (Set Atom)) : (w.drop m).drop n = w.drop (n + m) :=
  DFunLike.ext _ _ fun i => congrArg w (Nat.add_assoc i n m)

theorem tail_eq_drop_one (w : ωSequence (Set Atom)) : w.tail = w.drop 1 := rfl

/-- Dropping after the tail drops one more. -/
theorem drop_tail (n : ℕ) (w : ωSequence (Set Atom)) : w.tail.drop n = w.drop (n + 1) :=
  drop_drop 1 n w

/-- The tail after dropping drops one more. -/
theorem tail_drop (n : ℕ) (w : ωSequence (Set Atom)) : (w.drop n).tail = w.drop (n + 1) := by
  rw [tail_eq_drop_one, drop_drop, Nat.add_comm]

@[simp] theorem drop_zero (w : ωSequence (Set Atom)) : w.drop 0 = w := rfl

@[simp] theorem Satisfies.atom_iff {p : Atom} : ⇓LTL[w ⊨ .atom p] ↔ p ∈ w 0 := Iff.rfl

@[simp] theorem Satisfies.false_iff : ⇓LTL[w ⊨ ⊥] ↔ False := Iff.rfl

@[simp] theorem Satisfies.not_iff : ⇓LTL[w ⊨ ¬φ] ↔ ¬ ⇓LTL[w ⊨ φ] := Iff.rfl

@[simp] theorem Satisfies.or_iff : ⇓LTL[w ⊨ φ ∨ ψ] ↔ ⇓LTL[w ⊨ φ] ∨ ⇓LTL[w ⊨ ψ] := Iff.rfl

@[simp] theorem Satisfies.true_iff : ⇓LTL[w ⊨ ⊤] := fun h => h

@[simp] theorem Satisfies.and_iff : ⇓LTL[w ⊨ φ ∧ ψ] ↔ ⇓LTL[w ⊨ φ] ∧ ⇓LTL[w ⊨ ψ] := by
  change ¬(¬ ⇓LTL[w ⊨ φ] ∨ ¬ ⇓LTL[w ⊨ ψ]) ↔ _
  tauto

@[simp] theorem Satisfies.imp_iff : ⇓LTL[w ⊨ φ → ψ] ↔ (⇓LTL[w ⊨ φ] → ⇓LTL[w ⊨ ψ]) := by
  change (¬ ⇓LTL[w ⊨ φ] ∨ ⇓LTL[w ⊨ ψ]) ↔ _
  tauto

@[simp] theorem Satisfies.next_iff : ⇓LTL[w ⊨ X φ] ↔ ⇓LTL[w.tail ⊨ φ] := Iff.rfl

theorem Satisfies.until_iff :
    ⇓LTL[w ⊨ φ U ψ] ↔ ∃ n, ⇓LTL[w.drop n ⊨ ψ] ∧ ∀ k < n, ⇓LTL[w.drop k ⊨ φ] :=
  Iff.rfl

theorem Satisfies.eventually_iff : ⇓LTL[w ⊨ F φ] ↔ ∃ n, ⇓LTL[w.drop n ⊨ φ] := by
  simp [Formula.eventually, Satisfies.until_iff]

theorem Satisfies.always_iff : ⇓LTL[w ⊨ G φ] ↔ ∀ n, ⇓LTL[w.drop n ⊨ φ] := by
  simp [Formula.always, Satisfies.eventually_iff]

/-- `φ U ψ` unfolds: `ψ` holds now, or `φ` holds now and `φ U ψ` at the next position. -/
theorem Satisfies.until_unfold :
    ⇓LTL[w ⊨ φ U ψ] ↔ ⇓LTL[w ⊨ ψ] ∨ (⇓LTL[w ⊨ φ] ∧ ⇓LTL[w.tail ⊨ φ U ψ]) := by
  simp only [Satisfies.until_iff, drop_tail]
  constructor
  · rintro ⟨n, hn, hk⟩
    cases n with
    | zero => exact Or.inl hn
    | succ n =>
      exact Or.inr ⟨hk 0 (Nat.succ_pos n), n, hn, fun k hk' => hk (k + 1) (by omega)⟩
  · rintro (h | ⟨hφ, n, hn, hk⟩)
    · exact ⟨0, h, fun k hk => absurd hk (Nat.not_lt_zero k)⟩
    · refine ⟨n + 1, hn, fun k hk' => ?_⟩
      cases k with
      | zero => exact hφ
      | succ k => exact hk k (by omega)

end Cslib.Logic.LTL
